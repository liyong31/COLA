// Copyright (C) 2017-2019 Laboratoire de Recherche et Développement
// de l'Epita.
// Copyright (C) 2020  The Seminator Authors
// Copyright (C) 2021  The COLA Authors
//
// COLA is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// COLA is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

//#include "optimizer.hpp"
#include "cola.hpp"
#include "bscc.hpp"
//#include "struct.hpp"

#include <deque>
#include <map>
#include <set>

#include <spot/misc/hashfunc.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/isunamb.hh>

#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/parity.hh>

#include <spot/twaalgos/postproc.hh>

#include <spot/parseaut/public.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/misc/version.hh>
#include <spot/twa/acc.hh>

#include <types.hpp>

namespace cola
{
  const int RANK_N = -1; // nondeterministic states
  const int RANK_M = -2; // missing states

  // macro state in which every state is assigned with a value
  // indicating the order of entering the deterministic part
  typedef std::vector<int> mstate;
  // state and the labelling value
  typedef std::pair<unsigned, int> label;
  // state and labelling pairs
  typedef std::vector<label> small_mstate;

  struct small_mstate_hash
  {
    size_t
    operator()(small_mstate s) const noexcept
    {
      size_t hash = 0;
      for (const auto &p : s)
      {
        hash = spot::wang32_hash(hash ^ ((p.first << 2) | p.second));
      }
      return hash;
    }
  };

  class ldba_determinize
  {
  private:
    // The source automaton.
    const spot::const_twa_graph_ptr aut_;

    // SCCs information of the source automaton.
    spot::scc_info& si_;

    // Number of states in the input automaton.
    unsigned nb_states_;

    // state_simulator
    state_simulator simulator_;

    // The parity automata being built.
    spot::twa_graph_ptr res_;

    // the number of indices
    unsigned sets_ = 0;

    unsigned num_colors_;

    spot::option_map &om_;

    // use ambiguous
    bool use_unambiguous_;

    bool use_scc_;

    // use stutter
    bool use_stutter_;

    bool use_simulation_;

    // Association between labelling states and state numbers of the
    // DPA.
    std::unordered_map<small_mstate, unsigned, small_mstate_hash> rank2n_;

    // States to process.
    std::deque<std::pair<mstate, unsigned>> todo_;

    // Support for each state of the source automaton.
    std::vector<bdd> support_;

    // Propositions compatible with all transitions of a state.
    std::vector<bdd> compat_;

    // Whether a SCC is deterministic or not
    std::vector<bool> is_deter_;
    // Whether a SCC is weak and can be reached by an accepting SCC
    // std::vector<bool> is_weak_;
    // SCC reachability
    // std::vector<char> scc_reachability_;
    // Whether a state only has accepting transitions
    std::vector<bool> is_accepting_;

    // State names for graphviz display
    std::vector<std::string> *names_;

    // Show Rank states in state name to help debug
    bool show_names_;

    int get_max_rank(const mstate &ms)
    {
      int max_rnk = -2;
      for (int i = 0; i < nb_states_; i++)
      {
        if (ms[i] == RANK_M)
          continue;
        if (max_rnk < ms[i])
        {
          max_rnk = ms[i];
        }
      }
      return max_rnk;
    }

    std::string
    get_name(const small_mstate &ms)
    {
      int max_rnk = -2;
      for (const auto &p : ms)
      {
        if (p.second > max_rnk)
        {
          max_rnk = p.second;
        }
      }

      std::string res = "{";

      bool first_state = true;
      for (const auto &p : ms)
        if (p.second == RANK_N)
        {
          if (!first_state)
            res += ",";
          first_state = false;
          res += std::to_string(p.first);
        }

      res += "}";
      for (int i = 0; i <= max_rnk; i++)
      {
        res += ",[";
        first_state = true;
        for (const auto &p : ms)
          if (p.second == i)
          {
            if (!first_state)
              res += ",";
            first_state = false;
            res += std::to_string(p.first);
          }
        res += "]=" + std::to_string(i);
      }
      return res;
    }

    small_mstate
    to_small_mstate(const mstate &ms)
    {
      unsigned count = 0;
      for (unsigned i = 0; i < nb_states_; ++i)
        count += (ms[i] != RANK_M);
      small_mstate small;
      small.reserve(count);
      for (unsigned i = 0; i < nb_states_; ++i)
        if (ms[i] != RANK_M)
          small.emplace_back(i, ms[i]);
      return small;
    }

    struct compare_pair
    {
      bool
      operator()(const label &lhs,
                 const label &rhs) const
      {
        if (lhs.second < rhs.second)
        {
          return true;
        }
        else if (lhs.second > rhs.second)
        {
          return false;
        }
        else
        {
          return lhs.first < rhs.second;
        }
      }
    };
    // From a Rank state, looks for a duplicate in the map before
    // creating a new state if needed.
    unsigned
    new_state(mstate &&s)
    {
      auto p = rank2n_.emplace(to_small_mstate(s), 0);
      if (p.second) // This is a new state
      {
        p.first->second = res_->new_state();
        if (show_names_)
          names_->push_back(get_name(p.first->first));
        todo_.emplace_back(std::move(s), p.first->second);
      }
      return p.first->second;
    }

    bool exists(mstate &s)
    {
      return rank2n_.end() == rank2n_.find(to_small_mstate(s));
    }

    bool
    is_smaller(const mstate &fst, const mstate &snd)
    {
      for (unsigned s = 0; s < nb_states_; s++)
      {
        if (fst[s] == snd[s])
          continue;
        else if (fst[s] < snd[s])
          return true;
        else if (fst[s] > snd[s])
          return false;
      }
      return false;
    }

    // remove a state i if it is simulated by a state j
    void
    make_simulation_state(mstate &ms)
    {
      std::vector<unsigned> reached_states;
      for (unsigned i = 0; i < nb_states_; i++)
      {
        if (ms[i] == RANK_M)
          continue;
        reached_states.push_back(i);
      }
      //std::cout << "reach states = " << get_set_string(reached_states) << std::endl;
      for (unsigned i : reached_states)
      {
        for (unsigned j : reached_states)
        {
          // if j is not reached at this level
          if (i == j)
            continue;
          // std::cout << "i = " << i << " j = " << j << std::endl;
          //std::cout << "start simulated" << std::endl;
          // j simulates i and j cannot reach i
          // std::cout << "simulator_.simulate(j, i) " << simulator_.simulate(j, i) << std::endl;
          std::cout << "simulator_.can_reach(j, i) " << simulator_.can_reach(j, i) << std::endl;
          if (simulator_.simulate(j, i) && simulator_.can_reach(j, i) == 0)
          {
            // std::cout << "simulated" << std::endl;
            ms[i] = RANK_M;
          }
          // (j, k1) and (i, k2), if j simulates i and k1 <= k2, then remove k2
          // Note that here i and j are not equivalent
          if (simulator_.simulate(j, i) && ms[j] > RANK_N && ms[j] <= ms[i])
          {
            ms[i] = RANK_M;
          }
        }
      }
    }

    //@param
    void
    compute_labelling_successors(const mstate &ms, unsigned origin, bdd letter, mstate &nxt, int &color)
    {
      mstate succ(nb_states_, RANK_M);
      int max_rnk = get_max_rank(ms);
      std::vector<bool> incoming(nb_states_, false);
      std::vector<bool> ignores(nb_states_, false);
      // first handle nondeterministic states
      std::vector<unsigned> coming_states;
      std::vector<unsigned> bottom_scc_states;
      //std::vector<unsigned> acc_coming_states;
      for (unsigned s = 0; s < nb_states_; ++s)
      {
        // missing states
        if (ms[s] == RANK_M)
          continue;
        // nondeterministic states
        if (ms[s] == RANK_N)
        {
          for (const auto &t : aut_->out(s))
          {
            if (!bdd_implies(letter, t.cond))
              continue;
            // it is legal to ignore the states have two incoming transitions
            // in unambiguous Buchi automaton
            if (use_unambiguous_)
            {
              if (incoming[t.dst])
              {
                // this is the second incoming transitions
                ignores[t.dst] = true;
              }
              else
              {
                incoming[t.dst] = true;
              }
            }
            if (ignores[t.dst])
            {
              // ignore this state
              continue;
            }

            bool jump = false;
            //TODO: this will be used for elevator automata if(t.acc || is_accepting_[t.dst])
            if (use_scc_)
            {
              // only transition to labelling if it is in an accepting SCC
              jump = si_.is_accepting_scc(si_.scc_of(t.dst));
            }
            else
            {
              // either it is deterministic, or the SCC is accepting in nondeterministic inherently weak
              jump = is_deter_[si_.scc_of(t.dst)] || si_.is_accepting_scc(si_.scc_of(t.dst));
            }
            if (jump)
            {
              if (succ[t.dst] < RANK_N)
              {
                coming_states.push_back(t.dst);
                succ[t.dst] = max_rnk + 1; //Sharing labels
                // succ[t.dst] = ++ max_rnk;
              }
            }
            else
            {
              succ[t.dst] = RANK_N;
            }
          }
        }
      }
      std::sort(coming_states.begin(), coming_states.end());
      for (unsigned s : coming_states)
      {
        succ[s] = ++max_rnk;
      }
      // now we compute the rank successors
      for (int rnk = max_rnk; rnk >= 0; rnk--)
      {
        for (unsigned s = 0; s < nb_states_; ++s)
        {
          if (ms[s] == RANK_M || ms[s] == RANK_N)
            continue;
          if (ms[s] != rnk)
            continue;
          for (const auto &t : aut_->out(s))
          {
            if (!bdd_implies(letter, t.cond))
              continue;
            if (use_unambiguous_)
            {
              if (incoming[t.dst])
              {
                // this is the second incoming transitions
                ignores[t.dst] = true;
              }
              else
              {
                incoming[t.dst] = true;
              }
            }
            if (ignores[t.dst])
            {
              continue;
            }
            // NORMAL way, inherit the labelling
            //succ[t.dst] = rnk;
            int update_rnk = RANK_N;
            // get out of an SCC to another and it is not accepting
            if (use_scc_ && si_.scc_of(s) != si_.scc_of(t.dst) && !si_.is_accepting_scc(si_.scc_of(t.dst)))
            {
              update_rnk = RANK_N; // go back to nondeterministic part
            }
            else
            {
              update_rnk = rnk;
            }
            succ[t.dst] = update_rnk;
          }
        }
      }

      // remove redudant states
      if (use_simulation_)
        make_simulation_state(succ);
      // now compute min_dcc (minimal index disappeared) and min_acc (minimal index accepted)
      const int MAX_RANK = nb_states_ + 2;
      int min_dcc = MAX_RANK;
      int min_acc = MAX_RANK;
      for (int rnk = max_rnk; rnk >= 0; rnk--)
      {
        bool has_succ = false;
        bool has_acc = false;
        for (unsigned s = 0; s < nb_states_; ++s)
        {
          if (ms[s] == RANK_M || ms[s] == RANK_N)
            continue;
          if (ms[s] != rnk)
            continue;
          // exactly the rank is rnk
          for (const auto &t : aut_->out(s))
          {
            if (!bdd_implies(letter, t.cond))
              continue;
            // exactly the same rank means the existence of an edge from the parent s
            if (succ[t.dst] == rnk)
            {
              has_succ = true;
              has_acc = has_acc || t.acc;
            }
          }
        }
        if (!has_succ)
        {
          min_dcc = rnk;
        }
        else if (has_acc)
        {
          min_acc = rnk;
        }
      }

      int parity;
      if (min_dcc == MAX_RANK && min_acc != MAX_RANK)
      {
        parity = 2 * (min_acc + 1);
      }
      else if (min_dcc != MAX_RANK && min_acc == MAX_RANK)
      {
        parity = 2 * min_dcc + 1;
      }
      else if (min_dcc != MAX_RANK && min_acc != MAX_RANK)
      {
        parity = std::min(2 * min_dcc + 1, 2 * min_acc + 2);
      }
      else
      {
        parity = -1;
      }
      // now reorgnize the indices
      std::unordered_map<int, int> ord_func;
      int index = 0;
      // the succ has at most max_rnk + 1
      for (int i = 0; i <= max_rnk + 1; i++)
      {
        bool existing = false;
        for (unsigned s = 0; s < nb_states_; ++s)
        {
          if (succ[s] == i)
          {
            existing = true;
            break;
          }
        }
        if (existing)
        {
          ord_func.emplace(i, index);
          index++;
        }
      }
      for (unsigned s = 0; s < nb_states_; s++)
      {
        if (succ[s] != RANK_M && succ[s] != RANK_N)
        {
          // update indices
          succ[s] = ord_func[succ[s]];
        }
      }

      // now we find whether there is bisimulate-states
      //new_bisim_state(succ);

      nxt = succ;
      color = parity;
    }
    // copied and adapted from deterministic.cc in Spot
    void
    make_stutter_state(const mstate &curr, unsigned origin, bdd letter, mstate &succ, int &color)
    {
      mstate ms;//(nb_states_, RANK_M);
      for (unsigned s = 0; s < nb_states_; s++)
      {
        ms.push_back(curr[s]);
      }
      std::vector<mstate> stutter_path;
      if (use_stutter_ && aut_->prop_stutter_invariant())
      {
        // The path is usually quite small (3-4 states), so it's
        // not worth setting up a hash table to detect a cycle.
        stutter_path.clear();
        std::vector<mstate>::iterator cycle_seed;
        int mincolor = -1;
        // stutter forward until we   cycle
        for (;;)
        {
          // any duplicate value, if any, is usually close to
          // the end, so search backward.
          auto it = std::find(stutter_path.rbegin(),
                              stutter_path.rend(), ms);
          if (it != stutter_path.rend())
          {
            cycle_seed = (it + 1).base();
            break;
          }
          stutter_path.emplace_back(std::move(ms));
          // next state
          mstate tmp_succ;
          int tmp_color = -1;
          compute_labelling_successors(stutter_path.back(), origin, letter, tmp_succ, tmp_color);
          ms = tmp_succ;
          if (tmp_color != -1 && mincolor != -1)
          {
            mincolor = std::min(tmp_color, mincolor);
          }
          else if (tmp_color != -1)
          {
            mincolor = tmp_color;
          }
        }
        // check whether this ms has been seen before
        bool in_seen = exists(*cycle_seed);
        for (auto it = cycle_seed + 1; it < stutter_path.end(); ++it)
        {
          if (in_seen)
          {
            // if *cycle_seed is already in seen, replace
            // it with a smaller state also in seen.
            if (exists(*it) && is_smaller(*it, *cycle_seed))
              cycle_seed = it;
          }
          else
          {
            // if *cycle_seed is not in seen, replace it
            // either with a state in seen or with a smaller
            // state
            if (exists(*it))
            {
              cycle_seed = it;
              in_seen = true;
            }
            else if (is_smaller(*it, *cycle_seed))
            {
              cycle_seed = it;
            }
          }
        }
        succ = std::move(*cycle_seed);
        color = mincolor;
      }
      else
      {
        compute_labelling_successors(ms, origin, letter, succ, color);
      }
    }

  public:
    ldba_determinize(const spot::const_twa_graph_ptr &aut, spot::scc_info& si, spot::option_map &om, std::vector<bdd>& implications)
        : aut_(aut),
          om_(om),
          use_simulation_(om.get(USE_SIMULATION) > 0),
          use_scc_(om.get(USE_SCC_INFO) > 0),
          use_stutter_(om.get(USE_STUTTER) > 0),
          use_unambiguous_(om.get(USE_UNAMBIGUITY) > 0),
          si_(si),
          nb_states_(aut->num_states()),
          support_(nb_states_),
          compat_(nb_states_),
          is_accepting_(nb_states_),
          simulator_(aut, si, implications, om.get(USE_SIMULATION) > 0),
          show_names_(om.get(VERBOSE_LEVEL) >= 2)
    {
      if(om.get(VERBOSE_LEVEL) >= 2)
      {
        simulator_.output_simulation();
      }
      res_ = spot::make_twa_graph(aut->get_dict());
      res_->copy_ap_of(aut);
      res_->prop_copy(aut,
                      {
                          false,        // state based
                          false,        // inherently_weak
                          false, false, // deterministic
                          true,         // complete
                          false         // stutter inv
                      });
      // Generate bdd supports and compatible options for each state.
      // Also check if all its transitions are accepting.
      for (unsigned i = 0; i < nb_states_; ++i)
      {
        bdd res_support = bddtrue;
        bdd res_compat = bddfalse;
        bool accepting = true;
        bool has_transitions = false;
        for (const auto &out : aut->out(i))
        {
          has_transitions = true;
          res_support &= bdd_support(out.cond);
          res_compat |= out.cond;
          if (!out.acc)
            accepting = false;
        }
        support_[i] = res_support;
        compat_[i] = res_compat;
        is_accepting_[i] = accepting && has_transitions;
      }
      // std::cout << "now deterministic part: " << std::endl;
      // Compute which SCCs are part of the deterministic set.
      is_deter_ = get_deterministic_sccs(si_);
      // std::cout << "deterministic part computing " << std::endl;
      // optimize with the fact of being unambiguous
      use_unambiguous_ = use_unambiguous_ && is_unambiguous(aut);
      if (show_names_)
      {
        names_ = new std::vector<std::string>();
        res_->set_named_prop("state-names", names_);
      }
      // Because we only handle one initial state, we assume it
      // belongs to the N set. (otherwise the automaton would be
      // deterministic)
      unsigned init_state = aut->get_init_state_number();
      mstate new_init_state(nb_states_, RANK_M);
      new_init_state[init_state] = RANK_N;
      // we assume that the initial state is not in deterministic part
      res_->set_init_state(new_state(std::move(new_init_state)));
    }

    spot::twa_graph_ptr
    run()
    {
      // Main stuff happens here
      // todo_ is a queue for handling states
      while (!todo_.empty())
      {
        auto top = todo_.front();
        todo_.pop_front();
        // pop current state, (N, Rnk)
        mstate ms = top.first;

        // Compute support of all available states.
        bdd msupport = bddtrue;
        bdd n_s_compat = bddfalse;
        // compute the occurred variables in the outgoing transitions of ms, stored in msupport
        for (unsigned s = 0; s < nb_states_; ++s)
          if (ms[s] != RANK_M)
          {
            msupport &= support_[s];
            if (ms[s] != RANK_M || is_accepting_[s])
              n_s_compat |= compat_[s];
          }

        bdd all = n_s_compat;
        while (all != bddfalse)
        {
          bdd letter = bdd_satoneset(all, msupport, bddfalse);
          all -= letter;
          // Compute all new states available from the generated
          // letter.

          mstate succ;
          int color = -1;
          //compute_labelling_successors(std::move(ms), top.second, letter, succ, color);
          make_stutter_state(ms, top.second, letter, succ, color);

          unsigned origin = top.second;
          // add transitions
          // Create the automaton states
          unsigned dst = new_state(std::move(succ));
          // const unsigned MAX_RANK = 2* nb_det_states_ + 1;
          if (color >= 0)
          {
            unsigned pri = (unsigned)color;
            sets_ = std::max(pri, sets_);

            res_->new_edge(origin, dst, letter, {pri});
          }
          else
          {
            res_->new_edge(origin, dst, letter);
          }
        }
      }
      // check the number of indices
      unsigned max_odd_pri = -1;
      // sets_ stores the maximal priority has ever seen
      if (sets_ & 1)
      {
        max_odd_pri = sets_;
      }
      else
      {
        max_odd_pri = sets_ + 1;
      }

      for (auto &t : res_->edges())
      {
        if (t.acc.count() <= 0)
        {
          t.acc = spot::acc_cond::mark_t{max_odd_pri};
        }
      }
      // Acceptance is now min(odd) since we can emit Red on paths 0 with new opti
      num_colors_ = max_odd_pri + 1;

      res_->set_acceptance(num_colors_, spot::acc_cond::acc_code::parity_min_even(num_colors_));
      if (aut_->prop_complete().is_true())
        res_->prop_complete(true);
      res_->prop_universal(true);
      res_->prop_state_acc(false);
      res_ = postprocess(res_);
      cleanup_parity_here(res_);

      return res_;
    }

    spot::twa_graph_ptr
    postprocess(spot::twa_graph_ptr aut)
    {
      // set of states -> the forest of reachability in the states.
      mstate_equiv_map set2scc;
      // record the representative of every SCC
      for (auto p = rank2n_.begin(); p != rank2n_.end(); p++)
      {
        std::set<unsigned> set;
        // first the set of reached states
        for (auto tuple : p->first)
        {
          set.insert(tuple.first);
        }
        auto val = set2scc.find(set);
        if (val == set2scc.end())
        {
          // the set of macrostates in DPA
          std::set<unsigned> v;
          v.insert(p->second);
          set2scc[set] = v;
        }
        else
        {
          val->second.insert(p->second);
          set2scc[set] = val->second;
        }
      }
      mstate_merger merger(aut, set2scc);
      spot::twa_graph_ptr res = merger.run();
      if (om_.get(VERBOSE_LEVEL) >= 1)
        std::cout << "The number of states reduced by mstate_merger: "
                  << (aut->num_states() - res->num_states()) << " {out of "
                  << aut->num_states() << "}" << std::endl;
      return res;
    }
  };

  spot::twa_graph_ptr
  determinize_tldba(const spot::const_twa_graph_ptr &aut, spot::option_map &om)
  {
    if (!is_elevator_automaton(aut))
      throw std::runtime_error("determinize_tldba() requires a semi-deterministic input");

    // now we compute the simulator
        // now we compute the simulator
    spot::const_twa_graph_ptr aut_reduced;
    std::vector<bdd> implications;
    spot::twa_graph_ptr aut_tmp = nullptr;
    if (om.get(USE_SIMULATION) > 0)
    {
      aut_tmp = spot::scc_filter(aut);
      auto aut2 = simulation(aut_tmp, &implications);
      aut_tmp = aut2;
    }
    if (aut_tmp)
      aut_reduced = aut_tmp;
    else 
      aut_reduced = aut;
    spot::scc_info scc(aut_reduced, spot::scc_info_options::ALL);
    auto det = cola::ldba_determinize(aut_reduced, scc, om, implications);
    return det.run();
  }
}