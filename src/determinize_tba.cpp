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

// #include "optimizer.hpp"
#include "cola.hpp"
//#include "struct.hpp"

#include <deque>
#include <map>
#include <set>
#include <algorithm>
#include <functional>

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

// Determinization of TBAs via semi-determinization of TBAs and determinization of TLDBAs
namespace cola
{

  struct set_pair_compare
  {
    bool operator()(const std::pair<state_set, state_set> &lhs,
                    const std::pair<state_set, state_set> &rhs) const
    {
      if (lhs.first == rhs.first)
        return lhs.second < rhs.second;
      else
        return lhs.first < rhs.first;
    }
  };
  // using state_t = unsigned;
  // using state_set = state_set;
  //using node_t = std::pair<, state_set>;
  const int RANK_N = -1; // nondeterministic
  const int RANK_M = -2; // missing value

  // void copy_set_to(state_set &S1, state_set &S2)
  // {
  //   for (auto s : S1)
  //   {
  //     S2.insert(s);
  //   }
  // }
  // macrostate
  class mstate final
  {
    void
    check() const
    {
      // all states in P and Q are in reach_set_ and Q \subseteq P
      assert(qset_.size() == pset_.size());
      unsigned num = qset_.size();
      for (unsigned i = 0; i < num; i++)
      {
        for (state_t s : qset_[i])
        {
          assert(pset_[i].find(s) != pset_[i].end());
        }
        for (state_t s : pset_[i])
        {
          assert(reach_set_.find(s) != reach_set_.end());
        }
      }
    }

  public:
    mstate(state_t init_state)
    {
      reach_set_.insert(init_state);
    }
    mstate(const mstate &other)
    {
      reach_set_.clear();
      for(auto s : other.reach_set_)
      {
        reach_set_.insert(s);
      }
      pset_.clear();
      qset_.clear();
      for (unsigned i = 0; i < other.pset_.size(); i++)
      {
        state_set pset;
        state_set qset;
        for(auto s : other.pset_[i])
        {
          pset.insert(s);
        }
        pset_.push_back(pset);
        for(auto s : other.qset_[i])
        {
          qset.insert(s);
        }
        qset_.push_back(qset);
      }
    }
    mstate() {}
    mstate& operator=(const mstate &other)
    {
      reach_set_.clear();
      for(auto s : other.reach_set_)
      {
        reach_set_.insert(s);
      }
      pset_.clear();
      qset_.clear();
      for (unsigned i = 0; i < other.pset_.size(); i++)
      {
        state_set pset;
        state_set qset;
        for(auto s : other.pset_[i])
        {
          pset.insert(s);
        }
        pset_.push_back(pset);
        for(auto s : other.qset_[i])
        {
          qset.insert(s);
        }
        qset_.push_back(qset);
      }
      return *this;
    }
    bool operator<(const mstate &other) const;
    bool operator==(const mstate &other) const;

    size_t hash() const;
    // the set of reachable states in this level
    state_set reach_set_;
    // this is the list of nodes that ordered due to later introduction record
    std::vector<state_set> qset_;
    std::vector<state_set> pset_;
  };

  size_t
  hash_unsigned_set(const state_set &uset)
  {
    size_t hash = 0;
    for (auto i : uset) // not sure how you're storing them
    {
      hash = (hash << 3) ^ ((unsigned)i);
    }
    return hash;
  }

  bool
  mstate::operator<(const mstate &other) const
  {
    if (reach_set_ < other.reach_set_)
    {
      return true;
    }
    if (reach_set_ > other.reach_set_)
    {
      return false;
    }
    if (pset_.size() < other.pset_.size())
    {
      return true;
    }
    if (pset_.size() > other.pset_.size())
    {
      return false;
    }
    for (unsigned i = 0; i < pset_.size(); i++)
    {
      if (pset_[i] < other.pset_[i])
      {
        return true;
      }
      if (pset_[i] > other.pset_[i])
      {
        return false;
      }
      if (qset_[i] < other.qset_[i])
      {
        return true;
      }
      if (qset_[i] > other.qset_[i])
      {
        return false;
      }
    }
    return false;
  }
  bool
  mstate::operator==(const mstate &other) const
  {
    if (reach_set_ != other.reach_set_)
    {
      return false;
    }
    if (pset_.size() != other.pset_.size())
    {
      return false;
    }
    for (unsigned i = 0; i < pset_.size(); i++)
    {
      if (pset_[i] != other.pset_[i])
      {
        return false;
      }
      if (qset_[i] != other.qset_[i])
      {
        return false;
      }
    }
    return true;
  }

  size_t
  mstate::hash() const
  {
    size_t res = 0;

    for (unsigned i = 0; i < pset_.size(); i++)
    {
      res ^= (res << 3) ^ hash_unsigned_set(pset_[i]);
      res ^= (res << 3) ^ hash_unsigned_set(qset_[i]);
    }
    for (state_t s : reach_set_)
    {
      res ^= (res << 3) ^ s;
    }
    return res;
  }

  std::string
  get_name(const mstate &ms)
  {
    std::string res = get_set_string(ms.reach_set_) + ",[";
    bool first = true;
    for (unsigned i = 0; i < ms.pset_.size(); i++)
    {
      if (!first)
      {
        res += ", ";
      }
      else
      {
        first = false;
      }
      res += "(" + get_set_string(ms.pset_[i]) 
          + ", " + get_set_string(ms.qset_[i])
          + ") = " + std::to_string(i);
    }
    res += "]";
    return res;
  }
  struct mstate_hash
  {
    size_t
    operator()(const mstate &s) const noexcept
    {
      return s.hash();
    }
  };

  bool
  is_subset(state_set &x, state_set &y)
  {
    for (auto s : x)
    {
      if (y.find(s) == y.end())
      {
        return false;
      }
    }
    return true;
  }

  class tba_determinize
  {
  private:
    // The source automaton.
    const spot::const_twa_graph_ptr aut_;

    // SCCs information of the source automaton.
    spot::scc_info& si_;

    //optimizer opt_;

    // Number of states in the input automaton.
    unsigned nb_states_;

    // unsigned nb_det_states_;
    state_simulator simulator_;

    // The parity automata being built.
    spot::twa_graph_ptr res_;

    // the number of indices
    unsigned sets_ = 0;

    spot::option_map& om_;

    // number of colors used
    unsigned num_colors_;

    // use ambiguous
    bool use_unambiguous_;

    bool use_simulation_;

    // use optimization with SCC information
    bool use_scc_;

    // use stutter
    bool use_stutter_;

    // Association between labelling states and state numbers of the
    // DPA.
    std::unordered_map<mstate, unsigned, mstate_hash> rank2n_;

    // States to process.
    std::deque<std::pair<mstate, unsigned>> todo_;

    // Support for each state of the source automaton.
    std::vector<bdd> support_;

    // Propositions compatible with all transitions of a state.
    std::vector<bdd> compat_;

    // Whether a SCC has accepting cycle
    std::vector<bool> is_entering_;

    // Whether a state only has accepting transitions
    std::vector<bool> is_accepting_;

    // State names for graphviz display
    std::vector<std::string> *names_;

    // Show Rank states in state name to help debug
    bool show_names_;

    // From a Rank state, looks for a duplicate in the map before
    // creating a new state if needed.
    unsigned
    new_state(mstate &s)
    {
      // std::cout << "new state: " << get_name(s) << std::endl;
      //mstate s_p(s);
      // std::cout << "copy state: " << get_name(s) << std::endl;
      mstate dup(s);
      auto p = rank2n_.emplace(dup, 0);
      if (p.second) // This is a new state
      {
        p.first->second = res_->new_state();
        if (show_names_)
          names_->push_back(get_name(p.first->first));
        todo_.emplace_back(dup, p.first->second);
      }
      return p.first->second;
    }

    bool exists(mstate &s)
    {
      return rank2n_.end() == rank2n_.find(s);
    }

    // remove a state i if it is simulated by a state j
    void
    make_simulation_state(mstate &ms)
    {
      state_set removed_states;
      state_set reach_states;

      for(auto s : ms.reach_set_)
      {
        reach_states.insert(s);
      }

      for (unsigned i : reach_states)
      {
        for (unsigned j : reach_states)
        {
          // if j is not reached at this level
          if (i == j)
            continue;
          // j simulates i and j cannot reach i
          if (simulator_.simulate(j, i) 
            && simulator_.can_reach(j, i) == 0)
          {
            removed_states.insert(i);
            auto it = ms.reach_set_.find(i);
            if(it != ms.reach_set_.end()) 
            {
              ms.reach_set_.erase(it);
            }
          }
        }
      }
      // ms.reach_set_.clear();
      // now remove all states in removed_states
      // std::set_difference(reach_states.begin(), reach_states.end()
      //                   , removed_states.begin(), removed_states.end()
      //                   , std::inserter(ms.reach_set_, ms.reach_set_.begin()));

      for (unsigned i = 0; !removed_states.empty() && i < ms.pset_.size(); i++)
      {
        state_set pset;
        std::set_difference(ms.pset_[i].begin(), ms.pset_[i].end()
                        , removed_states.begin(), removed_states.end()
                        , std::inserter(pset, pset.begin()));
        ms.pset_[i] = pset;
        state_set qset;
        std::set_difference(ms.qset_[i].begin(), ms.qset_[i].end()
                        , removed_states.begin(), removed_states.end()
                        , std::inserter(qset, qset.begin()));
        ms.qset_[i] = qset;
      }
      // keep the empty set
      //compare (P1, Q1) and (P2, Q2) such that P1 \subseteq P2, and Q1 \superset Q2
      // then the language of (P1, Q1) includes the language of (P2, Q2)
      // To be proved
      std::set<unsigned> removed_indices;
      for (unsigned i = 0; i < ms.pset_.size(); i++)
      {
        if (ms.pset_[i].empty())
          continue;
        for (unsigned j = i + 1; j < ms.pset_.size(); j++)
        {
          //if(i == j) continue;
          if (is_subset(ms.pset_[i], ms.pset_[j]) && is_subset(ms.qset_[j], ms.qset_[i]))
          {
            removed_indices.insert(j);
          }
        }
      }
      // clear those indices
      for (unsigned i : removed_indices)
      {
        ms.pset_[i].clear();
        ms.qset_[i].clear();
      }
    }

    std::pair<state_set, state_set>
    get_set_successors(const state_set &p, const state_set &q
            , bdd letter, const state_set &restricts, bool &acc)
    {
      state_set p_prime;
      state_set p_acc_prime;
      state_set q_dprime;
      state_set q_prime;

      for (auto s : p)
      {
        for (const auto &t : aut_->out(s))
        {
          // ignore unreachable states and 
          // states that are not in restructs
          if (!bdd_implies(letter, t.cond)
             || (restricts.find(t.dst) == restricts.end()))
            continue;
          p_prime.insert(t.dst);
          if (t.acc || is_accepting_[t.dst])
          {
            p_acc_prime.insert(t.dst);
          }
          if (q.find(s) != q.end())
          {
            q_prime.insert(t.dst);
          }
        }
      }
      q_dprime.insert(q_prime.begin(), q_prime.end());
      q_dprime.insert(p_acc_prime.begin(), p_acc_prime.end());
      if (q_dprime == p_prime)
      {
        acc = !p_prime.empty();
        q_prime = p_acc_prime;
      }
      else
      {
        acc = false;
        q_prime = q_dprime;
      }
      return std::make_pair(p_prime, q_prime);
    }

    void
    rank_successors(const mstate &ms, unsigned origin, bdd letter, mstate &nxt, int &color)
    {
      mstate succ;
      std::vector<bool> incoming(nb_states_, false);
      std::vector<bool> ignores(nb_states_, false);
      // first handle nondeterministic states
      std::set<unsigned> coming_states;
      //std::vector<unsigned> acc_coming_states;
      for (unsigned s : ms.reach_set_)
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
          succ.reach_set_.insert(t.dst);
          // via accepting transitions
          if (t.acc && is_entering_[si_.scc_of(t.dst)])
          {
            coming_states.insert(t.dst);
          }
        }
      }

      // now compute the successors for (P, Q) states
      std::set<std::pair<state_set, state_set>, set_pair_compare> visited;
      unsigned acc_index = ms.pset_.size();
      unsigned rej_index = ms.pset_.size();
      for (unsigned i = 0; i < ms.pset_.size(); i++)
      {
        bool accepting_trans = false;
        std::pair<state_set, state_set> set_pair = get_set_successors(ms.pset_[i], ms.qset_[i], letter, succ.reach_set_, accepting_trans);
        // check whether this set is already existing
        if (visited.find(set_pair) == visited.end())
        {
          succ.pset_.push_back(set_pair.first);
          succ.qset_.push_back(set_pair.second);
          visited.insert(set_pair);
        }
        else
        // already there, so ignore
        {
          rej_index = std::min(rej_index, i);
        }
        if (accepting_trans)
        {
          acc_index = std::min(acc_index, i);
        }
      }
      for (auto s : coming_states)
      {
        state_set acc_set;
        acc_set.insert(s);
        state_set empty_set;
        std::pair<state_set, state_set> set_pair = std::make_pair(acc_set, empty_set);
        if (visited.find(set_pair) == visited.end())
        {
          succ.pset_.push_back(acc_set);
          succ.qset_.push_back(empty_set);
        }
      }
      // remove redudant states with simulation relation
      if (use_simulation_) make_simulation_state(succ);
      
      // update acc and rej
      for (unsigned i = 0; i < ms.pset_.size() && i < succ.pset_.size(); i++)
      {
        if (succ.pset_[i].empty())
        {
          rej_index = std::min(rej_index, i);
        }
        else if (succ.pset_[i] == succ.qset_[i])
        {
          acc_index = std::min(acc_index, i);
        }
      }

      int parity;
      int acc_color = 2 * ((int)acc_index + 1);
      int rej_color = 2 * ((int)rej_index) + 1;
      if (rej_index == ms.pset_.size() && acc_index != ms.pset_.size())
      {
        parity = acc_color;
      }
      else if (rej_index != ms.pset_.size() && acc_index == ms.pset_.size())
      {
        parity = rej_color;
      }
      else if (rej_index != ms.pset_.size() && acc_index != ms.pset_.size())
      {
        parity = std::min(acc_color, rej_color);
      }
      else
      {
        parity = -1;
      }
      std::vector<state_set> pset;
      std::vector<state_set> qset;
      for (unsigned i = 0; i < succ.pset_.size(); i++)
      {
        pset.push_back(succ.pset_[i]);
        qset.push_back(succ.qset_[i]);
      }
      visited.clear();
      succ.pset_.clear();
      succ.qset_.clear();
      for (unsigned i = 0; i < pset.size(); i++)
      {
        std::pair<state_set, state_set> set_pair = std::make_pair(pset[i], qset[i]);
        if (visited.find(set_pair) == visited.end() && !pset[i].empty())
        {
          succ.pset_.push_back(pset[i]);
          succ.qset_.push_back(qset[i]);
        }
      }
      nxt = succ;
      color = parity;
    }
    // copied and adapted from deterministic.cc in Spot
    void
    make_stutter_state(const mstate &curr, unsigned origin, bdd letter, mstate &succ, int &color)
    {
      mstate ms(curr);
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
          stutter_path.emplace_back(ms);
          // next state
          mstate tmp_succ;
          int tmp_color = -1;
          rank_successors(stutter_path.back(), origin, letter, tmp_succ, tmp_color);
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
            if (exists(*it) && *it < *cycle_seed)
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
            else if (*it < *cycle_seed)
            {
              cycle_seed = it;
            }
          }
        }
        succ = *cycle_seed;
        color = mincolor;
      }
      else
      {
        rank_successors(ms, origin, letter, succ, color);
      }
    }

  public:
    tba_determinize(const spot::const_twa_graph_ptr &aut, spot::scc_info& si, spot::option_map& om, std::vector<bdd>& implications)
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
          simulator_(aut_, si, implications, om.get(USE_SIMULATION) > 0),
          show_names_(om.get(VERBOSE_LEVEL) >= 2)
    {
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
        // all outgoing transitions are accepting
        is_accepting_[i] = accepting && has_transitions;
      }

      //std::cout << "Simulator\n";
      //simulator_.output_simulation();
      is_entering_ = get_accepting_reachable_sccs(si_);
      // optimize with the fact of being unambiguous
      use_unambiguous_ = use_unambiguous_ && is_unambiguous(aut);
      if (show_names_)
      {
        names_ = new std::vector<std::string>();
        res_->set_named_prop("state-names", names_);
      }

      unsigned init_state = aut->get_init_state_number();
      mstate new_init_state(init_state);
      unsigned index = new_state(new_init_state);
      // we assume that the initial state is not in deterministic part
      res_->set_init_state(index);
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
        for (unsigned s : ms.reach_set_)
        {
          msupport &= support_[s];
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
          //rank_successors(std::move(ms), top.second, letter, succ, color);
          make_stutter_state(ms, top.second, letter, succ, color);

          unsigned origin = top.second;
          // add transitions
          // Create the automaton states
          unsigned dst = new_state(succ);
          // const unsigned MAX_PRI = 2* nb_det_states_ + 1;
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
      // spot::print_hoa(std::cout, res_, nullptr);
      //   std::cout << "\n";
      res_ = postprocess(res_);
      cleanup_parity_here(res_);
      // spot::print_hoa(std::cout, res_, nullptr);
      //   std::cout << "\n";
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
        for (unsigned s : p->first.reach_set_)
        {
          set.insert(s);
        }
        auto val = set2scc.find(set);
        if (val == set2scc.end())
        {
          // the set of macrostates in DPA
          state_set v;
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
      if(om_.get(VERBOSE_LEVEL) >= 1)
         std::cout << "The number of states reduced by mstate_merger: "
              << (aut->num_states() - res->num_states()) << " {out of "
              << aut->num_states() << "}" << std::endl;
      return res;
    }
  };

  spot::twa_graph_ptr
  determinize_tba(const spot::const_twa_graph_ptr &aut, spot::option_map& om)
  {
    if (!aut->acc().is_buchi())
      throw std::runtime_error("determinize_tba() requires a Buchi input");
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

    auto det = cola::tba_determinize(aut_reduced, scc, om, implications);
    return det.run();
  }
}