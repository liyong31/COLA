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
#include "simulation.hpp"
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

// Determinization of TwBAs via breakpoint construction
namespace cola
{
  // macrostate
  class wmstate final
  {
  public:
    wmstate(state_t init_state)
    {
      reach_set_.insert(init_state);
    }
    wmstate()
    {
    }
    wmstate(const wmstate &other)
    {
      reach_set_.clear();
      reach_set_.insert(other.reach_set_.begin(), other.reach_set_.end());

      break_set_.clear();
      break_set_.insert(other.break_set_.begin(), other.break_set_.end());
    }
    bool operator<(const wmstate &other) const;
    bool operator==(const wmstate &other) const;

    size_t hash() const;
    // the set of reachable states in this level
    state_set reach_set_;
    // breakpoint construction
    state_set break_set_;
  };

  bool
  wmstate::operator<(const wmstate &other) const
  {
    if (reach_set_ == other.reach_set_)
    {
      return break_set_ < other.break_set_;
    }
    return reach_set_ < other.reach_set_;
 }
  bool
  wmstate::operator==(const wmstate &other) const
  {
    return reach_set_ == other.reach_set_
         && break_set_ == other.break_set_;
  }

  size_t
  wmstate::hash() const
  {
    size_t res = 0;
    for (unsigned i : reach_set_) // not sure how you're storing them
    {
      res = (res << 3) ^ (i);
    }
    for (unsigned i : break_set_)
    {
      res ^= (res << 3) ^ i;
    }
    
    return res;
  }

  std::string
  get_name(const wmstate &ms)
  {
    return get_set_string(ms.reach_set_) + ", " + get_set_string(ms.break_set_);
  }

  struct wmstate_hash
  {
    size_t
    operator()(const wmstate &s) const noexcept
    {
      return s.hash();
    }
  };


  class twba_determinize
  {
  private:
    // The source automaton.
    const spot::const_twa_graph_ptr aut_;

    // SCCs information of the source automaton.
    spot::scc_info &si_;

    //optimizer opt_;

    // Number of states in the input automaton.
    unsigned nb_states_;

    // unsigned nb_det_states_;
    state_simulator simulator_;

    // delayed simulator
    delayed_simulation delayed_simulator_;

    // The parity automata being built.
    spot::twa_graph_ptr res_;

    // the number of indices
    unsigned sets_ = 0;

    spot::option_map &om_;

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
    std::unordered_map<wmstate, unsigned, wmstate_hash> rank2n_;

    // States to process.
    std::deque<std::pair<wmstate, unsigned>> todo_;

    // Support for each state of the source automaton.
    std::vector<bdd> support_;

    // Propositions compatible with all transitions of a state.
    std::vector<bdd> compat_;

    // State names for graphviz display
    std::vector<std::string> *names_;

    // Show Rank states in state name to help debug
    bool show_names_;

    // From a Rank state, looks for a duplicate in the map before
    // creating a new state if needed.
    unsigned
    new_state(wmstate &s)
    {
      // std::cout << "new state: " << get_name(s) << std::endl;
      //wmstate s_p(s);
      // std::cout << "copy state: " << get_name(s) << std::endl;
      wmstate dup(s);
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

    bool exists(wmstate &s)
    {
      return rank2n_.end() != rank2n_.find(s);
    }

    // remove a state i if it is simulated by a state j
    void
    make_simulation_state(wmstate &ms)
    {
      state_set removed_states;
      state_set reach_states;

      for (auto s : ms.reach_set_)
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
          if ((simulator_.simulate(j, i) || delayed_simulator_.simulate(j, i)) && simulator_.can_reach(j, i) == 0)
          {
            removed_states.insert(i);
          }
        }
      }
      ms.reach_set_.clear();
      // now remove all states in removed_states
      std::set_difference(reach_states.begin(), reach_states.end()
                        , removed_states.begin(), removed_states.end()
                        , std::inserter(ms.reach_set_, ms.reach_set_.begin()));

      state_set break_set;
      std::set_difference(ms.break_set_.begin(), ms.break_set_.end()
                , removed_states.begin(), removed_states.end()
                , std::inserter(break_set, break_set.begin()));
      ms.break_set_ = break_set;

    }

    void
    rank_successors(const wmstate &ms, unsigned origin, bdd letter, wmstate &nxt, int &color)
    {
      wmstate succ;
      std::vector<bool> incoming(nb_states_, false);
      std::vector<bool> ignores(nb_states_, false);
      // first handle nondeterministic states
      std::set<unsigned> coming_states;
      //std::vector<unsigned> acc_coming_states;
      for (unsigned s : ms.reach_set_)
      {
        bool in_break_set = (ms.break_set_.find(s) != ms.break_set_.end());
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
          bool in_acc_scc = si_.is_accepting_scc(si_.scc_of(t.dst));
          // via accepting transitions, assuming it weak automaton
          if (in_acc_scc)
          {
            coming_states.insert(t.dst);
          }
          // only keep the states in accepting SCC
          if (in_break_set && in_acc_scc)
          {
            succ.break_set_.insert(t.dst);
          }
        }
      }
      

      // remove redudant states with simulation relation
      if (use_simulation_)
        make_simulation_state(succ);
      
      int parity = 2;
      // B' is empty
      if (succ.break_set_.empty())
      {
        parity = 1;
        state_set result;
        std::set_intersection(succ.reach_set_.begin(), succ.reach_set_.end()
              , coming_states.begin(), coming_states.end(), std::inserter(result, result.begin()));
        succ.break_set_ = result;
      }

      nxt = succ;
      color = parity;
    }
    // copied and adapted from deterministic.cc in Spot
    void
    make_stutter_state(const wmstate &curr, unsigned origin, bdd letter, wmstate &succ, int &color)
    {
      wmstate ms(curr);
      std::vector<wmstate> stutter_path;
      if (use_stutter_ && aut_->prop_stutter_invariant())
      {
        // The path is usually quite small (3-4 states), so it's
        // not worth setting up a hash table to detect a cycle.
        stutter_path.clear();
        std::vector<wmstate>::iterator cycle_seed;
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
          wmstate tmp_succ;
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
        }        // check whether this ms has been seen before
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
    twba_determinize(const spot::const_twa_graph_ptr &aut, spot::scc_info &si, spot::option_map &om, std::vector<bdd> &implications)
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
          simulator_(aut_, si, implications, om.get(USE_SIMULATION) > 0),
          delayed_simulator_(aut, om),
          show_names_(om.get(VERBOSE_LEVEL) >= 1)
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
        for (const auto &out : aut->out(i))
        {
          res_support &= bdd_support(out.cond);
          res_compat |= out.cond;
        }
        support_[i] = res_support;
        compat_[i] = res_compat;
      }

      if (use_stutter_ && aut_->prop_stutter_invariant())
      {
        for (unsigned c = 0; c != si_.scc_count(); ++c)
            {
              bdd c_supp = si_.scc_ap_support(c);
              for (const auto& su: si_.succ(c))
                c_supp &= support_[si_.one_state_of(su)];
              for (unsigned st: si_.states_of(c))
                support_[st] = c_supp;
            }
      }

      //std::cout << "Simulator\n";
      //simulator_.output_simulation();
      // is_entering_ = get_accepting_reachable_sccs(si_);
      // optimize with the fact of being unambiguous
      use_unambiguous_ = use_unambiguous_ && is_unambiguous(aut);
      if (show_names_)
      {
        names_ = new std::vector<std::string>();
        res_->set_named_prop("state-names", names_);
      }

      unsigned init_state = aut->get_init_state_number();
      wmstate new_init_state(init_state);
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
        wmstate ms = top.first;
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

          wmstate succ;
          int color = -1;
          //rank_successors(std::move(ms), top.second, letter, succ, color);
          make_stutter_state(ms, top.second, letter, succ, color);

          unsigned origin = top.second;
          // add transitions
          // Create the automaton states
          unsigned dst = new_state(succ);
          // const unsigned MAX_PRI = 2* nb_det_states_ + 1;
          if (color & 1)
          {
            unsigned pri = (unsigned)color;
            //sets_ = std::max(pri, sets_);
            res_->new_edge(origin, dst, letter, { 0});
          }
          else
          {
            res_->new_edge(origin, dst, letter);
          }
        }
      }
      // Acceptance is now min(odd) since we can emit Red on paths 0 with new opti
      res_->set_acceptance(1, spot::acc_cond::acc_code::fin({0}));
      if (aut_->prop_complete().is_true())
        res_->prop_complete(true);
      res_->prop_universal(true);
      res_->prop_state_acc(false);
      // spot::print_hoa(std::cout, res_, nullptr);
      //   std::cout << "\n";
      if (om_.get(USE_SCC_INFO) > 0) res_ = postprocess(res_);
      // cleanup_parity_here(res_);
      // spot::print_hoa(std::cout, res_, nullptr);
      //   std::cout << "\n";
      return res_;
    }

    spot::twa_graph_ptr
    postprocess(spot::twa_graph_ptr aut)
    {
      spot::scc_info scc_dpa(aut, spot::scc_info_options::ALL);
      if (om_.get(NUM_SCC_LIMIT_MERGER) != 0 && om_.get(NUM_SCC_LIMIT_MERGER) < scc_dpa.scc_count())
      {
        return aut;
      }
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
      mstate_merger merger(aut, set2scc, scc_dpa, om_);
      spot::twa_graph_ptr res = merger.run();
      if (om_.get(VERBOSE_LEVEL) >= 1)
        std::cout << "The number of states reduced by mstate_merger: "
                  << (aut->num_states() - res->num_states()) << " {out of "
                  << aut->num_states() << "}" << std::endl;
      return res;
    }
  };

  spot::twa_graph_ptr
  determinize_twba(const spot::const_twa_graph_ptr &aut, spot::option_map &om)
  {
    if (!aut->acc().is_buchi())
      throw std::runtime_error("determinize_twba() requires a Buchi input");
    // now we compute the simulator
    spot::const_twa_graph_ptr aut_reduced;
    std::vector<bdd> implications;
    spot::twa_graph_ptr aut_tmp = nullptr;
    if (om.get(USE_SIMULATION) > 0)
    {
      aut_tmp = spot::scc_filter(aut);
      auto aut2 = spot::simulation(aut_tmp, &implications);
      aut_tmp = aut2;
    }
    if (aut_tmp)
      aut_reduced = aut_tmp;
    else
      aut_reduced = aut;
    spot::scc_info scc(aut_reduced, spot::scc_info_options::ALL);

    auto det = cola::twba_determinize(aut_reduced, scc, om, implications);
    return det.run();
  }
}