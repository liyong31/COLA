// Copyright (C) 2017-2020  The Seminator Authors
// Copyright (C) 2021  The COLA Authors
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

#include "optimizer.hpp"
#include "cola.hpp"
#include "simulation.hpp"

#include <algorithm>

#include <spot/twaalgos/simulation.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/isunamb.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twa/twagraph.hh>

namespace cola
{
    mstate_merger::mstate_merger(spot::twa_graph_ptr &dpa, const mstate_equiv_map &equiv_map
    , spot::scc_info& si, spot::option_map& om)
        : dpa_(dpa), equiv_map_(equiv_map), si_(si), om_(om)
    {
    }
  spot::twa_graph_ptr
  mstate_merger::run()
  {
    unsigned num_states = dpa_->num_states();
    // a map that maps the original mstate to the replaced mstate
    std::vector<unsigned> replace_states(num_states);
    // by default the replacement is itself
    for (unsigned s = 0; s < num_states; s++)
    {
      replace_states[s] = s;
    }
    // reach_sccs[i + scccount*j] = 1 iff SCC i is reachable from SCC j
    // unsigned num_size = scc.scc_count();
    // num_size = 8 * num_size * num_size;
    // int memory_limit = om_.get(SCC_REACH_MEMORY_LIMIT);
    // std::vector<bool> reach_sccs;
    // if (memory_limit == 0 || num_size <= (memory_limit * (1 << 20)))
    // {
    //   // if the memory usage is not too large
    //   reach_sccs = find_scc_paths_(scc);
    //   // std::vector<bool> another = find_scc_paths_(scc);
    // }
    // // whether the state s can reach t
    // auto scc_reach = [&scc, &reach_sccs](unsigned s, unsigned t) -> bool
    // {
    //   if (s == t) return true;
    //   // s reach t, then s > t 
    //   if (s < t) return false;
    //   if (! reach_sccs.empty())
    //     // return (reach_sccs[t + scc.scc_count() * s]);
    //     return (reach_sccs[t + s * (s + 1)/2]);
    //   else 
    //   {
    //     // we traverse the map
    //     unsigned nscc = s;
    //     std::vector<bool> reachable(scc.scc_count(), false);
    //     reachable[s] = true;
    //     while(true) // iterator of SCCs in reverse topological order
    //     {
    //       // larger nscc is closer to initial state?
    //       if (reachable[nscc])
    //         {
    //           for (unsigned succ: scc.succ(nscc))
    //           {
    //             if (succ == t) return true;
    //             reachable[succ] = true;
    //           }
    //         }
    //         // s != t
    //         if (! nscc)
    //         {
    //           break;
    //         }
    //         --nscc;
    //     }
    //     return false;
    //   }
    // };
    // set of states -> the forest of reachability in the states.
    // output
    spot::scc_info scc = si_;
    bool debug = false;
    unsigned num_replaced_states = 0;
    // Key: set of reached states in NBA, Value: the mstates with the same Key
    for (auto p = equiv_map_.begin(); p != equiv_map_.end(); p++)
    {
      // if there is only one mstate, no need to replace
      if (p->second.size() <= 1)
        continue;
      if (debug)
      {
        std::cout << "state = " + get_set_string(p->first) + "\n";
        for (auto t : p->second)
        {
          std::cout << " " << t << "(" << scc.scc_of(t) << ")";
        }
        std::cout << "\n";
      }
      // now compute states
      // std::vector<unsigned> reach_vec(scc.scc_count());
      // indicator for no successor SCC
      // unsigned no_next_scc = scc.scc_count();
      // for (unsigned scc_i = 0; scc_i < scc.scc_count(); scc_i++)
      // {
        // first set to non scc
        // reach_vec[scc_i] = no_next_scc;
      // }
      // std::set<unsigned> not_bottom_set;
      std::set<unsigned> bottom_set;
      // traverse the number of states in p->second
      std::unordered_map<unsigned, unsigned> scc2repr;
      unsigned min_scc = scc.scc_count();
      for (auto s : p->second)
      {
        unsigned scc_s_idx = scc.scc_of(s);
        // by construction, an SCC with smaller index cannot reach an SCC with larger index
        min_scc = std::min(scc_s_idx, min_scc);
        bottom_set.insert(scc_s_idx);
        auto val_state = scc2repr.find(scc_s_idx);
        if (val_state == scc2repr.end())
        {
          scc2repr[scc_s_idx] = s;
        }
        else
        {
          // keep the smallest one
          scc2repr[scc_s_idx] = std::min(s, scc2repr[scc_s_idx]);
        }
      }
      // if all mstates are in the same SCC, no need to replace states
      if (bottom_set.size() <= 1)
      {
        continue;
      }
      // check the reachability of SCCs
      // for (auto fst_scc : bottom_set)
      // {
      //   for (auto snd_scc : bottom_set)
      //   {
      //     if (fst_scc == snd_scc)
      //       continue;
      //     if (scc_reach(fst_scc, snd_scc))
      //     {
      //       // only record the smallest SCC that fst_scc can reach so far
      //       reach_vec[fst_scc] = std::min(snd_scc, reach_vec[fst_scc]);
      //       // record the SCC that have successors
      //       not_bottom_set.insert(fst_scc);
      //       continue;
      //     }
      //   }
      // }
      // if (debug)
      // {
      //   std::cout << "Bottom set: {";
      //   for (auto s : bottom_set)
      //   {
      //     if (not_bottom_set.find(s) == not_bottom_set.end())
      //     {
      //       std::cout << " " << s << " (state=" << scc2repr[s] << ")";
      //     }
      //     else
      //     {
      //       std::cout << " " << s << "(next=" << reach_vec[s] << ") ";
      //     }
      //   }
      //   std::cout << "}\n";
      // }
      // reach the bottom scc from a given scc
      // auto get_bottom_scc = [&reach_vec, &no_next_scc](unsigned scc_idx) -> unsigned
      // {
      //   while (true)
      //   {
      //     if (reach_vec[scc_idx] == no_next_scc)
      //     {
      //       break;
      //     }
      //     scc_idx = reach_vec[scc_idx];
      //   }
      //   return scc_idx;
      // };
      // compute the replacement of each state
      // unsigned smallest_bottom_scc = scc.scc_count();
      // for (auto t : p->second)
      // {
      //   unsigned scc_idx = scc.scc_of(t);
        // unsigned bottom_scc_idx = get_bottom_scc(scc_idx);
        // if t is not in the bottom scc, then it can be replace by a state in
        // the bottom scc
      //   smallest_bottom_scc = std::min(smallest_bottom_scc, bottom_scc_idx);
      // }
      for (auto t : p->second)
      {
        unsigned scc_idx = scc.scc_of(t);
        if (min_scc != scc_idx)
        {
          replace_states[t] = scc2repr[min_scc];
          ++num_replaced_states;
          if (om_.get(VERBOSE_LEVEL) >= 2)
          {
            std::cout << "State " << t << " replaced by State " << scc2repr[min_scc] << "\n";
          }
        }
      }
    }
    if (num_replaced_states == 0)
    {
      return dpa_;
    }

    // now construct new DPAs
    spot::twa_graph_ptr res = spot::make_twa_graph(dpa_->get_dict());
    res->copy_ap_of(dpa_);
    res->prop_copy(dpa_,
                   {
                       false,        // state based
                       false,        // inherently_weak
                       false, false, // deterministic
                       true,         // complete
                       false         // stutter inv
                   });
    for (unsigned s = 0; s < num_states; s++)
    {
      res->new_state();
    }
    for (auto &t : dpa_->edges())
    {
      // out going transition for t.src
      if (t.src == replace_states[t.src] && t.dst == replace_states[t.dst])
      {
        res->new_edge(t.src, t.dst, t.cond, t.acc);
      }
      else if (t.src == replace_states[t.src] && t.dst != replace_states[t.dst])
      {
        res->new_edge(t.src, replace_states[t.dst], t.cond, t.acc);
      }
      // igonre the rest cases
      //t.src != replace_states[t.src] && t.dst == replace_states[t.dst])
      //t.src != replace_states[t.src] && t.dst != replace_states[t.dst])
    }
    // names
    if (om_.get(VERBOSE_LEVEL) > 0)
    {
      auto sn = dpa_->get_named_prop<std::vector<std::string>>("state-names");
      if(sn) res->copy_state_names_from(dpa_);
    }
    
    res->set_init_state(replace_states[dpa_->get_init_state_number()]);
    // now acceptance condition
    if(dpa_->acc().is_co_buchi())
    {
      dpa_->set_co_buchi();
    }else 
      res->set_acceptance(dpa_->num_sets(), dpa_->get_acceptance());
    if (dpa_->prop_complete().is_true())
      res->prop_complete(true);
    res->prop_universal(true);
    res->prop_state_acc(false);
    // remove unreachable macrostates
    res->purge_unreachable_states();
    return res;
  }

  // -------------- state_simulator ----------------------
  state_simulator::state_simulator(const spot::const_twa_graph_ptr &nba, spot::scc_info &si, std::vector<bdd> &implications, bool use_simulation)
      : nba_(nba), si_(si)
  {
    is_connected_ = find_scc_paths(si);
    if (!use_simulation)
    {
      return;
    }
    for (unsigned i = 0; i < nba_->num_states(); i++)
    {
      std::vector<bool> elem;
      for (unsigned j = 0; j < nba_->num_states(); j++)
      {
        elem.push_back(i == j);
      }
      is_implies_.push_back(elem);
    }
    // If use_simulation is false, implications is empty, so nothing is built
    std::vector<std::vector<char>> implies(
        implications.size(),
        std::vector<char>(implications.size(), 0));
    {
      unsigned sccs = si.scc_count();
      bool something_implies_something = false;
      for (unsigned i = 0; i != implications.size(); ++i)
      {
        // COPIED from Spot determimze.cc
        // NB spot::simulation() does not remove unreachable states, as it
        // would invalidate the contents of 'implications'.
        // so we need to explicitly test for unreachable states
        // FIXME based on the scc_info, we could remove the unreachable
        // states, both in the input automaton and in 'implications'
        // to reduce the size of 'implies'.
        if (!si_.reachable_state(i))
          continue;
        unsigned scc_of_i = si_.scc_of(i);
        bool i_implies_something = false;
        for (unsigned j = 0; j != implications.size(); ++j)
        {
          //reachable states
          if (!si_.reachable_state(j))
            continue;
          // j simulates i and j cannot reach i
          bool i_implies_j = bdd_implies(implications[i], implications[j]);
          implies[i][j] = i_implies_j;
          i_implies_something |= i_implies_j;
        }
        // Clear useless lines.
        if (!i_implies_something)
          implies[i].clear();
        else
          something_implies_something = true;
      }
      if (!something_implies_something)
      {
        implies.clear();
      }
    }
    // store simulation relation
    for (int i = 0; i < implies.size(); i++)
    {
      for (int j = 0; j < implies[i].size(); j++)
      {
        if (i == j)
          continue;
        // j contains the language of i
        is_implies_[j][i] = (implies[i][j] >= 1);
      }
    }
  }
  state_simulator::state_simulator(const state_simulator &other)
      : nba_(other.nba_), si_(other.si_)
  {
    for (unsigned i = 0; i < other.is_implies_.size(); i++)
    {
      std::vector<bool> elem;
      for (unsigned j = 0; j < other.is_implies_[i].size(); j++)
      {
        elem.push_back(other.is_implies_[i][j]);
      }
      this->is_implies_.push_back(elem);
    }
    for (unsigned i = 0; i < other.is_connected_.size(); i++)
    {
      this->is_connected_.push_back(other.is_connected_[i]);
    }
  }

  void state_simulator::output_simulation()
  {
    for (int i = 0; i < is_implies_.size(); i++)
    {
      for (int j = 0; j < is_implies_[i].size(); j++)
      {
        if (i == j || !is_implies_[i][j])
          continue;
        // j contains the language of i
        std::cout << j << " is simulated by " << i << " : " << (is_implies_[i][j]) << std::endl;
      }
    }
  }

  // state i reach state j
  char state_simulator::can_reach(unsigned i, unsigned j)
  {
    unsigned scc_of_i = si_.scc_of(i);
    unsigned scc_of_j = si_.scc_of(j);
    if (scc_of_i < scc_of_j) return 0;
    if (scc_of_i == scc_of_j) return 1;
    // test whether j is reachable from i
    return is_connected_[scc_of_j + si_.scc_count() * scc_of_i];
  }

  char state_simulator::can_reach_scc(unsigned scc1, unsigned scc2)
  {
    return is_connected_[scc2 + si_.scc_count() * scc1];
  }
  // check whether state i simulates state j
  bool state_simulator::simulate(unsigned i, unsigned j)
  {
    return is_implies_[i][j];
  }

  edge_strengther::edge_strengther(spot::const_twa_graph_ptr nba, const spot::scc_info &si, unsigned threshold)
      : enumerate_cycles(si), nba_(nba), threshold_(threshold)
  {
  }

  bool
  edge_strengther::fix_scc(const unsigned m)
  {
    overlap_.clear();
    overlap_initialized = false;
    cycles_left_ = threshold_;
    run(m);
    // all accepting cycles will visit these edges
    for (trans *t : overlap_)
    {
      // std::cout << "orig = " << t->acc;
      if (! t->acc)
      {
        t->acc = {0};
      }
      // std::cout << " renewed = " << t->acc << std::endl;
    }
    return threshold_ != 0 && cycles_left_ == 0;
  }

  bool
  edge_strengther::is_cycle_accepting(cycle_iter begin, edge_set &ts) const
  {
    auto a = std::const_pointer_cast<spot::twa_graph>(nba_);
    // Check if the loop is acceptingin the automaton.
    bool accepting = false;
    for (cycle_iter i = begin; i != dfs_.end(); ++i)
    {
      trans *t = &a->edge_data(i->succ);
      if (t->acc)
      {
        accepting = true;
      }
      ts.insert(t);
    }
    if (!accepting)
    {
      ts.clear();
    }
    return accepting;
  }

}
