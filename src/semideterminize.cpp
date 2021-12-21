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


#include "optimizer.hpp"
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

                      template<class T>
                      struct pair_compare
                      {
                        bool operator() (const std::pair<T, T>& lhs,
                                        const std::pair<T, T>& rhs) const
                        {
                          if (lhs.first == rhs.first)
                            return lhs.second < rhs.second;
                          else
                            return lhs.first < rhs.first;
                        }
                      };
    using state_t = unsigned;
    using state_set = std::set<state_t>;
    //using node_t = std::pair<, std::set<state_t>>;  
    const int RANK_N = -1; // nondeterministic
    const int RANK_M = -2; // missing value

    void copy_set_to(state_set& S1, state_set& S2)
    {
      for(auto s : S1)
      {
        S2.insert(s);
      }
    }
    // macrostate
    class mstate final
    {
      void
      check() const
      {
        // all states in P and Q are in reach_set_ and Q \subseteq P
        assert(qset_.size() == pset_.size());
        unsigned num = qset_.size();
        for(unsigned i = 0; i < num; i ++)
        {
          for(state_t s : qset_[i])
          {
            assert(pset_[i].find(s) != pset_[i].end());
          }
          for(state_t s : pset_[i])
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
      mstate(const mstate& other)
      {
        reach_set_.clear();
        state_set oreach_set = other.reach_set_;
        copy_set_to(oreach_set, reach_set_);
        pset_.clear();
        qset_.clear();
        for(unsigned i = 0; i < other.pset_.size(); i ++)
        {
          state_set pset;
          state_set qset;
          state_set opset = other.pset_[i];
          state_set oqset = other.qset_[i];
          copy_set_to(opset, pset);
          copy_set_to(oqset, qset);
          pset_.push_back(pset);
          qset_.push_back(qset);
        }
      }
      mstate() {}
      bool operator<(const mstate& other) const;
      bool operator==(const mstate& other) const;

      size_t hash() const;
      // the set of reachable states in this level
      state_set reach_set_;
      // this is the list of nodes that ordered due to later introduction record
      std::vector<state_set> qset_;
      std::vector<state_set> pset_;
    };

    std::string 
    get_set_string(const state_set& set)
    {
      std::string res = "{";
      bool first = true;
      for(state_t s : set)
      {
        if(first)
        {
          first = false;
        }else 
        {
          res += ", ";
        }
        res += std::to_string(s);
      }
      res += "}";
      return res;
    }

    size_t
    hash_unsigned_set(const state_set& uset)
    {
      size_t hash = 0;
      for(auto i : uset)   // not sure how you're storing them
      {
        hash = ((31 * hash) + (unsigned)i);
      }
      return hash;
    }

    bool
    mstate::operator<(const mstate& other) const 
    {
        if(reach_set_ < other.reach_set_)
        {
          return true;
        }
        if(reach_set_ > other.reach_set_)
        {
          return false;
        }
        if(pset_.size() < other.pset_.size())
        {
          return true;
        }
        if(pset_.size() > other.pset_.size())
        {
          return false;
        }
        for(unsigned i = 0; i < pset_.size(); i ++)
        {
          if(pset_[i] < other.pset_[i])
          {
            return true;
          }
          if(pset_[i] > other.pset_[i])
          {
            return false;
          }
          if(qset_[i] < other.qset_[i])
          {
            return true;
          }
          if(qset_[i] > other.qset_[i])
          {
            return false;
          }
        }
        return false;
    }
    bool
    mstate::operator==(const mstate& other) const
      {
        if(reach_set_ != other.reach_set_)
        {
          return false;
        }
        if(pset_.size() != other.pset_.size())
        {
          return false;
        }
        for(unsigned i = 0; i < pset_.size(); i ++)
        {
          if(pset_[i] != other.pset_[i])
          {
            return false;
          }
          if(qset_[i] != other.qset_[i])
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

      for (unsigned i = 0; i < pset_.size(); i ++)
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
    get_name(const mstate& ms)
    {
      std::string res = get_set_string(ms.reach_set_) + ",[";
      bool first = true;
      for(unsigned i = 0; i < ms.pset_.size(); i ++)
      {
        if(! first)
        {
          res += ", ";
        }else 
        {
          first = false;
        }
        res += "(" + get_set_string(ms.pset_[i]) + ", " + get_set_string(ms.qset_[i]) + ") = " + std::to_string(i);
      }
      res += "]";
      return res;
    }
    struct mstate_hash
    {
      size_t
      operator()(const mstate& s) const noexcept
      {
        return s.hash();
      }
    };

    bool 
    is_subset(state_set& x, state_set& y)
    {
      for(auto s : x)
      {
        if(y.find(s) == y.end())
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
              spot::scc_info si_;

              optimizer opt_;

              // Number of states in the input automaton.
              unsigned nb_states_;

              // unsigned nb_det_states_;

              // The parity automata being built.
              spot::twa_graph_ptr res_;

              // the number of indices
              unsigned sets_ = 0;
            
              // number of colors used
              unsigned num_colors_;

              // use ambiguous
              bool use_unambiguous_;

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

              // Whether a SCC is deterministic or not
              //std::vector<bool> is_deter_;

              // Whether a state only has accepting transitions
              std::vector<bool> is_accepting_;

              // State names for graphviz display
              std::vector<std::string>* names_;

              // Show Rank states in state name to help debug
              bool show_names_;


                    // From a Rank state, looks for a duplicate in the map before
                    // creating a new state if needed.
                    unsigned
                    new_state(mstate& s)
                    {
                      //std::cout << "new state: " << get_name(s) << std::endl;
                      //mstate s_p(s);
                      // std::cout << "copy state: " << get_name(s) << std::endl;
                      auto p = rank2n_.emplace(s, 0);
                      if (p.second) // This is a new state
                      {
                        p.first->second = res_->new_state();
                        if (show_names_)
                          names_->push_back(get_name(p.first->first));
                        todo_.emplace_back(s, p.first->second);
                      }
                      return p.first->second;
                    }

                    bool exists(mstate& s)
                    {
                      return rank2n_.end() == rank2n_.find(s);
                    }


                    // remove a state i if it is simulated by a state j
                    void 
                    make_simulation_state(mstate& ms)
                    {
                      state_set reached_states;
                      state_set removed_states;
                      for(auto s : ms.reach_set_)
                      {
                        reached_states.insert(s);
                      }
                      for(unsigned i : reached_states)
                      {
                        for(unsigned j : reached_states)
                        {
                          // if j is not reached at this level
                          if(i == j ) continue;
                          //std::cout << "start simulated" << std::endl;
                          // j simulates i and j cannot reach i
                          if(opt_.simulate(j, i) && opt_.reach(j, i) == 0) 
                          {
                            removed_states.insert(i);
                          }
                        }
                      }
                      // now remove all states in removed_states
                      ms.reach_set_.erase(removed_states.begin(), removed_states.end());
                      for(unsigned i = 0; i < ms.pset_.size(); i ++)
                      {
                        ms.pset_[i].erase(removed_states.begin(), removed_states.end());
                        ms.qset_[i].erase(removed_states.begin(), removed_states.end());
                      }
                      // keep the empty set
                      //compare (P1, Q1) and (P2, Q2) such that P1 \subseteq P2, and Q1 \superset Q2
                      // then the language of (P1, Q1) includes the language of (P2, Q2)
                      // To be proved
                      std::set<unsigned> removed_indices;
                      for(unsigned i = 0; i < ms.pset_.size(); i ++)
                      {
                        if(ms.pset_[i].empty()) continue;
                        for(unsigned j = i + 1; j < ms.pset_.size(); j ++)
                        {
                          //if(i == j) continue;
                          if(is_subset(ms.pset_[i], ms.pset_[j]) && is_subset(ms.qset_[j], ms.qset_[i]))
                          {
                            removed_indices.insert(j);
                          }
                        }
                      }
                      // clear those indices
                      for(unsigned i : removed_indices)
                      {
                        ms.pset_[i].clear();
                        ms.qset_[i].clear();
                      }
                    }

                    std::pair<std::set<state_t>, std::set<state_t>>
                    get_set_successors(const std::set<state_t>& P, const std::set<state_t>& Q, bdd letter, const std::set<state_t>& restricts, bool & acc)
                    {
                      std::set<state_t> pPrime;
                      std::set<state_t> pAccPrime;
                      std::set<state_t> qDPrime;
                      std::set<state_t> qPrime;
                      
                      for(auto s : P)
                      {
                        for (const auto &t: aut_->out(s))
                          {
                            // ignore unreachable states and states that are not in restructs
                            if (!bdd_implies(letter, t.cond) || (restricts.find(t.dst) == restricts.end()))
                              continue;
                            pPrime.insert(t.dst);
                            if(t.acc || is_accepting_[t.dst])
                            {
                              pAccPrime.insert(t.dst);
                            }
                            if(Q.find(s) != Q.end())
                            {
                              qPrime.insert(t.dst);
                            }
                          }
                      }
                      // std::cout << "P = " << get_set_string(P) << " Q = " << get_set_string(Q) << " letter = " << letter << std::endl; 
                      // std::cout << "P' = " << get_set_string(pPrime) << " Q' = " << get_set_string(qPrime) << " PA' = " << get_set_string(pAccPrime) << std::endl; 
                      qDPrime.insert(qPrime.begin(), qPrime.end());
                      qDPrime.insert(pAccPrime.begin(), pAccPrime.end());
                      if(qDPrime == pPrime)
                      {
                        acc = !pPrime.empty();
                        qPrime = pAccPrime;
                      }else 
                      {
                        acc = false;
                        qPrime = qDPrime;
                      }
                      // std::cout << "Final : P' = " << get_set_string(pPrime) << " Q' = " << get_set_string(qPrime) << std::endl;
                      return std::make_pair(pPrime, qPrime);
                    }

                    void
                    rank_successors(const mstate& ms, unsigned origin, bdd letter, mstate& nxt, int& color)
                    {
                      mstate succ;
                      std::vector<bool> incoming(nb_states_, false);
                      std::vector<bool> ignores(nb_states_, false);
                      // first handle nondeterministic states
                      std::set<unsigned> coming_states;
                      //std::vector<unsigned> acc_coming_states;
                      for (unsigned s : ms.reach_set_)
                      {
                          for (const auto &t: aut_->out(s))
                          {
                            if (!bdd_implies(letter, t.cond))
                              continue;
                            // it is legal to ignore the states have two incoming transitions
                            // in unambiguous Buchi automaton
                            if(use_unambiguous_) 
                            {
                              if(incoming[t.dst])
                              {
                                // this is the second incoming transitions
                                ignores[t.dst] = true;
                              }else 
                              {
                                incoming[t.dst] = true;
                              }
                            }
                            if(ignores[t.dst])
                            {
                                // ignore this state
                                continue;
                            }
                            succ.reach_set_.insert(t.dst);
                            // via accepting transitions
                            if(t.acc || is_accepting_[t.dst])
                            {
                              // std::cout << "coming states: " << t.dst << std::endl;
                              coming_states.insert(t.dst);  
                            }
                          }
                      }
                      // now compute the successors for (P, Q) states
                      std::set<std::pair<std::string, std::string>, pair_compare<std::string>> visited; 
                      unsigned acc_index = ms.pset_.size();
                      unsigned rej_index = ms.pset_.size();
                      for(unsigned i = 0; i < ms.pset_.size(); i ++)
                      {
                        bool accepting_trans = false;
                        std::pair<state_set, state_set> set_pair = get_set_successors(ms.pset_[i], ms.qset_[i], letter, succ.reach_set_, accepting_trans);
                        state_set pset_succ = set_pair.first;
                        state_set qset_succ = set_pair.second;
                        // std::cout << "P = " << get_set_string(ms.pset_[i]) << " Q = " << get_set_string(ms.qset_[i]) << std::endl;
                        // std::cout << "P' = " << get_set_string(pset_succ) << " Q' = " << get_set_string(qset_succ) << " Acc = " << accepting_trans << std::endl;
                        // check whether this set is already existing
                        std::pair<std::string, std::string> str_pair = std::make_pair(get_set_string(pset_succ), get_set_string(qset_succ));
                        if(visited.find(str_pair) == visited.end())
                        {
                          succ.pset_.push_back(pset_succ);
                          succ.qset_.push_back(qset_succ);
                          visited.insert(str_pair);
                        }else 
                        // already there, so ignore
                        {
                          rej_index = std::min(rej_index, i);
                        }
                        if(accepting_trans)
                        {
                          acc_index = std::min(acc_index, i);
                        }
                      }
                      for(auto s : coming_states)
                      {
                        std::set<state_t> acc_set;
                        acc_set.insert(s);
                        std::set<state_t> empty_set;
                        std::pair<std::string, std::string> str_pair = std::make_pair(get_set_string(acc_set), get_set_string(empty_set));
                        if(visited.find(str_pair) == visited.end())
                        {
                          succ.pset_.push_back(acc_set);
                          succ.qset_.push_back(empty_set);
                        }
                      }
                      // std::cout << "state= " << get_name(ms) << " letter = " << letter << std::endl;
                      // std::cout << "State before simulation: " << get_name(succ) << std::endl;
                      // remove redudant states
                      make_simulation_state(succ);
                      // std::cout << "State after simulation: " << get_name(succ) << std::endl;
                      // now compute min_dcc (minimal index disappeared) and min_acc (minimal index accepted)
                      // std::cout << "ms-num= " << ms.pset_.size() << " succ-num=" << succ.pset_.size() << std::endl;
                      //rej_index = std::min(rej_index, succ.pset_.size());
                      for(unsigned i = 0; i < ms.pset_.size() && i < succ.pset_.size(); i ++)
                      {
                        if(succ.pset_[i].empty())
                        {
                          rej_index = std::min(rej_index, i);
                        }
                        else if(succ.pset_[i] == succ.qset_[i])
                        {
                         acc_index = std::min(acc_index, i);
                        }
                      }
                      //std::cout << "Acc = " << acc_index << " rej = " << rej_index << "\n"; 

                      int parity;
                      int acc_color = 2 * ((int)acc_index + 1);
                      int rej_color = 2 * ((int)rej_index) + 1;
                      if(rej_index == ms.pset_.size() && acc_index != ms.pset_.size()) 
                      {
                        parity = acc_color;
                      }else if(rej_index != ms.pset_.size() && acc_index == ms.pset_.size())
                      {
                        parity = rej_color;
                      }else if(rej_index != ms.pset_.size() && acc_index != ms.pset_.size()) 
                      {
                        parity = std::min(acc_color, rej_color);
                      }else {
                        parity = -1;
                      }
                      std::vector<state_set> pset;
                      std::vector<state_set> qset;
                      // std::cout << "Reorganize  \n"; 
                      visited.clear();
                      for(unsigned i = 0; i < succ.pset_.size(); i ++)
                      {
                        std::pair<std::string, std::string> str_pair = std::make_pair(get_set_string(succ.pset_[i]), get_set_string(succ.qset_[i]));
                        if(visited.find(str_pair) == visited.end() && !succ.pset_[i].empty())
                        {
                          pset.push_back(succ.pset_[i]);
                          qset.push_back(succ.qset_[i]);
                        }
                      }
                      succ.pset_ = pset;
                      succ.qset_ = qset;
                      // std::cout << "Final state = " << get_name(succ) << " color=" << parity<< std::endl;
                       // now we find whether there is bisimulate-states
                      //new_bisim_state(succ);
                      nxt = succ;
                      color = parity;
                    }
                // copied and adapted from deterministic.cc in Spot
                void
                make_stutter_state(const mstate& curr, unsigned origin, bdd letter, mstate& succ, int& color)
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
                        if(tmp_color != -1 && mincolor != -1)
                        {
                          mincolor = std::min(tmp_color, mincolor);
                        }else if(tmp_color != -1)
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
                            if (exists(*it)
                                && *it < *cycle_seed)
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
                  tba_determinize(const spot::const_twa_graph_ptr& aut, bool show_names, optimizer& opt, bool use_scc, bool use_unambiguous, bool use_stutter)
                            : aut_(aut),
                              opt_(opt),
                              use_scc_(use_scc),
                              use_stutter_(use_stutter),
                              si_(aut, spot::scc_info_options::ALL),
                              nb_states_(aut->num_states()),
                              support_(nb_states_),
                              compat_(nb_states_),
                              is_accepting_(nb_states_),
                              show_names_(show_names)
                    {
                      res_ = spot::make_twa_graph(aut->get_dict());
                      res_->copy_ap_of(aut);
                      res_->prop_copy(aut,
                          { false, // state based
                              false, // inherently_weak
                              false, false, // deterministic
                              true, // complete
                              false // stutter inv
                              });
                      // Generate bdd supports and compatible options for each state.
                      // Also check if all its transitions are accepting.
                      for (unsigned i = 0; i < nb_states_; ++i)
                      {
                        bdd res_support = bddtrue;
                        bdd res_compat = bddfalse;
                        bool accepting = true;
                        bool has_transitions = false;
                        for (const auto& out: aut->out(i))
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
                      // std::cout << "now deterministic part: " << std::endl;
                      // Compute which SCCs are part of the deterministic set.
                      //is_deter_ = spot::semidet_sccs(si_);
                      //std::cout << "now deterministic part over " << is_deter_.size() << std::endl;
                      //nb_det_states_ = 0;
                      // for(unsigned i = 0; i < nb_states_; i ++)
                      // {
                      //   std::cout << "scc = " << si_.scc_of(i) << std::endl;
                        //if(is_deter_[si_.scc_of(i)])
                        //{
                        //  nb_det_states_ ++;
                        //}
                      // }
                      // std::cout << "deterministic part computing " << std::endl;
                      // optimize with the fact of being unambiguous
                      use_unambiguous_ = use_unambiguous && is_unambiguous(aut);
                      if (show_names_)
                      {
                        names_ = new std::vector<std::string>();
                        res_->set_named_prop("state-names", names_);
                      }
                      // std::cout << "NumS: " << nb_states_ << std::endl;
                      // Because we only handle one initial state, we assume it
                      // belongs to the N set. (otherwise the automaton would be
                      // deterministic)
                      unsigned init_state = aut->get_init_state_number();
                      // std::cout << "Init: " << init_state << std::endl;
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
                          // std::cout << "Current state=" << get_name(ms) << std::endl;
                          //rank_successors(std::move(ms), top.second, letter, succ, color);
                          make_stutter_state(ms, top.second, letter, succ, color);
                          
                          unsigned origin = top.second;
                          // add transitions
                          // Create the automaton states
                          unsigned dst = new_state(succ);
                          // const unsigned MAX_PRI = 2* nb_det_states_ + 1;
                          if(color >= 0) 
                          {
                            unsigned pri = (unsigned)color;
                            sets_ = std::max(pri, sets_);
                            // std::cout << "src=" << origin << "->" << dst << ": " << letter << " {" << pri << "}" << std::endl;
                            res_->new_edge(origin, dst, letter, {pri});
                          }else 
                          {
                            // std::cout << "src=" << origin << "->" << dst << ": " << letter << std::endl;
                            res_->new_edge(origin, dst, letter);
                          }
                        }
                      }
                      // // now I output states
                      // for(auto p = rank2n_.begin(); p != rank2n_.end(); p ++)
                      // {
                      //   std::cout << "repr = " << get_name(p->first) << " --- " << p->second << "\n";
                      // }
                      // std::cout << "size: = " << bisim2n_.size() << std::endl;
                      // now copy 
                      // check the number of indices
                      unsigned max_odd_pri = -1;
                      // sets_ stores the maximal priority has ever seen
                      if(sets_ & 1)
                      {
                        max_odd_pri = sets_;
                      }else 
                      {
                        max_odd_pri = sets_ + 1;
                      }
                     
                      for (auto& t: res_->edges())
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
                        unsigned num_states = aut->num_states();
                        std::vector<unsigned> repr_states(num_states);
                        for(unsigned s = 0; s < num_states; s ++)
                        {
                          repr_states[s] = s;
                        }
                        spot::scc_info scc(aut, spot::scc_info_options::ALL);
                        // res[i + scccount*j] = 1 iff SCC i is reachable from SCC j
                        std::vector<char> reach_sccs = find_scc_paths(scc);
                        auto scc_reach = [&scc, &reach_sccs](unsigned s, unsigned t) -> bool 
                        {
                          return s == t || (reach_sccs[t + scc.scc_count() * s]);
                        };
                        struct set_hash
                        {
                          size_t
                          operator()(std::set<unsigned> s) const noexcept
                          {
                            size_t hash = 0;
                            for (const auto& p: s)
                            {
                              hash = spot::wang32_hash(p);
                            }
                            return hash;
                          }
                        };
                        // set of states -> the forest of reachability in the states.
                        std::unordered_map<state_set, state_set, set_hash> set2scc;
                        // record the representative of every SCC
                        for(auto p = rank2n_.begin(); p != rank2n_.end(); p ++)
                        {
                              // std::cout << "state = " << get_name(p->first) << " number = " << p->second << ":\n";
                              // std::cout << "set = " << get_set_string(p->first.reach_set_) << "\n";
                              std::set<unsigned> set;
                              for(unsigned s : p->first.reach_set_)
                              {
                                set.insert(s);
                              }
                              auto val = set2scc.find(set);
                              if(val == set2scc.end())
                              {
                                // the set of macrostates in DPA
                                state_set v;
                                v.insert(p->second);
                                set2scc[set] = v;
                              }else 
                              {
                                val->second.insert(p->second);
                                set2scc[set] = val->second;
                              }
                        }
                        // output
                        bool debug = false;
                        unsigned num_reduced = 0;
                        for(auto p = set2scc.begin(); p != set2scc.end(); p ++)
                        {
                              if(p->second.size() <= 1)
                              {
                                continue;
                              }
                              if(debug)
                              {
                                std::cout << "state = {";
                                for(auto t : p->first)
                                {
                                  std::cout << " " << t ;
                                }
                                std::cout << "}: ";
                                
                                for(auto t : p->second)
                                {
                                  std::cout << " " << t << "(" << scc.scc_of(t) << ")";
                                }
                                std::cout << "\n";
                              }
                              // now compute states
                              std::vector<unsigned> reach_vec(scc.scc_count());
                              unsigned no_next_scc = scc.scc_count();
                              for(unsigned i = 0; i < scc.scc_count(); i ++)
                              {
                                // first set to non scc
                                reach_vec[i] = no_next_scc;
                              }
                              std::set<unsigned> not_bottom_set;
                              std::set<unsigned> bottom_set;
                              // traverse the number of states in p->second
                              std::unordered_map<unsigned, unsigned> scc2repr; 
                              for(auto s : p->second)
                              {
                                unsigned scc_s_idx = scc.scc_of(s);
                                bottom_set.insert(scc_s_idx);
                                auto val_state = scc2repr.find(scc_s_idx);
                                if(val_state == scc2repr.end())
                                {
                                  scc2repr[scc_s_idx] = s;
                                }else 
                                {
                                  // keep the smallest one
                                  scc2repr[scc_s_idx] = std::min(s, scc2repr[scc_s_idx]);
                                }
                              }
                              if(bottom_set.size() <= 1) 
                              {
                                continue;
                              }
                              for(auto fst_idx : bottom_set)
                              {
                                for(auto snd_idx : bottom_set)
                                {
                                  if(fst_idx == snd_idx) continue;
                                  if(scc_reach(fst_idx, snd_idx)) 
                                  {
                                    // std::cout << fst_idx<<  " can reach " << snd_idx << std::endl;
                                    // only record the smallest SCC that it can reach so far
                                    reach_vec[fst_idx] = std::min(snd_idx, reach_vec[fst_idx]);
                                    not_bottom_set.insert(fst_idx);
                                    continue;
                                  }
                                }
                              }
                              if(debug)
                              {
                                std::cout << "Bottom set: {" ;
                                for(auto s : bottom_set)
                                {
                                  if(not_bottom_set.find(s) == not_bottom_set.end())
                                  {
                                    std::cout << " " << s << " (state=" << scc2repr[s] << ")";
                                  }else 
                                  {
                                    std::cout << " " << s << "(next=" << reach_vec[s] <<") ";
                                  }
                                }
                                std::cout << "}\n";
                              }
                              
                              auto get_bottom_scc = [&reach_vec, &no_next_scc](unsigned scc_idx) -> unsigned
                              {
                                while(true)
                                {
                                  if(reach_vec[scc_idx] == no_next_scc)
                                  {
                                    break;
                                  }
                                  scc_idx = reach_vec[scc_idx];
                                }
                                return scc_idx;
                              };
                              for(auto t : p->second)
                              {
                                if(debug) std::cout << " " << t << "(" << scc.scc_of(t) << ")";
                                unsigned scc_idx = scc.scc_of(t);
                                unsigned bottom_scc_idx = get_bottom_scc(scc_idx);
                                if(bottom_scc_idx != scc_idx)
                                {
                                  if(debug) std::cout << "State " << t << " replaced by " << scc2repr[bottom_scc_idx] << std::endl;
                                  repr_states[t] = scc2repr[bottom_scc_idx];
                                  ++ num_reduced;
                                }
                              }
                        }
                        std::cout << "The number of states(colors) reduced by merging: " << num_reduced << "("<< num_colors_<< ") {out of " << aut->num_states() << "(" << num_colors_ << ")"<< "}"<< std::endl;
                        if(num_reduced == 0)
                        {
                          return aut;
                        }
                        // now construct new DPAs
                        spot::twa_graph_ptr post_aut = spot::make_twa_graph(aut->get_dict());
                        post_aut->copy_ap_of(aut);
                        post_aut->prop_copy(aut,
                            { false, // state based
                                false, // inherently_weak
                                false, false, // deterministic
                                true, // complete
                                false // stutter inv
                                });
                        // if(show_names_)
                        // {
                        //   post_aut->set_named_prop("state-names", names_);
                        // }
                        for(unsigned s = 0; s < num_states; s ++)
                        {
                          post_aut->new_state();
                        }
                        for (auto& t: aut->edges())
                        {
                          // out going transition for t.src
                          if(t.src == repr_states[t.src] && t.dst == repr_states[t.dst])
                          {
                            post_aut->new_edge(t.src, t.dst, t.cond, t.acc);
                          }else if(t.src == repr_states[t.src] && t.dst != repr_states[t.dst])
                          {
                            post_aut->new_edge(t.src, repr_states[t.dst], t.cond, t.acc);
                          }
                          // igonre the rest cases
                          //t.src != repr_states[t.src] && t.dst == repr_states[t.dst])
                          //t.src != repr_states[t.src] && t.dst != repr_states[t.dst])
                        }
                        post_aut->set_init_state(repr_states[aut->get_init_state_number()]);
                        // now acceptance condition
                        post_aut->set_acceptance(num_colors_, spot::acc_cond::acc_code::parity_min_even(num_colors_));
                        if (aut->prop_complete().is_true())
                          post_aut->prop_complete(true);
                        post_aut->prop_universal(true);
                        post_aut->prop_state_acc(false);
                        // remove unreachable macrostates
                        post_aut->purge_unreachable_states();
                        return post_aut;
                    }
          };


    spot::twa_graph_ptr
    determinize_tba(const spot::const_twa_graph_ptr& aut, bool show_names, optimizer &opt, bool use_scc, bool use_unambiguous, bool use_stutter)
    {
      if (!aut->acc().is_buchi())
            throw std::runtime_error
                    ("determinize_tba() requires a Buchi input");

      auto det = cola::tba_determinize(aut, show_names, opt, use_scc, use_unambiguous, use_stutter);
      return det.run();
    }
}