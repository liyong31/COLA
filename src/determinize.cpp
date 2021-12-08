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
// determinization
        std::unordered_map<int, int> labelIndex;
        class determinization_rabin
        {
        private:
            // The source automaton.
            const spot::const_twa_graph_ptr aut_;

            // SCCs information of the source automaton.
            spot::scc_info si_;

            // Number of states in the input automaton.
            int n_states_;

            // Number of states in Q_D
            int d_states_ = 1;
            int rabin = 0;

            // The complement being built.
            spot::twa_graph_ptr res_;

            // Association between NCSB states and state numbers of the
            // complement.
            std::unordered_map<small_dstate, int, small_dstate_hash> rabin2n_;

            // States to process.
            std::deque<std::pair<dstate, int>> todo_;

            // Support for each state of the source automaton.
            std::vector<bdd> support_;

            // Propositions compatible with all transitions of a state.
            std::vector<bdd> compat_;

            // Whether a SCC is deterministic or not
            std::vector<bool> is_deter_;

            // Whether a state only has accepting transitions
            std::vector<bool> is_accepting_;

            // State names for graphviz display
            std::vector<std::string>* names_;

            // Show NCSB states in state name to help debug
            bool show_names_;

            std::string
            get_name(const small_dstate& ms)
            {
              std::string res = "{";

              // N
              bool first_state = true;
              for (const auto& p: ms)
              {
                if (p.second == detrb_n)
                {
                  if (!first_state)
                    res += ",";
                  first_state = false;
                  res += ("N:" + std::to_string(p.first));
                }
              }

              res += "},{";
              
              // (state, bottom)
              first_state = true;
              for (const auto& p: ms)
              {
                if (p.second == detrb_bot)
                {
                  if (!first_state)
                    res += ",";
                  first_state = false;
                  res += ("(" + std::to_string(p.first) + ", bot)");
                }

                // (state, label)
                // first_state = true;
                if (p.second >= detrb_d)
                {
                  if (!first_state)
                    res += ",";
                  first_state = false;
                  res += ("(" + std::to_string(p.first) + ", " + std::to_string(p.second) + " )");
                }
              }

              return res + "}";
            }

            small_dstate
            to_small_dstate(const dstate& ms)
            {
              int count = 0;
              for (int i = 0; i < n_states_; ++i)
                count += (ms[i] != detrb_m);
              small_dstate small;
              small.reserve(count);
              for (int i = 0; i < n_states_; ++i)
                if (ms[i] != detrb_m)
                  small.emplace_back(i, ms[i]);
              return small;
            }

            // looks for a duplicate in the map before
            // creating a new state if needed.
            int
            new_state(dstate&& s)
            {
              auto p = rabin2n_.emplace(to_small_dstate(s), 0);
              if (p.second) // This is a new state
              {
                p.first->second = res_->new_state();
                if (show_names_)
                  names_->push_back(get_name(p.first->first));
                todo_.emplace_back(std::move(s), p.first->second);
              }
              return p.first->second;
            }

            void
            rabin_successors(dstate&& ms, int origin, bdd letter)
            {
              dstate succ(n_states_, detrb_m);
                  
              // At first, all states in Q_D is set to bottom
              for (int i = 0; i < n_states_; ++i)
              {
                // i is in Q_D
                if (is_deter_[si_.scc_of(i)])
                {
                  succ[i] = detrb_bot;
                }
              }

              int minLabel = INT32_MAX;
              for (int i = 0; i < n_states_; ++i)
              {
                if (ms[i] < detrb_d)
                  continue;
                
                if (ms[i] < minLabel)
                {
                  minLabel = ms[i];
                }
              }

              int jumpLabel = 0;
              for (int i = 1; i <= d_states_; i++)
              {
                // find the min label that does not appear in ms
                if (std::find(ms.begin(), ms.end(), i) == ms.end())
                {
                  jumpLabel = i;
                  break;
                }
              }

              // Handle \delta_D(\alpha(g), a)
              
              for (int i = 0; i < n_states_; ++i)
              {
                if (ms[i] < detrb_d)
                  continue;
                
                if (!labelIndex.count(ms[i]))
                {
                  int tmp = labelIndex.size() + 1;
                  labelIndex.emplace(ms[i], tmp);
                }
              
                for (const auto &t: aut_->out(i))
                {
                  if (!bdd_implies(letter, t.cond))
                    continue;

                  // only one successor
                  succ[t.dst] = minLabel;     
                  break;
                }
              }
            
              // Handle N states.
              for (int i = 0; i < n_states_; ++i)
              {
                if (ms[i] != detrb_n)
                  continue;
                for (const auto &t: aut_->out(i))
                {
                  if (!bdd_implies(letter, t.cond))
                    continue;

                  // t.dst is in Q_D
                  if (is_deter_[si_.scc_of(t.dst)])
                  {
                    // if g(t.dst) >= detrb_d, 
                    // means it has been given a label, 
                    // and means it is a successor of some state in Q_D,
                    // then we should skip it,
                    // and only consider the situation that g(t.dst) < detrb_d
                    if (succ[t.dst] < detrb_d)
                    {
                      succ[t.dst] = jumpLabel;
                      if (!labelIndex.count(succ[t.dst]))
                      {
                        int tmp = labelIndex.size() + 1;
                        labelIndex.emplace(succ[t.dst], tmp);
                      }
                    }
                  } 
                  else
                  {
                    succ[t.dst] = detrb_n;
                  }
                }
              }
             
              // accepting state
              // Ri = {(N,g) | i \notin beta(g)
              // Ai = {(N,g) | i \in g(F)}
              // `(Fin(0)&Inf(1))|(Fin(2)&Inf(3))|...|(Fin(2n-2)&Inf(2n-1))`

              dstate succBackup(n_states_, detrb_m);
              for (int i = 0; i < n_states_; ++i)
              {
                succBackup[i] = succ[i];
              }
             
              int dst = new_state(std::move(succ)); 
              int flag = false;

              for (int i = 0; i < n_states_; ++i)
              {
                if (ms[i] < detrb_d)
                  continue;
              
                for (const auto &t: aut_->out(i))
                {
                  if (!bdd_implies(letter, t.cond))
                    continue;

                  // only one successor
                  if (t.acc || is_accepting_[t.dst])
                  {
                    if (ms[i] == succBackup[t.dst])
                    {
                      res_->new_edge(origin, dst, letter, {(unsigned) 2 * labelIndex[ms[i]] - 1});
                      res_->merge_edges();
                      flag = true; 
                    }
                    break;
                  }
                 
                }
              }

              int init = true;

              for (int i = 0; i < n_states_; ++i)
              {
                if (ms[i] < detrb_d)
                  continue;
                init = false;
                for (const auto &t: aut_->out(i))
                {
                  if (!bdd_implies(letter, t.cond))
                    continue;
                  if (succBackup[t.dst] != ms[i])
                  {
                    res_->new_edge(origin, dst, letter, {(unsigned) 2 * labelIndex[ms[i]] - 2});
                    res_->merge_edges();
                    flag = true;
                  } 
                }
                
              }
              if (init == true)
              {
                for (int i = 0; i < n_states_; i++)
                {
                  if (succBackup[i] < detrb_d)
                    continue;
                  res_->new_edge(origin, dst, letter, {(unsigned) 2 * (labelIndex[succBackup[i]] - 1)});
                  res_->merge_edges();
                  flag = true; 
                }
              }
              
              if (flag == false)
              {
                res_->new_edge(origin, dst, letter);
              }
              
            }


        public:
            determinization_rabin(const spot::const_twa_graph_ptr& aut, bool show_names)
                    : aut_(aut),
                      si_(aut),
                      n_states_(aut->num_states()),
                      support_(n_states_),
                      compat_(n_states_),
                      is_accepting_(n_states_),
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
              for (int i = 0; i < n_states_; ++i)
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
                is_accepting_[i] = accepting && has_transitions;
              }

              // Compute which SCCs are part of the deterministic set.
              is_deter_ = spot::semidet_sccs(si_);

              if (show_names_)
              {
                names_ = new std::vector<std::string>();
                res_->set_named_prop("state-names", names_);
              }

              // Because we only handle one initial state, we assume it
              // belongs to the N set. (otherwise the automaton would be
              // deterministic)
              int init_state = aut->get_init_state_number();
              dstate new_init_state(n_states_, detrb_m);
              new_init_state[init_state] = detrb_n;
              for (int i = 0; i < n_states_; ++i)
              {
                if (is_deter_[si_.scc_of(i)])
                {
                  d_states_++;
                  new_init_state[i] = detrb_bot;
                }
              }

              res_->set_init_state(new_state(std::move(new_init_state)));
            }

            spot::twa_graph_ptr
            run()
            {
              // Main stuff happens here

              while (!todo_.empty())
              {
                auto top = todo_.front();
                todo_.pop_front();

                dstate ms = top.first;

                // Compute support of all available states.
                bdd msupport = bddtrue;
                bdd n_s_compat = bddfalse;
                
                for (int i = 0; i < n_states_; ++i)
                  if (ms[i] != detrb_m)
                  {
                    msupport &= support_[i];   
                    if (ms[i] != detrb_m || is_accepting_[i])             
                      n_s_compat |= compat_[i];
                  }

                bdd all;
                all = n_s_compat;
                
                while (all != bddfalse)
                {
                  bdd one = bdd_satoneset(all, msupport, bddfalse);
                  all -= one;

                  // Compute all new states available from the generated letter.
                  rabin_successors(std::move(ms), top.second, one);
                }
              }
              
              int tmpMax = labelIndex.size();
            
              res_->set_acceptance(2 * tmpMax, spot::acc_cond::acc_code::rabin(tmpMax));
             
              res_->prop_state_acc(false);
              res_->merge_edges();
              return res_;
            }
        };

          const int RANK_N = -1; // nondeterministic
          const int RANK_M = -2; // missing value

          // states
          typedef std::vector<int> mstate;
          typedef std::pair<unsigned, int> label;
          // state and labelling pairs
          typedef std::vector<label> small_mstate;

          struct small_mstate_hash
          {
            size_t
            operator()(small_mstate s) const noexcept
            {
              size_t hash = 0;
              for (const auto& p: s)
              {
                hash = spot::wang32_hash(hash ^ ((p.first<<2) | p.second));
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
              spot::scc_info si_;

              optimizer opt_;

              // Number of states in the input automaton.
              unsigned nb_states_;

              // unsigned nb_det_states_;

              // The parity automata being built.
              spot::twa_graph_ptr res_;

              // the number of indices
              unsigned sets_ = 0;

              // use ambiguous
              bool use_unambiguous_;
              
              // use stutter
              bool use_stutter_;

              // Association between labelling states and state numbers of the
              // DPA.
              std::unordered_map<small_mstate, unsigned, small_mstate_hash> rank2n_;

              // bisimulate map
              std::unordered_map<small_mstate, std::set<mstate>, small_mstate_hash> bisim2n_;

              // States to process.
              std::deque<std::pair<mstate, unsigned>> todo_;

              // Support for each state of the source automaton.
              std::vector<bdd> support_;

              // Propositions compatible with all transitions of a state.
              std::vector<bdd> compat_;

              // Whether a SCC is deterministic or not
              std::vector<bool> is_deter_;

              // Whether a state only has accepting transitions
              std::vector<bool> is_accepting_;

              // State names for graphviz display
              std::vector<std::string>* names_;

              // Show Rank states in state name to help debug
              bool show_names_;

              int get_max_rank(const mstate& ms) 
              {
                int max_rnk = -2;
                for(int i = 0; i < nb_states_; i ++) 
                {
                  if(ms[i] == RANK_M) 
                    continue;
                  if(max_rnk < ms[i]) 
                  {
                    max_rnk = ms[i];
                  }
                }
                return max_rnk;
              }

              std::string
              get_name(const small_mstate& ms)
              {
                int max_rnk = -2;
                for(const auto & p : ms) 
                {
                  if(p.second > max_rnk) 
                  {
                    max_rnk = p.second;
                  }
                }
          
                std::string res = "{";

                bool first_state = true;
                  for (const auto& p: ms)
                  if (p.second == RANK_N)
                  {
                      if (!first_state)
                        res += ",";
                      first_state = false;
                      res += std::to_string(p.first);
                  }

                  res += "}";
                  for(int i = 0; i <= max_rnk; i ++) 
                  {
                    res += ",[";
                    first_state = true;
                    for (const auto& p: ms)
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
                    to_small_mstate(const mstate& ms)
                    {
                      unsigned count = 0;
                      for (unsigned i = 0; i < nb_states_; ++i)
                        count+= (ms[i] != RANK_M);
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
                      operator() (const label& lhs,
                                  const label& rhs) const
                      {
                        if( lhs.second < rhs.second)
                        {
                          return true;
                        }else if(lhs.second > rhs.second) 
                        {
                          return false;
                        }else 
                        {
                          return lhs.first < rhs.second;
                        }
                      }
                    };
                    small_mstate
                    to_bisim_small_mstate(const mstate& ms)
                    {
                        small_mstate sm = to_small_mstate(ms);
                        std::sort(sm.begin(), sm.end(), compare_pair());
                        // output sorted pairs
                        int count = 1;
                        small_mstate res;
                        res.reserve(sm.size());
                        for(label p : sm)
                        {
                          // std::cout << "(" << p.first << ", " << p.second << ") ";
                          if(p.second == RANK_N)
                          {
                            res.emplace_back(p.first, p.second);
                          }else 
                          {
                            res.emplace_back(p.first, count);
                            count ++;
                          }
                        }
                        // std::cout << "\nSorted Unique:\n";
                        // for(label p : res)
                        // {
                        //   std::cout << "( " << p.first << ", " << p.second << ") ";
                        // }
                        // std::cout << "\n";
                        return res;
                    }

                    // From a Rank state, looks for a duplicate in the map before
                    // creating a new state if needed.
                    unsigned
                    new_state(mstate&& s)
                    {
                      //small_mstate repr = to_bisim_small_mstate(s);
                      //auto p = rank2n_.emplace(repr, 0);
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

                    unsigned 
                    new_bisim_state(mstate& ms)
                    {
                      small_mstate res = to_bisim_small_mstate(ms);
                      auto p = bisim2n_.find(res);
                      if(p == bisim2n_.end())
                      {
                        std::set<mstate> mset;
                        mset.insert(ms);
                        bisim2n_[res] = mset;
                      }else 
                      {
                        p->second.insert(ms);
                      }
                      return 0;
                    }

                    bool exists(mstate& s)
                    {
                      return rank2n_.end() == rank2n_.find(to_small_mstate(s));
                    }

                    bool
                    is_smaller(const mstate& fst, const mstate& snd)
                    {                    
                      for(unsigned s = 0; s < nb_states_; s ++)
                      {
                        if(fst[s] == snd[s]) continue;
                        else if(fst[s] < snd[s]) return true;
                        else if(fst[s] > snd[s]) return false;
                      }
                      return false;
                    }


                    // remove a state i if it is simulated by a state j
                    void 
                    merge_redundant_states(mstate& ms)
                    {
                      for(unsigned i = 0; i < nb_states_; i ++)
                      {
                        for(unsigned j = 0; j < nb_states_; j ++)
                        {
                          // if j is not reached at this level
                          if(i == j || ms[j] == RANK_M || ms[i] == RANK_M) continue;
                          //std::cout << "start simulated" << std::endl;
                          // j simulates i and j cannot reach i
                          if(opt_.simulate(j, i) && opt_.reach(j, i) == 0) 
                          {
                            // std::cout << "simulated" << std::endl;
                            ms[i] = RANK_M;
                          }
                          // (j, k1) and (i, k2), if j simulates i and k1 <= k2, then remove k2
                          if(opt_.simulate(j, i) && ms[j] > RANK_N && ms[j] <= ms[i] )
                          {
                            ms[i] = RANK_M;
                          } 
                        }
                      }
                    }

                    void
                    make_compact_ranking(mstate& ms)
                    {
                      int max_rnk = get_max_rank(ms);
                      // now reorgnize the indices
                      std::unordered_map<int, int> ord_func;
                      int index = 0;
                      // the succ has at most max_rnk + 1
                      for(int i = 0; i <= max_rnk + 1; i ++)
                      {
                        bool existing = false;
                        for (unsigned s = 0; s < nb_states_; ++s)
                        {
                          if(ms[s] == i)
                          {
                            existing = true;
                            break;
                          }
                        }
                        if(existing) 
                        {
                          ord_func.emplace(i, index);
                          index ++;
                        }
                      }
                      for(unsigned s = 0; s < nb_states_; s ++)
                      {
                        if(ms[s] != RANK_M && ms[s] != RANK_N)
                        {
                          // update indices
                          ms[s] = ord_func[ms[s]];
                        }
                      }

                    }

                    void
                    rank_successors(const mstate& ms, unsigned origin, bdd letter, mstate& nxt, int& color)
                    {
                      mstate succ(nb_states_, RANK_M);
                      int max_rnk = get_max_rank(ms);
                      std::vector<bool> incoming(nb_states_, false);
                      std::vector<bool> ignores(nb_states_, false);
                      // first handle nondeterministic states
                      std::vector<unsigned> coming_states;
                      for (unsigned s = 0; s < nb_states_; ++ s)
                      {
                        // missing states
                        if (ms[s] == RANK_M)
                          continue;
                        // nondeterministic states
                        if (ms[s] == RANK_N)
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
                            // BETTER: transition when seeing deterministic states
                            if (is_deter_[si_.scc_of(t.dst)])
                            // only transition to labelling if seeing accepting transitions or states
                            //if(t.acc || is_accepting_[t.dst])
                            {
                              if(succ[t.dst] < RANK_N) 
                              {
                                coming_states.push_back(t.dst);
                                succ[t.dst] = max_rnk + 1; //Sharing labels 
                                //succ[t.dst] = ++ max_rnk;  
                              }
                            } else 
                            {
                              succ[t.dst] = RANK_N;
                            }
                          }
                        }
                      }
                      // give labelling to coming_states
                      std::sort(coming_states.begin(), coming_states.end());
                      for(unsigned s : coming_states)
                      {
                        // std::cout << " " << s;
                        succ[s] = ++max_rnk;
                      }
                      // std::cout << "\n";
                      // now we compute the rank successors
                      for(int rnk = max_rnk; rnk >= 0; rnk --)
                      {
                        for (unsigned s = 0; s < nb_states_; ++s)
                        {
                          if (ms[s] == RANK_M || ms[s] == RANK_N)
                            continue;
                          if (ms[s] != rnk)
                            continue;
                          for (const auto &t: aut_->out(s))
                          {
                            if (!bdd_implies(letter, t.cond))
                              continue;
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
                              continue;
                            }
                            succ[t.dst] = rnk;
                          }
                        }
                      }
                      // remove redudant states
                      merge_redundant_states(succ);
                      // now compute min_dcc (minimal index disappeared) and min_acc (minimal index accepted)
                      const int MAX_PRI = nb_states_ + 2;
                      int min_dcc = MAX_PRI;
                      int min_acc = MAX_PRI;
                      for(int rnk = max_rnk; rnk >= 0; rnk --)
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
                          for (const auto &t: aut_->out(s))
                          {
                            if (!bdd_implies(letter, t.cond))
                              continue;
                            // exactly the same rank means the existence of an edge from the parent s
                            if(succ[t.dst] == rnk)
                            {
                              has_succ = true;
                              has_acc = has_acc || t.acc;
                            }
                          }
                        }
                        if(! has_succ)
                        {
                          min_dcc = rnk;
                        }else if(has_acc)
                        {
                          min_acc = rnk;
                        }
                      }

                      int parity;
                      if(min_dcc == MAX_PRI && min_acc != MAX_PRI) 
                      {
                        parity = 2 * (min_acc + 1);
                      }else if(min_dcc != MAX_PRI && min_acc == MAX_PRI)
                      {
                        parity = 2 * min_dcc + 1;
                      }else if(min_dcc != MAX_PRI && min_acc != MAX_PRI) 
                      {
                        parity = std::min(2* min_dcc + 1, 2 * min_acc + 2);
                      }else {
                        parity = -1;
                      }
                      // now reorgnize the indices
                      std::unordered_map<int, int> ord_func;
                      int index = 0;
                      // the succ has at most max_rnk + 1
                      for(int i = 0; i <= max_rnk + 1; i ++)
                      {
                        bool existing = false;
                        for (unsigned s = 0; s < nb_states_; ++s)
                        {
                          if(succ[s] == i)
                          {
                            existing = true;
                            break;
                          }
                        }
                        if(existing) 
                        {
                          ord_func.emplace(i, index);
                          index ++;
                        }
                      }
                      for(unsigned s = 0; s < nb_states_; s ++)
                      {
                        if(succ[s] != RANK_M && succ[s] != RANK_N)
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
                get_stutter_state(const mstate& curr, unsigned origin, bdd letter, mstate& succ, int& color)
                {
                  mstate ms(nb_states_, RANK_M);
                  for(unsigned s = 0; s < nb_states_; s ++)
                  {
                    ms[s] = curr[s];
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
                                && is_smaller(*it, *cycle_seed))
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
                    rank_successors(ms, origin, letter, succ, color);
                  }

                }

                public:
                  ldba_determinize(const spot::const_twa_graph_ptr& aut, bool show_names, optimizer& opt, bool use_unambiguous, bool use_stutter)
                            : aut_(aut),
                              opt_(opt),
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
                      // std::cout << "Output simulation" << std::endl;
                      // opt_.output_simulation();
                      // std::cout << "End output" << " NumS " << nb_states_ << std::endl;
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
                        is_accepting_[i] = accepting && has_transitions;
                      }
                      // std::cout << "now deterministic part: " << std::endl;
                      // Compute which SCCs are part of the deterministic set.
                      is_deter_ = spot::semidet_sccs(si_);
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
                          //rank_successors(std::move(ms), top.second, letter, succ, color);
                          get_stutter_state(std::move(ms), top.second, letter, succ, color);
                          
                          unsigned origin = top.second;
                          // add transitions
                          // Create the automaton states
                          unsigned dst = new_state(std::move(succ));
                          // const unsigned MAX_PRI = 2* nb_det_states_ + 1;
                          if(color >= 0) 
                          {
                            unsigned pri = (unsigned)color;
                            sets_ = std::max(pri, sets_);
                          
                            res_->new_edge(origin, dst, letter, {pri});
                          }else 
                          {
                            res_->new_edge(origin, dst, letter);
                          }
                        }
                      }
                      // // now I output states
                      // for(auto p = bisim2n_.begin(); p != bisim2n_.end(); p ++)
                      // {
                      //   std::cout << "bisim repr = " << get_name(p->first) << ":\n";
                      //   for(auto ms : p->second)
                      //   {
                      //     std::cout << get_name(to_small_mstate(ms)) << " ";
                      //   }
                      //   std::cout << "\n";
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
                      unsigned num_sets = max_odd_pri + 1;
                     
                      res_->set_acceptance(num_sets, spot::acc_cond::acc_code::parity_min_even(num_sets));
                      if (aut_->prop_complete().is_true())
                        res_->prop_complete(true);
                      res_->prop_universal(true);
                      res_->prop_state_acc(false);

                      cleanup_parity_here(res_);
                      
                      return res_;
                    }
          };

        // determinization
    spot::twa_graph_ptr
    determinize_rabin(const spot::const_twa_graph_ptr& aut, bool show_names)
    {
      if (!is_semi_deterministic(aut))
        throw std::runtime_error
                ("determinize_rabin() requires a semi-deterministic input");
      
      auto rabin = determinization_rabin(aut, show_names);
      return rabin.run();
    }

    spot::twa_graph_ptr
    determinize_tldba(const spot::const_twa_graph_ptr& aut, bool show_names, optimizer &opt, bool use_unambiguous, bool use_stutter)
    {
      if (!is_semi_deterministic(aut))
            throw std::runtime_error
                    ("determinize_tldba() requires a semi-deterministic input");

      auto det = cola::ldba_determinize(aut, show_names, opt, use_unambiguous, use_stutter);
      return det.run();
    }
}