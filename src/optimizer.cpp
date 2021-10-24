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

#include <spot/twaalgos/simulation.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/isunamb.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/sccfilter.hh>

optimizer::optimizer(optimizer& other)
: aut_(other.aut_)
{
  this->implies_ = other.implies_;
  this->support_ = other.support_;
}

optimizer::optimizer(spot::twa_graph_ptr aut, bool use_simulation, bool use_stutter)
        : aut_(aut)
        {

            if(use_simulation) 
            {

                      //std::cout << "output simulation" << std::endl;
                      std::vector<bdd> implications;
                      auto aut_tmp = spot::scc_filter(aut);
                      auto aut2 = simulation(aut_tmp, &implications);
                      aut = aut2;
                      // now compute 
                      spot::scc_info_options scc_opt = spot::scc_info_options::TRACK_SUCCS;
                      // We do need to track states in SCC for stutter invariance (see below how
                      // supports are computed in this case)
                      if (use_stutter && aut->prop_stutter_invariant())
                        scc_opt = spot::scc_info_options::TRACK_SUCCS | spot::scc_info_options::TRACK_STATES;
                     spot::scc_info scc = spot::scc_info(aut, scc_opt);
                     
                     // copied to optimizer
                     //scc_ = scc;
                      // If use_simulation is false, implications is empty, so nothing is built
                      std::vector<std::vector<char>> implies(
                          implications.size(),
                          std::vector<char>(implications.size(), 0));
                      {
                        std::vector<char> is_connected = find_scc_paths(scc);
                        unsigned sccs = scc.scc_count();
                        std::vector<std::vector<char>> reach_sccs(aut_->num_states(), std::vector<char> (aut_->num_states(), 2));
                        is_connected_ = reach_sccs;
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
                            if (!scc.reachable_state(i))
                              continue;
                            unsigned scc_of_i = scc.scc_of(i);
                            bool i_implies_something = false;
                            for (unsigned j = 0; j != implications.size(); ++j)
                              {
                                //reachable states
                                if (!scc.reachable_state(j))
                                  continue;
                                // SCC i is reachable from SCC j
                                is_connected_[i][j] = is_connected[sccs * scc.scc_of(j) + scc_of_i];
                                // j simulates i and j cannot reach i
                                bool i_implies_j = //!is_connected[sccs * scc.scc_of(j) + scc_of_i] && 
                                  bdd_implies(implications[i], implications[j]);
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
                            use_simulation = false;
                          }
                      }
                      // store simulation relation
                      implies_ = implies;

                      // Compute the support of each state
                      std::vector<bdd> support(aut->num_states());
                      if (use_stutter && aut->prop_stutter_invariant())
                        {
                          // FIXME this could be improved
                          // supports of states should account for possible stuttering if we plan
                          // to use stuttering invariance
                          for (unsigned c = 0; c != scc.scc_count(); ++c)
                            {
                              bdd c_supp = scc.scc_ap_support(c);
                              for (const auto& su: scc.succ(c))
                                c_supp &= support[scc.one_state_of(su)];
                              for (unsigned st: scc.states_of(c))
                                support[st] = c_supp;
                            }
                        }
                      else
                        {
                          for (unsigned i = 0; i != aut->num_states(); ++i)
                            {
                              bdd res = bddtrue;
                              for (const auto& e : aut->out(i))
                                res &= bdd_support(e.cond);
                              support[i] = res;
                            }
                        }
                    support_ = support;
            }else 
            {
                 std::vector<std::vector<char>> implies(
                          1,
                          std::vector<char>(0, 0));
                implies_ = implies;
                std::vector<std::vector<char>> is_connected(1, std::vector<char>(0, 0));
                is_connected_ = is_connected;
            }           

        }

std::vector<char>
        optimizer::find_scc_paths(const spot::scc_info& scc)
    {
        unsigned scccount = scc.scc_count();
        std::vector<char> res(scccount * scccount, 0);
        for (unsigned i = 0; i != scccount; ++i)
            res[i + scccount * i] = 1;
        for (unsigned i = 0; i != scccount; ++i)
        {
            unsigned ibase = i * scccount;
            for (unsigned d: scc.succ(i))
            {
                // we necessarily have d < i because of the way SCCs are
                // numbered, so we can build the transitive closure by
                // just ORing any SCC reachable from d.
                unsigned dbase = d * scccount;
                for (unsigned j = 0; j != scccount; ++j)
                res[ibase + j] |= res[dbase + j];
            }
        }
        return res;
    }

