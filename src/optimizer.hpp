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

#pragma once

#include "cola.hpp"

#include <set>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/isunamb.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/cycles.hh>
#include <spot/twaalgos/sccfilter.hh>

typedef unsigned state_t;
typedef std::set<state_t> state_set;

struct state_set_hash
{
  size_t
  operator()(const state_set &s) const noexcept
  {
    size_t hash = 0;
    for (const auto &p : s)
    {
      hash = spot::wang32_hash(p);
    }
    return hash;
  }
};

// put together the mstates with the same reachable states of input NBA
typedef std::unordered_map<state_set, state_set, state_set_hash> mstate_equiv_map;

namespace cola
{
  /// \brief Merge the macro states in the constructed DPA
  class mstate_merger
  {
  private:
    // the constructed DPA to be reduced
    spot::twa_graph_ptr &dpa_;
    // mstates that are identified with the same language
    // Item = (set of reachable states of NBA, the set of mstates with the set of reachable states).
    const mstate_equiv_map &equiv_map_;

    spot::option_map& om_;

    spot::scc_info& si_;

  public:
    mstate_merger(spot::twa_graph_ptr &dpa, const mstate_equiv_map &equiv_map, spot::scc_info& si, spot::option_map& om);

    spot::twa_graph_ptr
    run();
  };

  // compute the simulation relation of the states of the input NBA
  class state_simulator
  {
  private:
    // the constructed DPA to be reduced
    const spot::const_twa_graph_ptr &nba_;
    // language containment indicator
    //std::vector<std::vector<char>> implies_;
    std::vector<std::vector<bool>> is_implies_;
    // the SCC information of states
    spot::scc_info &si_;
    // reachability relation of SCCs by find SCC paths
    std::vector<bool> is_connected_;

  public:
    state_simulator(const spot::const_twa_graph_ptr &nba, spot::scc_info &si, std::vector<bdd>& implications, bool use_simulation = true);
    state_simulator(const state_simulator& other);
    // do nothing constructor
    void output_simulation();
    //void output_reachability_relation();
    // state i reach state j
    char can_reach(unsigned i, unsigned j);
    // check whether state i simulates state j
    bool simulate(unsigned i, unsigned j);
    char can_reach_scc(unsigned scc1, unsigned scc2);
  };

  // adaped from spot/twaalgos/powerset.cc
  class edge_strengther final: protected spot::enumerate_cycles
    {
    public:
      typedef enumerate_cycles::dfs_stack::const_iterator cycle_iter;
      typedef spot::twa_graph_edge_data trans;
      typedef std::set<trans*> edge_set;
      typedef std::vector<edge_set> set_set;
    protected:
      bool overlap_initialized;
      spot::const_twa_graph_ptr nba_;
    //   power_map& refmap_;
    //   edge_set reject_;         // set of rejecting edges
    //   set_set accept_;          // set of cycles that are accepting
    //   edge_set all_;            // all non rejecting edges
      edge_set overlap_;      // set of edges that oppear in every cycle in an SCC
      unsigned threshold_;      // maximum count of enumerated cycles
      unsigned cycles_left_;    // count of cycles left to explore
    public:
      edge_strengther(spot::const_twa_graph_ptr nba, const spot::scc_info& si, unsigned threshold);

      // fixed an SCC to explore
      bool fix_scc(const unsigned m);

      bool is_cycle_accepting(cycle_iter begin, edge_set& ts) const;
      // override the function;
      virtual bool
      cycle_found(unsigned start) override
      {
        // from start
        cycle_iter i = dfs_.begin();
        while (i->s != start)
          ++i;
        // found start, transition considered for the cycle.
        edge_set ts;
        bool is_acc = is_cycle_accepting(i, ts);
        do
          ++i;
        while (i != dfs_.end());
        // pop out the dfs?
        if (is_acc)
          {
            // add all edges in accepting cycle
            if (! overlap_initialized)
            {
                overlap_.insert(ts.begin(), ts.end());
                overlap_initialized = true;
            }
            if (overlap_initialized)
            {
                edge_set common;
                std::set_intersection(ts.begin(), ts.end(),
                          overlap_.begin(), overlap_.end(),
                          std::inserter(common, common.begin()));
                overlap_ = common;
            }
          }
        // if no edge will be used by every accepting cycle
        // no need to explore further
        if (overlap_initialized && overlap_.empty())
        {
            cycles_left_ = 1;
        }
        // Abort this algorithm if we have seen too many cycles, i.e.,
        // when cycle_left_ *reaches* 0.  (If cycle_left_ == 0, that
        // means we had no limit.)
        return (cycles_left_ == 0) || --cycles_left_;
      }


    };
}
