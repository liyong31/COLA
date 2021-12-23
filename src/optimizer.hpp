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
//#include <spot/twaalgos/sccinfo.hh>
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

  public:
    mstate_merger(spot::twa_graph_ptr &dpa, const mstate_equiv_map &equiv_map)
        : dpa_(dpa), equiv_map_(equiv_map)
    {
    }

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
    std::vector<std::vector<char>> implies_;
    // the SCC information of states
    spot::scc_info &si_;
    // reachability relation of SCCs by find SCC paths
    std::vector<char> is_connected_;

  public:
    state_simulator(const spot::const_twa_graph_ptr &nba, spot::scc_info &si, bool use_simulation = true);
    // do nothing constructor
    void output_simulation();
    //void output_reachability_relation();
    // state i reach state j
    char can_reach(unsigned i, unsigned j);
    // check whether state i simulates state j
    bool simulate(unsigned i, unsigned j);
  };
}
