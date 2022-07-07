// Copyright (C) 2022  The COLA Authors
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

#include "cola.hpp"

#include <functional>
#include <set>

#include <spot/misc/optionmap.hh>
#include <spot/twaalgos/hoa.hh>

namespace cola {
class decomposer {
private:
  // the NBA to be decomposed
  spot::twa_graph_ptr &nba_;
  // mstates that are identified with the same language
  spot::option_map &om_;

  int num_nbas_;

  spot::twa_graph_ptr make_twa_with_scc(spot::scc_info &si,
                                        std::set<unsigned> sccs,
                                        std::vector<bool> &reach_sccs);

public:
  decomposer(spot::twa_graph_ptr &nba, spot::option_map &om)
      : nba_(nba), om_(om) {
    num_nbas_ = om.get(NUM_NBA_DECOMPOSED);
  }

  std::vector<spot::twa_graph_ptr> run();
};
} // namespace cola