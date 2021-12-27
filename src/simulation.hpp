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

#include "cola.hpp"

#include <string>
#include <map>
#include <set>
#include <vector>

typedef std::vector<std::vector<bool>> bool_mat;
typedef std::vector<bdd> bdd_vec;
typedef std::vector<std::pair<unsigned, bool>> pair_vec;

struct pair_hash
  {
    size_t
    operator()(std::pair<unsigned, bool> p) const noexcept
    {
      return (p.first << 2) | (p.second ? 1 : 0);
    }
  };

namespace cola
{
    class delayed_simulation
    {
        private:
        const spot::const_twa_graph_ptr nba_;
        const spot::option_map& om_;

        // spoiler (player 0) and duplicator (player 1)
        // win_region_[p][q] == false iff p is simulated by q
        std::vector<std::vector<bool>> win_region_;

        // states to its index
        std::unordered_map<std::pair<unsigned, bool>, unsigned, pair_hash> s2index_;

        pair_vec states_;
        bdd_vec compact_;
        bdd_vec support_;

        // number of states of the form (q, b)
        // b = 1 or 0 if q has accepting incoming transitions
        // otherwise b = 0
        unsigned num_states_;
        // check whether p delayed-simulates q
        bool back_reach(unsigned p, unsigned q, bool_mat& avoid);
        void get_avoid_set(bool_mat &avoid);
        bool get_winning_set(bool_mat &avoid);
        // unsigned get_pair_index(pair_vec& states_vec, std::pair<unsigned, bool> pair);

        public:
        delayed_simulation(const spot::const_twa_graph_ptr nba, spot::option_map& om);

        // whether p simulates q or alternatively q is simulated by p
        bool simulate(unsigned p, unsigned q)
        {
            if (win_region_.size() == 0)
              return p == q;
            return !win_region_[q][p]; // q is simulated by p
        }

    };
}
