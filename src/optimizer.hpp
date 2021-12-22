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

#include <set>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/isunamb.hh>
#include <spot/twaalgos/hoa.hh>
//#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/sccfilter.hh>

class optimizer
{
private:
    const spot::twa_graph_ptr aut_;
    // Simplifications options
    std::vector<std::vector<char>> implies_;
    // is connected
    std::vector<std::vector<char>> is_connected_;
    // representative for every state
    std::vector<unsigned> repr_;
    //spot::scc_info scc_;
    std::vector<bdd> support_;

public:
    optimizer(const spot::twa_graph_ptr aut, bool use_simulation, bool use_stutter);
    optimizer(optimizer &other);

    void output_simulation()
    {
        for (int i = 0; i < implies_.size(); i++)
        {
            for (int j = 0; j < implies_[i].size(); j++)
            {
                if (i == j)
                    continue;
                // j contains the language of i
                std::cout << j << " simulates " << i << " : " << (unsigned)(implies_[i][j]) << " " << simulate(j, i) << std::endl;
            }
        }
    }

    void output_reach()
    {
        for (int i = 0; i < is_connected_.size(); i++)
        {
            for (int j = 0; j < is_connected_[i].size(); j++)
            {
                if (i == j)
                    continue;
                std::cout << j << " reaches " << i << " : " << (unsigned)(is_connected_[i][j]) << " " << reach(j, i) << std::endl;
            }
        }
    }

    void output_repr()
    {
        for (unsigned i = 0; i < aut_->num_states(); i++)
        {
            std::cout << i << " repr " << repr_[i] << std::endl;
        }
    }

    unsigned get_repr(unsigned s)
    {
        return repr_[s];
    }

    // state i reach state j
    char reach(unsigned i, unsigned j)
    {
        if (i == j)
            return true;
        if (j < is_connected_.size() && i < is_connected_[j].size())
        {
            // j is reachable from i
            return is_connected_[j][i];
        }
        else
        {
            return 2;
        }
    }

    // check whether state i simulates state j
    bool simulate(unsigned i, unsigned j)
    {
        if (i == j)
            return true;
        if (j < implies_.size() && i < implies_[j].size())
        {
            return implies_[j][i] > 0;
        }
        else
        {
            return false;
        }
    }
};
