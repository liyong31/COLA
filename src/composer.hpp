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


#include <spot/twaalgos/hoa.hh>
#include <spot/misc/optionmap.hh>

namespace cola
{
    class composer
    {  
        private:
        std::vector<spot::twa_graph_ptr>& dpas_;
        spot::option_map& om_;

        public:
        composer(std::vector<spot::twa_graph_ptr>& dpas, spot::option_map& om)
        : dpas_(dpas), om_(om)
        {

        }

        spot::twa_graph_ptr
        run();

    };
}