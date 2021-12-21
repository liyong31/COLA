// Copyright (c) 2017-2020  The Seminator Authors
// Copyright (c) 2021  The COLA Authors
//
// This file is a part of COLA, a tool for determinization
// of omega automata.
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

#include <seminator.hpp>

#include <cutdet.hpp>
#include <bscc.hpp>
#include <breakpoint_twa.hpp>

#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/isweakscc.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/misc/optionmap.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twa/bddprint.hh>

namespace cola
{
    bool
    is_elevator_tba(const spot::const_twa_graph_ptr& aut)
    {
        spot::scc_info si(aut);
        unsigned nc = si.scc_count();
        for (unsigned scc = 0; scc < nc; ++scc)
        {
            if(is_deterministic_scc(scc, si) || spot::is_inherently_weak_scc(si, scc))
                continue;
            return false;
        }
        return true;
    }
}