
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

#include "composer.hpp"

#include <set>
#include <vector>
#include <functional>
#include <queue>

#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/dualize.hh>

namespace cola
{
    spot::twa_graph_ptr
    composer::run()
    {
        struct aut_compare
        {
        // reverse order
            bool operator()( spot::twa_graph_ptr aut1,  spot::twa_graph_ptr aut2) const
            {
                return aut1->num_states() >= aut2->num_states();
            }
        };
        // smaller number first
        std::priority_queue<spot::twa_graph_ptr, std::vector<spot::twa_graph_ptr>, aut_compare> autlist;
        for (auto& aut : dpas_)
        {
            spot::twa_graph_ptr tmp = spot::dualize(aut);
            spot::postprocessor p;
            // p.set_pref(spot::postprocessor::Rabin);
            p.set_pref(spot::postprocessor::Deterministic);
            p.set_pref(spot::postprocessor::Parity);
            tmp = p.run(tmp);
            autlist.push(tmp);
        }
        while(autlist.size() > 1)
        {
            auto aut1 = autlist.top();
            autlist.pop();
            auto aut2 = autlist.top();
            autlist.pop();

            if (om_.get(VERBOSE_LEVEL) >= 2)
            {
                std::cout << "#FstOp = " << aut1->num_states() << " #SndOp = " << aut1->num_states()
                    << std::endl;
            }

            spot::twa_graph_ptr res = spot::product(aut1, aut2);
            if (om_.get(VERBOSE_LEVEL) >= 2)
            {
                std::cout << "#Product = " << res->num_states() << std::endl;
            }
            // postprocessing
            spot::postprocessor p;
            // p.set_pref(spot::postprocessor::Rabin);
            p.set_pref(spot::postprocessor::Parity);
            p.set_pref(spot::postprocessor::Deterministic);
            p.set_pref(spot::postprocessor::Small);
            res = p.run(res);
            autlist.push(res);
            if (om_.get(VERBOSE_LEVEL) >= 2)
            {
                std::cout << "#Post-Product = " << res->num_states() << " #Q = " << autlist.size() << std::endl;
            }
        }
        spot::twa_graph_ptr res = autlist.top();
        res = spot::dualize(res);
        // output_file(res, "final.hoa");
        // spot::postprocessor p;
        // p.set_pref(spot::postprocessor::Parity);
        // p.set_pref(spot::postprocessor::Deterministic);
        // res = p.run(res);
        return res;
    }
}