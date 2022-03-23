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

#include "decomposer.hpp"

#include <set>
#include <vector>
#include <functional>
#include <queue>

#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/postproc.hh>


namespace cola
{

std::vector<spot::twa_graph_ptr>
decomposer::run()
{
    std::vector<spot::twa_graph_ptr> result;
    spot::scc_info si(nba_, spot::scc_info_options::ALL);

    if (num_nbas_ == -1)
    {
        num_nbas_ = si.scc_count();
    }

    std::string scc_types = get_scc_types(si);
    std::vector<bool> reach_sccs = find_scc_paths_(si);

    struct pair_compare
    {
        // reverse order
        bool operator()(std::pair<std::set<unsigned>, unsigned> scc_i, std::pair<std::set<unsigned>, unsigned> scc_j) const
        {
            return scc_i.second <= scc_j.second;
        }
    };
    if (om_.get(VERBOSE_LEVEL) > 0)
    {
        std::cout << "Start to decompose the NBA\n";
    }
    // TODO: classify weak SCC into one?
    // first deal with SCCs with large numbers
    // SCC with more states gets priority to decompose
    //std::priority_queue<std::pair<unsigned, unsigned>, std::vector<std::pair<unsigned, unsigned>>, pair_compare> scclist;
    std::set<unsigned> weak_sccs;
    unsigned num_weak_states = 0;
    std::map<unsigned, unsigned> non_weak_sccs;
    std::priority_queue<std::pair<std::set<unsigned>, unsigned>, std::vector<std::pair<std::set<unsigned>, unsigned>>, pair_compare> scclist;

    for (unsigned sc = 0; sc < si.scc_count(); sc ++)
    {
        // only care about accepting scc
        if (! si.is_accepting_scc(sc)) continue;
        if ( is_weakscc(scc_types, sc))
        {
            weak_sccs.insert(sc);
            num_weak_states +=  si.states_of(sc).size();
        }else 
        {
            non_weak_sccs.emplace(sc, si.states_of(sc).size());
        }
    }
    // first weak
    if (num_weak_states > 0)
    {
        scclist.push(std::make_pair(weak_sccs, num_weak_states));
    }

    for (auto& sc : non_weak_sccs)
    {
        std::set<unsigned> set;
        set.insert(sc.first);
        scclist.push(std::make_pair(set, sc.second));
    }

    while(scclist.size() > 0)
    {
        
        std::set<unsigned> sccs = scclist.top().first;
        scclist.pop();
        // sccs.insert(scc_i);
        spot::twa_graph_ptr aut = make_twa_with_scc(si, sccs, reach_sccs);
        result.push_back(aut);

        -- num_nbas_;
        if(num_nbas_ == 1 && scclist.size() > 0)
        {
            // put rest together
            break;
        }
    }
    std::set<unsigned> remaining_sccs;
    while(scclist.size() > 0)
    {
        std::set<unsigned> scc_set = scclist.top().first;
        scclist.pop();
        remaining_sccs.insert(scc_set.begin(), scc_set.end());
    }
    if (! remaining_sccs.empty())
    {
        spot::twa_graph_ptr aut = make_twa_with_scc(si, remaining_sccs, reach_sccs);
        result.push_back(aut);
    }
    if (om_.get(VERBOSE_LEVEL) > 0)
    {
        std::cout << "The original NBA has been decomposed into " << result.size() << " small NBAs\n";
    }
    return result;
}

spot::twa_graph_ptr
decomposer::make_twa_with_scc(spot::scc_info& si, std::set<unsigned> sccs, std::vector<bool>& reach_sccs)
{
    assert(! sccs.empty());

    auto scc_reach = [&si, &reach_sccs](unsigned s, unsigned t) -> bool
    {
      // compute the reachability 
      return s == t || (s > t) && (reach_sccs[t + compute_median(s)]);
    };
    
    // now construct new DPAs
    spot::twa_graph_ptr res = spot::make_twa_graph(nba_->get_dict());
    res->copy_ap_of(nba_);
    res->prop_copy(nba_,
                   {
                       false,        // state based
                       nba_->prop_inherently_weak().is_true(),        // inherently_weak
                       false, false, // deterministic
                       nba_->prop_complete().is_true(),         // complete
                       nba_->prop_stutter_invariant().is_true()         // stutter inv
                   });
    for (unsigned s = 0; s < nba_->num_states(); s++)
    {
      res->new_state();
    }
    auto is_good_scc = [&scc_reach, &sccs](unsigned scc_i) -> bool
    {
        for(auto scc : sccs)
        {
            if (scc == scc_i) return true;
            if (scc_reach(scc_i, scc))
            {
                return true;
            }
        }
        return false;
    };
    for (auto &t : nba_->edges())
    {
      // out going transition for t.src
      unsigned scc_src = si.scc_of(t.src);
      unsigned scc_dst = si.scc_of(t.dst);
      if (is_good_scc(scc_src) && is_good_scc(scc_dst))
      {
        //   if(sccs.find(scc_src) != sccs.end() && sccs.find(scc_dst) != sccs.end())
            res->new_edge(t.src, t.dst, t.cond, t.acc);
      }
    }
    // names
    res->set_init_state(nba_->get_init_state_number());
    // now acceptance condition
    res->set_buchi();
    // remove unreachable macrostates
    spot::postprocessor p;
    p.set_type(spot::postprocessor::Buchi);
    res = p.run(res);
    return res;
}

}

