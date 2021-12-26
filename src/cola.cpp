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

#include "cola.hpp"
#include "optimizer.hpp"

#include <seminator.hpp>

#include <cutdet.hpp>
#include <bscc.hpp>
#include <breakpoint_twa.hpp>
#include <vector>

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
  is_elevator_automaton(const spot::const_twa_graph_ptr &aut)
  {
    spot::scc_info si(aut);
    unsigned nc = si.scc_count();
    for (unsigned scc = 0; scc < nc; ++scc)
    {
      if (is_deterministic_scc(scc, si) || spot::is_inherently_weak_scc(si, scc))
      {
          continue;
      }
      return false;
    }
    return true;
  }

  std::vector<bool>
  get_deterministic_sccs(spot::scc_info &si)
  {
    std::vector<bool> res;
    unsigned nc = si.scc_count();
    for (unsigned scc = 0; scc < nc; ++scc)
    {
      res.push_back(is_deterministic_scc(scc, si));
    }
    return res;
  }

  std::string
  get_set_string(const state_set &set)
  {
    std::string res = "{";
    bool first = true;
    for (state_t s : set)
    {
      if (first)
      {
        first = false;
      }
      else
      {
        res += ", ";
      }
      res += std::to_string(s);
    }
    res += "}";
    return res;
  }

  // NOTE: copied from spot/twaalgos/deterministic.cc in SPOT
  std::vector<char>
  find_scc_paths(const spot::scc_info &scc)
  {
    unsigned scccount = scc.scc_count();
    std::vector<char> res(scccount * scccount, 0);
    for (unsigned i = 0; i != scccount; ++i)
      res[i + scccount * i] = 1;
    for (unsigned i = 0; i != scccount; ++i)
    {
      unsigned ibase = i * scccount;
      for (unsigned d : scc.succ(i))
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

  void output_file(spot::const_twa_graph_ptr aut, const char *file)
  {
    const char *opts = nullptr;
    std::ofstream outfile;
    std::string file_name(file);
    outfile.open(file_name);

    spot::print_hoa(outfile, aut, opts);
    outfile.close();
  }

    /// \brief Output an automaton to a file
  // std::vector<bool>
  // is_reachable_weak_sccs(const spot::scc_info &si, state_simulator& sim)
  // {
  //   std::vector<bool> res;
  //   unsigned nc = si.scc_count();
  //   for (unsigned sc = 0; sc < nc; ++sc)
  //   {
  //     res.push_back(false);
  //     if( spot::is_inherently_weak_scc(s, sc) && )
  //     {

  //     }
  //     if (is_deterministic_scc(scc, si) || spot::is_inherently_weak_scc(si, scc))
  //       continue;
  //     return false;
  //   }
  // }
}