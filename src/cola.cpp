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
#include <sstream>

#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/isweakscc.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/misc/optionmap.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/word.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twa/twagraph.hh>

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

  bool
  is_elevator_automaton(const spot::scc_info &scc, std::string& scc_str)
  {
    for (unsigned sc = 0; sc < scc.scc_count(); ++sc)
    {
      if ((scc_str[sc]&SCC_INSIDE_DET_TYPE) > 0 
      || (scc_str[sc]&SCC_WEAK_TYPE) > 0)
      {
          continue;
      }
      return false;
    }
    return true;
  }

  bool
  is_weak_automaton(const spot::const_twa_graph_ptr &aut)
  {
    spot::scc_info si(aut);
    unsigned nc = si.scc_count();
    for (unsigned scc = 0; scc < nc; ++scc)
    {
      if (spot::is_inherently_weak_scc(si, scc))
      {
          continue;
      }
      return false;
    }
    return true;
  }

  bool
  is_weak_automaton(const spot::scc_info &scc, std::string& scc_str)
  {
    for (unsigned sc = 0; sc < scc.scc_count(); ++sc)
    {
      if (scc_str[sc]&SCC_WEAK_TYPE)
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
  //res[i + scccount*j] = 1 iff SCC i is reachable from SCC j
  std::vector<bool>
  find_scc_paths(const spot::scc_info &scc)
  {
    unsigned scccount = scc.scc_count();
    std::vector<bool> res(scccount * scccount, 0);
    for (unsigned i = 0; i < scccount; ++i)
      {
        // reach itself
        res[i + scccount * i] = true;
      }
    for (unsigned i = 0; i < scccount; ++i)
    {
      unsigned ibase = i * scccount;
      for (unsigned d : scc.succ(i))
      {
        // we necessarily have d < i because of the way SCCs are
        // numbered, so we can build the transitive closure by
        // just ORing any SCC reachable from d.
        unsigned dbase = d * scccount;
        // j reach d (i can reach d, so res[d + i * scccount] = 1)
        for (unsigned j = 0; j < scccount; ++j)
        {
          // j is reachable from i if j is reachable from d 
          res[ibase + j] = res[ibase + j] || res[dbase + j];
        }
      }
    }
    return res;
  }

  /// Output a vector res such that res[i + (j+1)*j/2] = 1 iff SCC i is reachable from SCC j
  std::vector<bool>
  find_scc_paths_(const spot::scc_info &scc)
  {
    unsigned scccount = scc.scc_count();
    std::vector<bool> res(scccount * (scccount + 1) / 2 , false);
    for (unsigned i = 0; i < scccount; ++i)
      {
        // reach itself
        res[i + i * (i + 1) / 2] = true;
      }
    for (unsigned i = 0; i < scccount; ++i)
    {
      unsigned ibase = (i * ( i + 1)) / 2;
      for (unsigned d : scc.succ(i))
      {
        // we necessarily have d < i because of the way SCCs are
        // numbered, so we can build the transitive closure by
        // just ORing any SCC reachable from d.
        unsigned dbase = d * (d + 1) / 2;
        // j reach d (i can reach d, so res[d + i * scccount] = 1)
        for (unsigned j = 0; j <= d; ++j)
        {
          // j is reachable from i if j is reachable from d (d > j)
          res[ibase + j] = res[ibase + j] || res[dbase + j];
        }
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
  std::vector<bool>
  get_accepting_reachable_sccs(spot::scc_info &si)
  {
    unsigned nscc = si.scc_count();
    assert(nscc);
    std::vector<bool> reachable_from_acc(nscc);
    std::vector<bool> res(nscc);
    do // iterator of SCCs in reverse topological order
      {
        --nscc;
        // larger nscc is closer to initial state?
        if (si.is_accepting_scc(nscc) || reachable_from_acc[nscc])
          {
            for (unsigned succ: si.succ(nscc))
              reachable_from_acc[succ] = true;
            res[nscc] = true;
          }
      }
    while (nscc);
    return res;
  }

  bool
  is_limit_deterministic_automaton(const spot::scc_info &si, std::string& scc_str)
  {
    unsigned nscc = si.scc_count();
    assert(nscc);
    std::vector<bool> reachable_from_acc(nscc);
    do // iterator of SCCs in reverse topological order
      {
        --nscc;
        // larger nscc is closer to initial state?
        if ((scc_str[nscc] & SCC_ACC) > 0 || reachable_from_acc[nscc])
          {
            // need to check all outgoing transitions of states in the SCC
            if ((scc_str[nscc] & SCC_DET_TYPE) == 0)
            {
              return false;
            }
            for (unsigned succ: si.succ(nscc))
              reachable_from_acc[succ] = true;
          }
      }
    while (nscc);
    return true;
  }

  std::string
  get_scc_types(spot::scc_info &si)
  {
    unsigned nc = si.scc_count();
    std::string res(nc, 0);
    for (unsigned sc = 0; sc < nc; ++sc)
    {
      char type = 0;
      type |= is_deterministic_scc(sc, si) ? SCC_INSIDE_DET_TYPE : 0; // only care about the states inside SCC
      type |= is_deterministic_scc(sc, si, false) ? SCC_DET_TYPE : 0; // must also be deterministic for all transitions after accepting
      type |=  spot::is_inherently_weak_scc(si, sc) ? SCC_WEAK_TYPE : 0;
      type |= si.is_accepting_scc(sc) ? SCC_ACC : 0;
      // other type is 0
      res[sc] = type;
    }
    return res;
  }

  void
  print_scc_types(std::string& scc_types, spot::scc_info &scc)
  {
    std::vector<bool> reach_sccs = get_accepting_reachable_sccs(scc);
    for (unsigned i = 0; i < scc.scc_count(); i ++)
    {
      std::cout << "Scc " << i;
      if (scc_types[i] & SCC_WEAK_TYPE)
      {
        std::cout << " weak";
      }
      if (scc_types[i] & SCC_INSIDE_DET_TYPE)
      {
        std::cout << " inside-det";
      }
      if (scc_types[i] & SCC_DET_TYPE)
      {
        std::cout << " det";
      }
      if (scc_types[i] & SCC_ACC)
      {
        std::cout << " accepting";
      }
      std::cout << " " << reach_sccs[i]<< std::endl;
    }
  }

  void
  check_equivalence(spot::const_twa_graph_ptr nba, spot::twa_graph_ptr dpa)
  {
    spot::twa_graph_ptr dualized_dpa = spot::complement(dpa);
    spot::twa_word_ptr word = nba->intersecting_word(dualized_dpa);
    std::stringstream ss;
    if (word != nullptr)
    {
      ss << (*word);
      std::cout << "dpa should accept word: " << ss.str() << std::endl;
      exit(-1);
    }
    spot::twa_graph_ptr dualized_nba = spot::complement(nba);
    word = dpa->intersecting_word(dualized_nba);
    if (word != nullptr)
    {
      ss << (*word);
      std::cout << "dpa should not accept word: " <<  ss.str() << std::endl;
      exit(-1);
    }
  }

  bool
  is_acepting_detscc(std::string& scc_types, unsigned scc)
  {
    return (scc_types[scc] & SCC_WEAK_TYPE) == 0 && (scc_types[scc] & SCC_INSIDE_DET_TYPE) > 0 && (scc_types[scc] & SCC_ACC) > 0;
  }

  bool 
  is_accepting_weakscc(std::string& scc_types, unsigned scc)
  {
    return (scc_types[scc] & SCC_WEAK_TYPE) > 0 && (scc_types[scc] & SCC_ACC) > 0;
  }

  bool 
  is_weakscc(std::string& scc_types, unsigned scc)
  {
    return (scc_types[scc] & SCC_WEAK_TYPE) > 0;
  }

  bool
  is_accepting_nondetscc(std::string& scc_types, unsigned scc)
  {
    return (scc_types[scc] & SCC_WEAK_TYPE) == 0 && (scc_types[scc] & SCC_INSIDE_DET_TYPE) == 0 && (scc_types[scc] & SCC_ACC) > 0;
  }
}