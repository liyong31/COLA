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
        continue;
      return false;
    }
    return true;
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

  void output_file(spot::twa_graph_ptr aut, const char *file)
  {
    const char *opts = nullptr;
    std::ofstream outfile;
    std::string file_name(file);
    outfile.open(file_name);

    spot::print_hoa(outfile, aut, opts);
    outfile.close();
  }


  spot::twa_graph_ptr
  mstate_merger::run()
  {
    unsigned num_states = dpa_->num_states();
    // a map that maps the original mstate to the replaced mstate
    std::vector<unsigned> replace_states(num_states);
    // by default the replacement is itself
    for (unsigned s = 0; s < num_states; s++)
    {
      replace_states[s] = s;
    }
    spot::scc_info scc(dpa_, spot::scc_info_options::ALL);
    // reach_sccs[i + scccount*j] = 1 iff SCC i is reachable from SCC j
    std::vector<char> reach_sccs = find_scc_paths(scc);
    // whether the state s can reach t
    auto scc_reach = [&scc, &reach_sccs](unsigned s, unsigned t) -> bool
    {
      return s == t || (reach_sccs[t + scc.scc_count() * s]);
    };
    // set of states -> the forest of reachability in the states.
    // output
    bool debug = false;
    unsigned num_replaced_states = 0;
    // Key: set of reached states in NBA, Value: the mstates with the same Key
    for (auto p = equiv_map_.begin(); p != equiv_map_.end(); p++)
    {
      // if there is only one mstate, no need to replace
      if (p->second.size() <= 1)
        continue;
      if (debug)
      {
        std::cout << "state = " + get_set_string(p->first) + "\n";
        for (auto t : p->second)
        {
          std::cout << " " << t << "(" << scc.scc_of(t) << ")";
        }
        std::cout << "\n";
      }
      // now compute states
      std::vector<unsigned> reach_vec(scc.scc_count());
      // indicator for no successor SCC
      unsigned no_next_scc = scc.scc_count();
      for (unsigned scc_i = 0; scc_i < scc.scc_count(); scc_i++)
      {
        // first set to non scc
        reach_vec[scc_i] = no_next_scc;
      }
      std::set<unsigned> not_bottom_set;
      std::set<unsigned> bottom_set;
      // traverse the number of states in p->second
      std::unordered_map<unsigned, unsigned> scc2repr;
      for (auto s : p->second)
      {
        unsigned scc_s_idx = scc.scc_of(s);
        bottom_set.insert(scc_s_idx);
        auto val_state = scc2repr.find(scc_s_idx);
        if (val_state == scc2repr.end())
        {
          scc2repr[scc_s_idx] = s;
        }
        else
        {
          // keep the smallest one
          scc2repr[scc_s_idx] = std::min(s, scc2repr[scc_s_idx]);
        }
      }
      // if all mstates are in the same SCC, no need to replace states
      if (bottom_set.size() <= 1)
      {
        continue;
      }
      // check the reachability of SCCs
      for (auto fst_scc : bottom_set)
      {
        for (auto snd_scc : bottom_set)
        {
          if (fst_scc == snd_scc)
            continue;
          if (scc_reach(fst_scc, snd_scc))
          {
            // only record the smallest SCC that fst_scc can reach so far
            reach_vec[fst_scc] = std::min(snd_scc, reach_vec[fst_scc]);
            // record the SCC that have successors
            not_bottom_set.insert(fst_scc);
            continue;
          }
        }
      }
      if (debug)
      {
        std::cout << "Bottom set: {";
        for (auto s : bottom_set)
        {
          if (not_bottom_set.find(s) == not_bottom_set.end())
          {
            std::cout << " " << s << " (state=" << scc2repr[s] << ")";
          }
          else
          {
            std::cout << " " << s << "(next=" << reach_vec[s] << ") ";
          }
        }
        std::cout << "}\n";
      }
      // reach the bottom scc from a given scc
      auto get_bottom_scc = [&reach_vec, &no_next_scc](unsigned scc_idx) -> unsigned
      {
        while (true)
        {
          if (reach_vec[scc_idx] == no_next_scc)
          {
            break;
          }
          scc_idx = reach_vec[scc_idx];
        }
        return scc_idx;
      };
      // compute the replacement of each state
      for (auto t : p->second)
      {
        unsigned scc_idx = scc.scc_of(t);
        unsigned bottom_scc_idx = get_bottom_scc(scc_idx);
        // if t is not in the bottom scc, then it can be replace by a state in
        // the bottom scc
        if (bottom_scc_idx != scc_idx)
        {
          replace_states[t] = scc2repr[bottom_scc_idx];
          ++num_replaced_states;
        }
      }
    }
    std::cout << "The number of states reduced by mstate_merger: "
              << num_replaced_states << " {out of "
              << dpa_->num_states() << "}" << std::endl;
    if (num_replaced_states == 0)
    {
      return dpa_;
    }
    // now construct new DPAs
    spot::twa_graph_ptr res = spot::make_twa_graph(dpa_->get_dict());
    res->copy_ap_of(dpa_);
    res->prop_copy(dpa_,
                   {
                       false,        // state based
                       false,        // inherently_weak
                       false, false, // deterministic
                       true,         // complete
                       false         // stutter inv
                   });
    for (unsigned s = 0; s < num_states; s++)
    {
      res->new_state();
    }
    for (auto &t : dpa_->edges())
    {
      // out going transition for t.src
      if (t.src == replace_states[t.src] && t.dst == replace_states[t.dst])
      {
        res->new_edge(t.src, t.dst, t.cond, t.acc);
      }
      else if (t.src == replace_states[t.src] && t.dst != replace_states[t.dst])
      {
        res->new_edge(t.src, replace_states[t.dst], t.cond, t.acc);
      }
      // igonre the rest cases
      //t.src != replace_states[t.src] && t.dst == replace_states[t.dst])
      //t.src != replace_states[t.src] && t.dst != replace_states[t.dst])
    }
    res->set_init_state(replace_states[dpa_->get_init_state_number()]);
    // now acceptance condition
    res->set_acceptance(dpa_->num_sets(), spot::acc_cond::acc_code::parity_min_even(dpa_->num_sets()));
    if (dpa_->prop_complete().is_true())
      res->prop_complete(true);
    res->prop_universal(true);
    res->prop_state_acc(false);
    // remove unreachable macrostates
    res->purge_unreachable_states();
    return res;
  }
}