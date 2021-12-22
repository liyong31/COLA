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

#include "optimizer.hpp"

#include <set>
#include <map>

using state_t = unsigned;
using state_set = std::set<state_t>;

struct state_set_hash
{
  size_t
  operator()(const state_set &s) const noexcept
  {
    size_t hash = 0;
    for (const auto &p : s)
    {
      hash = spot::wang32_hash(p);
    }
    return hash;
  }
};
// put together the mstates with the same reachable states of input NBA
using mstate_equiv_map = std::unordered_map<state_set, state_set, state_set_hash>;

namespace cola
{

  spot::twa_graph_ptr
  complement_semidet_opt(const spot::const_twa_graph_ptr &aut, bool show_names = false);

  spot::twa_graph_ptr
  complement_semidet_onthefly(const spot::const_twa_graph_ptr &aut, bool show_names = false);

  spot::twa_graph_ptr
  complement_semidet_opt_onthefly(const spot::const_twa_graph_ptr &aut, bool show_names = false);

  /// \brief Complement a unambiguous TωA
  ///
  /// The automaton \a aut should be unambiguous.
  ///
  /// Uses the NCSB algorithm described by Y. Li, M.Y. Vardi, and L. Zhang (GandALF'20)
  spot::twa_graph_ptr
  complement_unambiguous(const spot::const_twa_graph_ptr &aut, bool show_names = false);

  /// \brief Complement a semideterministic TωA
  ///
  /// The automaton \a aut should be semideterministic.
  ///
  /// Uses the NCB algorithm described by Y. Li
  spot::twa_graph_ptr
  new_complement_semidet(const spot::const_twa_graph_ptr &aut, bool show_names = false);

  // /// \brief Determinization
  // ///
  // /// The automaton \a aut should be a semideterminisitc.
  // /// Output a deterministic rabin automaton
  // spot::twa_graph_ptr
  // determinize_rabin(const spot::const_twa_graph_ptr& aut, bool show_names = false);

  /// \brief Determinizing semi-deterministic or limit deterministic or elevator Buchi automaton
  ///
  /// The automaton \a aut should be a semideterminisitc.
  /// Output a deterministic parity automaton
  spot::twa_graph_ptr
  determinize_tldba(const spot::const_twa_graph_ptr &aut, bool show_names, optimizer &opt, bool use_scc, bool use_unambiguous, bool use_stutter);

  /// \brief Determinizing TBA by combining the semi-determinization of TBA
  /// and the determinization of TLDBA 
  ///
  /// The automaton \a aut should have Buchi condition.
  /// Output a deterministic parity automaton
  spot::twa_graph_ptr
  determinize_tba(const spot::const_twa_graph_ptr &aut, bool show_names, optimizer &opt, bool use_scc, bool use_unambiguous, bool use_stutter);

  /// \brief Testing whether the input is an elevator automata in which every scc is either deterministic
  /// or inherently weak (i.e., the states/transitions are either all accepting or nonaccepting)
  ///
  /// Output a bool value
  bool
  is_elevator_automaton(const spot::const_twa_graph_ptr &aut);

  /// \brief Output the set of states
  ///
  std::string
  get_set_string(const state_set &set);

  /// \brief Compute the reachability of the SCCs
  /// 
  ///
  /// Output a vector res such that res[i + scccount*j] = 1 iff SCC i is reachable from SCC j
  std::vector<char>
  find_scc_paths(const spot::scc_info &scc);

  class mstate_merger
  {
  private:
    // the constructed DPA to be reduced
    spot::twa_graph_ptr &dpa_;
    // mstates that are identified with the same language
    // Item = (set of reachable states of NBA, the set of mstates with the set of reachable states).
    const mstate_equiv_map &equiv_map_;

  public:
    mstate_merger(spot::twa_graph_ptr &dpa, const mstate_equiv_map &equiv_map)
        : dpa_(dpa), equiv_map_(equiv_map)
    {
    }

    spot::twa_graph_ptr
    run();
  };

}
