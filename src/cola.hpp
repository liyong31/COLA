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
#include <vector>
#include <fstream>
#include <string>

#include <spot/twaalgos/hoa.hh>
#include <spot/misc/optionmap.hh>
#include <spot/twaalgos/sccinfo.hh>

// options for the determinization constructions
static const char *USE_SIMULATION = "use-simulation";
static const char *USE_STUTTER = "use-stutter";
static const char *USE_SCC_INFO = "use-scc";
static const char *USE_UNAMBIGUITY = "use-unambiguity";
static const char *VERBOSE_LEVEL = "verbose-level";

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
  determinize_tldba(const spot::const_twa_graph_ptr &aut, spot::option_map &om);

  /// \brief Determinizing TBA by combining the semi-determinization of TBA
  /// and the determinization of TLDBA
  ///
  /// The automaton \a aut should have Buchi condition.
  /// Output a deterministic parity automaton
  spot::twa_graph_ptr
  determinize_tba(const spot::const_twa_graph_ptr &aut, spot::option_map &om);

  /// \brief Testing whether the input is an elevator automata in which every scc is either deterministic
  /// or inherently weak (i.e., the states/transitions are either all accepting or nonaccepting)
  ///
  /// Output a bool value
  bool
  is_elevator_automaton(const spot::const_twa_graph_ptr &aut);

  /// \brief Output the set of states
  ///
  std::string
  get_set_string(const std::set<unsigned> &set);

  /// \brief Compute the reachability of the SCCs
  ///
  ///
  /// Output a vector res such that res[i + scccount*j] = 1 iff SCC i is reachable from SCC j
  std::vector<char>
  find_scc_paths(const spot::scc_info &scc);

  /// \brief Output an automaton to a file
  void output_file(spot::const_twa_graph_ptr aut, const char *file);

  std::vector<bool>
  get_deterministic_sccs(spot::scc_info &scc);

  std::vector<bool>
  get_elevator_sccs(spot::scc_info &scc);

  // /// \brief Output an automaton to a file
  // std::vector<bool>
  // is_reachable_weak_sccs(const spot::scc_info &scc, state_simulator& sim);

}
