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
static const char *USE_DELAYED_SIMULATION = "use-delayed-simulation";
static const char *USE_STUTTER = "use-stutter";
static const char *USE_SCC_INFO = "use-scc";
static const char *USE_UNAMBIGUITY = "use-unambiguity";
static const char *MORE_ACC_EDGES = "more-acc-edges";
static const char *VERBOSE_LEVEL = "verbose-level";
static const char *NUM_NBA_DECOMPOSED = "num-nba-decomposed";
static const char *NUM_SCC_LIMIT_MERGER = "num-scc-limit-merger";
static const char *SCC_REACH_MEMORY_LIMIT = "scc-reach-memory-limit";
static const char *REQUIRE_PARITY = "require-parity";
static const char *NUM_TRANS_PRUNING = "num-trans-pruning"; 
static const char *MSTATE_REARRANGE = "rank-rearrange";


static const char SCC_WEAK_TYPE = 1;
static const char SCC_INSIDE_DET_TYPE = 2;
static const char SCC_DET_TYPE = 4;
static const char SCC_ACC = 8;


// for states ranking/labelling
static const int RANK_N = -1; // nondeterministic states
static const int RANK_M = -2; // missing states

enum automaton_type
{
  NONDETERMINISTIC = 0,
  INHERENTLY_WEAK  = 1,
  ELEVATOR         = 2,
  LIMIT_DETERMINISTIC = 4
};

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

  /// \brief Complementation
  ///
  /// The automaton \a aut should be an elevator automaton for now.
  /// Output a generalized Buchi automaton
  spot::twa_graph_ptr
  complement_tnba(const spot::const_twa_graph_ptr &aut, spot::option_map &om);


  spot::twa_graph_ptr
  determinize_twba(const spot::const_twa_graph_ptr &aut, spot::option_map &om);

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
  // spot::twa_graph_ptr
  // determinize_tba(const spot::const_twa_graph_ptr &aut, spot::option_map &om);

  /// \brief Determinizing TNBA by independently determinizing different SCCs
  ///
  /// The automaton \a aut should have Buchi condition.
  /// Output a deterministic Emenson-Lei automaton
  spot::twa_graph_ptr
  determinize_tnba(const spot::const_twa_graph_ptr &aut, spot::option_map &om);


  /// \brief Determinizing elevator Buchi automaton that has either deterministic or weak SCCs
  ///
  /// The automaton \a aut should be an elevator automaton.
  /// Output a deterministic automaton
  spot::twa_graph_ptr
  determinize_televator(const spot::const_twa_graph_ptr &aut, spot::option_map &om);


  // ============================ helper functions ===================================

  /// \brief Testing whether the input is an elevator automata in which every scc is either deterministic
  /// or inherently weak (i.e., the states/transitions are either all accepting or nonaccepting)
  ///
  /// Output a bool value
  bool
  is_elevator_automaton(const spot::scc_info &scc, std::string& scc_str);

  bool
  is_elevator_automaton(const spot::const_twa_graph_ptr &aut);

  bool
  is_weak_automaton(const spot::const_twa_graph_ptr &aut);
  
  bool
  is_weak_automaton(const spot::scc_info &scc, std::string& scc_str);

  bool
  is_limit_deterministic_automaton(const spot::scc_info &scc, std::string& scc_str);

  /// \brief Output the set of states
  ///
  std::string
  get_set_string(const std::set<unsigned> &set);

  /// \brief Compute the reachability of the SCCs
  ///
  ///
  /// Output a vector res such that res[i + scccount*j] = 1 iff SCC i is reachable from SCC j
  std::vector<bool>
  find_scc_paths(const spot::scc_info &scc);
  /// Output a vector res such that res[i + (j+1)*j/2] = 1 iff SCC i is reachable from SCC 
  /// Must ensure that j >= i
  std::vector<bool>
  find_scc_paths_(const spot::scc_info &scc);

  /// \brief Output an automaton to a file
  void output_file(spot::const_twa_graph_ptr aut, const char *file);

  std::vector<bool>
  get_deterministic_sccs(spot::scc_info &scc);

  std::vector<bool>
  get_accepting_reachable_sccs(spot::scc_info &scc);

  std::string
  get_scc_types(spot::scc_info &scc);
  // /// \brief Output an automaton to a file
  // std::vector<bool>
  // is_reachable_weak_sccs(const spot::scc_info &scc, state_simulator& sim);
  void
  print_scc_types(std::string& scc_types, spot::scc_info &scc);

  // Check the equivalence of the constructed dpa and the input nba
  void
  check_equivalence(spot::const_twa_graph_ptr nba, spot::twa_graph_ptr dpa);

  bool
  is_accepting_detscc(std::string& scc_types, unsigned scc);

  bool 
  is_accepting_weakscc(std::string& scc_types, unsigned scc);

  bool 
  is_weakscc(std::string& scc_types, unsigned scc);

  bool
  is_accepting_nondetscc(std::string& scc_types, unsigned scc);

  bool 
  is_deterministic_scc(unsigned scc, spot::scc_info& si,
                     bool inside_only = true);

}
