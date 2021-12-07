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

  /// \brief Determinization
  /// 
  /// The automaton \a aut should be a semideterminisitc.
  /// Output a deterministic rabin automaton
  spot::twa_graph_ptr
  determinize_rabin(const spot::const_twa_graph_ptr& aut, bool show_names = false);
  
  /// \brief Determinization
  /// 
  /// The automaton \a aut should be a semideterminisitc.
  /// Output a deterministic parity automaton
  spot::twa_graph_ptr
  determinize_tldba(const spot::const_twa_graph_ptr& aut, bool show_names, optimizer &opt, bool use_unambiguous, bool use_stutter);
    

}