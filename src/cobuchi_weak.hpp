// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#pragma once
#include "colour_choice.hpp"

namespace cola
{
  struct cobuchi_weak_options
  {
    unsigned max_states = 512;
    unsigned max_clauses = 64;
    unsigned max_edges = 16384;
    unsigned max_colours = spot::acc_cond::mark_t::max_accsets();
  };

  // Convert unsupported SCCs with positive Fin-only local acceptance into
  // rejecting prefix SCCs and accepting weak copies. This may add states.
  // It is separate from the state-preserving colour-choice transformation.
  colour_choice_result weakify_cobuchi_sccs(
    const spot::const_twa_graph_ptr& input,
    const cobuchi_weak_options& options = {});
}
