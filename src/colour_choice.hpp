// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#pragma once
#include <spot/twa/twagraph.hh>
#include <string>
#include <vector>

namespace cola
{
  struct colour_choice_options
  {
    unsigned max_clauses = 64;
    unsigned max_regions = 4096;
    unsigned max_formula_words = 4096;
    unsigned max_colours = spot::acc_cond::mark_t::max_accsets();
  };

  struct colour_scc_certificate
  {
    unsigned scc = 0, states = 0, clauses = 0, regions = 0, fresh_colours = 0;
    bool target_deterministic = false;
    std::string reason;
  };

  struct colour_choice_result
  {
    spot::twa_graph_ptr automaton;
    std::vector<colour_scc_certificate> sccs;
    unsigned rewritten = 0;
    bool equivalent = true;
  };

  // Eliminate only internal acceptance-choice nondeterminism. State numbers,
  // internal successor relations and inter-SCC transitions are preserved.
  // Rewriting is transactional per SCC and globally checked for equivalence.
  colour_choice_result eliminate_colour_choices(
    const spot::const_twa_graph_ptr& input,
    const colour_choice_options& options = {});
}
