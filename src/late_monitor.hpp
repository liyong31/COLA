// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#pragma once
#include <spot/twa/twagraph.hh>
#include <string>
#include <vector>

namespace cola
{
  struct late_monitor_options
  {
    unsigned max_profiles = 8;
    unsigned max_states = 4096;
    unsigned max_edges = 65536;
  };
  struct late_monitor_result
  {
    spot::twa_graph_ptr automaton;
    unsigned profiles = 0;
    std::string reason;
  };

  // Experimental acceptance-parametric interface. mixed_acceptance indexes
  // skeleton colours first, then the raw colours of each global monitor.
  // Monitors must be complete/deterministic and share the skeleton dictionary.
  // Monitor predicates are substituted before native determinisation; their
  // actual colours are composed only once, afterwards. Every profile gets its
  // own checked native instance, so pruning never assumes an unknown valuation.
  // This bounded reference implementation has a PRODUCT of profile state
  // counts, not the stronger single-rank-graph bound proposed in idea.md.
  // Null result means a budget, unsupported profile or verification failed.
  late_monitor_result determinise_with_global_monitors(
    const spot::const_twa_graph_ptr& skeleton,
    const std::vector<spot::twa_graph_ptr>& monitors,
    const spot::acc_cond::acc_code& mixed_acceptance,
    const late_monitor_options& options = {});
}
