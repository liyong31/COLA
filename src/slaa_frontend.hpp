// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#pragma once
#include <spot/tl/formula.hh>
#include <spot/twa/twagraph.hh>
#include <string>

namespace cola
{
  // Runs only LTL3TELA's positive, unsplit SLAA/dealternation path, keeping
  // Fin marks. A failed, oversized, or timed-out attempt returns nullptr.
  // The timeout covers the child, not parsing or later language checking.
  spot::twa_graph_ptr slaa_frontend(spot::formula f, spot::bdd_dict_ptr dict,
                                  const std::string& tool,
                                  unsigned timeout_ms, unsigned state_limit);
  // OWL's optimized generalized-Buchi LTL-to-limit-deterministic frontend.
  // Bypass its easy-fragment portfolio; COLA already handles those directly.
  spot::twa_graph_ptr owl_ldgba_frontend(spot::formula f, spot::bdd_dict_ptr dict,
                                       const std::string& tool,
                                       const std::string& construction,
                                       unsigned timeout_ms, unsigned state_limit);
}
