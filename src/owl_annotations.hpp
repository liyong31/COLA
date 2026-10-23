// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#pragma once
#include <spot/twa/twagraph.hh>
#include <spot/tl/formula.hh>
#include <map>
#include <vector>

namespace cola
{
  struct owl_annotation_stats
  {
    unsigned decoded = 0, certified = 0, rejected = 0;
    unsigned pair_proofs = 0, union_proofs = 0;
  };

  // Decode OWL 21 SEJK16/EKS20 accepting-state descriptions, then certify
  // each reconstructed formula against the automaton rooted at that state.
  // Missing, malformed and inequivalent annotations remain unknown.
  class owl_language_oracle
  {
    spot::bdd_dict_ptr dict_ = spot::make_bdd_dict();
    std::map<spot::formula, bdd> atoms_;
    std::vector<spot::formula> formulas_;
    std::vector<bdd> languages_;
    bdd boolean_abstraction(spot::formula f);
  public:
    owl_annotation_stats stats;
    explicit owl_language_oracle(const spot::const_twa_graph_ptr& aut);
    ~owl_language_oracle();
    owl_language_oracle(const owl_language_oracle&) = delete;
    owl_language_oracle& operator=(const owl_language_oracle&) = delete;
    bool known(unsigned state) const;
    bool covers(unsigned target, const std::vector<unsigned>& older) const;
  };
}
