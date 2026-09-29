// Copyright (C) 2026  The COLA Authors
//
// This file is part of COLA, a tool for determinization and complementation
// of omega automata.
//
// COLA is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.

#pragma once

#include "cola.hpp"

#include <spot/tl/formula.hh>
#include <spot/tl/simplify.hh>
#include <spot/twa/bdddict.hh>

#include <iosfwd>
#include <vector>

namespace cola
{
  struct ltl2dela_options
  {
    bool boolean_decomposition = true;
    bool use_profiles = true;
    bool use_delta2 = true;
    bool use_recurrence_compiler = true;
    bool use_master_profiles = true;
    bool use_state_annotations = true;
    bool use_exact_state_languages = true;
    bool require_profile_progress = true;

    unsigned profile_depth = 4;
    unsigned profile_budget = 24;
    unsigned profile_lookahead = 8;
    unsigned profile_guard_max_length = 64;

    // Delta2 normalization is useful, but can increase the formula
    // substantially.  Apply it only to small residuals and keep the result
    // only when the growth stays below this factor.
    unsigned delta2_input_limit = 128;
    unsigned delta2_growth_limit = 8;

    // Exact state-language containment strengthens the semantic order when it
    // is cheap.  Larger SCCs and exhausted budgets automatically fall back to
    // simulation + formula-annotation approximation.
    unsigned exact_state_lang_scc_limit = 8;
    unsigned exact_union_cover_limit = 4;
    unsigned exact_containment_budget = 64;

    unsigned verbose = 0;
  };

  struct ltl2dela_stats
  {
    unsigned direct_formula_components = 0;
    unsigned deterministic_buchi_components = 0;
    unsigned elevator_components = 0;
    unsigned hard_buchi_components = 0;
    unsigned profile_splits = 0;
    unsigned profile_leaves = 0;
    unsigned deterministic_fallbacks = 0;
    unsigned delta2_rewrites = 0;
    unsigned recurrence_rewrites = 0;
    unsigned recurrence_splits = 0;
    unsigned flat_until_monitors = 0;
    unsigned master_profile_bundles = 0;
    unsigned master_profile_splits = 0;
    unsigned master_profile_facts = 0;
    unsigned syntactic_profile_splits = 0;
    unsigned profile_context_rewrites = 0;
    unsigned annotated_na_states = 0;
    unsigned buchi_attempts = 0;

    unsigned long long buchi_states_examined = 0;
    unsigned max_na_scc_states = 0;

    void print(std::ostream& out) const;
  };

  /// Profile-guided LTL -> deterministic Emerson-Lei translation.
  ///
  /// The translator follows three tiers:
  ///   1. compile syntactically easy and Boolean components deterministically;
  ///   2. try a small Buchi automaton and accept it only when its SCCs are
  ///      elevator (nonaccepting, inherently weak, or deterministic accepting);
  ///   3. refine hard residuals using asymptotic profiles
  ///          FG(gamma)  vs.  GF(!gamma)
  ///      chosen by looking at the SCC structure of the two resulting BAs.
  ///
  /// If bounded profile refinement cannot remove all nondeterministic
  /// accepting SCCs, translation falls back to Spot's deterministic generic
  /// LTL translation for that residual only.  Therefore the procedure is total.
  class ltl2dela_translator
  {
  public:
    explicit ltl2dela_translator(
      spot::bdd_dict_ptr dict = spot::make_bdd_dict(),
      ltl2dela_options options = {});

    spot::twa_graph_ptr run(spot::formula f);

    const ltl2dela_stats& stats() const
    {
      return stats_;
    }

    bool delta2_available() const;

  private:
    struct hardness
    {
      bool elevator = false;
      unsigned na_sccs = 0;
      unsigned na_states = 0;
      unsigned max_na_states = 0;
      unsigned states = 0;
    };

    struct separator
    {
      spot::formula guard;
      unsigned priority = 0;
    };

    struct profile_fact
    {
      spot::formula guard;
      // true  => FG guard, so G guard is eventually permanently true.
      // false => GF !guard, so G guard is false at every position.
      bool stable = true;
    };

    struct separator_eval
    {
      bool valid = false;
      separator sep;
      unsigned easy_branches = 0;
      unsigned worst_na_states = 0;
      unsigned total_na_states = 0;
      unsigned total_states = 0;
      unsigned guard_length = 0;
    };

    spot::twa_graph_ptr compile(
      spot::formula f,
      unsigned depth,
      const std::vector<spot::formula>& used,
      bool allow_boolean_split,
      const std::vector<profile_fact>& profile = {});

    spot::twa_graph_ptr compile_master_bundle(
      spot::formula f,
      unsigned depth,
      const std::vector<spot::formula>& used,
      bool& handled,
      const std::vector<profile_fact>& inherited_profile);

    bool match_fg(spot::formula f, spot::formula& body) const;
    bool match_gf_not(spot::formula f, spot::formula& guard) const;
    spot::formula rewrite_recurrence_with_profile(
      spot::formula body,
      const std::vector<profile_fact>& profile) const;
    bool choose_syntactic_profile(
      spot::formula f,
      const std::vector<spot::formula>& used,
      spot::formula& guard) const;
    spot::formula rewrite_formula_with_profile(
      spot::formula f,
      const std::vector<profile_fact>& profile) const;
    spot::formula find_master_separator(
      spot::formula f,
      const std::vector<spot::formula>& used,
      const std::vector<profile_fact>& profile) const;

    void collect_nu_subformulas(
      spot::formula f,
      std::vector<spot::formula>& out) const;
    bool nu_profile_value(
      spot::formula nu,
      const std::vector<profile_fact>& profile,
      bool& stable) const;
    spot::formula advice_mu(
      spot::formula f,
      const std::vector<spot::formula>& y) const;
    void add_profile_fact(std::vector<profile_fact>& profile,
                          spot::formula guard,
                          bool stable) const;

    spot::formula prepare(spot::formula f);
    bool is_direct_fragment(spot::formula f) const;

    // Exact recurrence identities and small deterministic monitors are tried
    // before Delta2 normalization, while the useful GF(mu) syntax is still
    // visible.
    spot::twa_graph_ptr compile_recurrence(
      spot::formula f,
      unsigned depth,
      const std::vector<spot::formula>& used,
      bool& handled,
      const std::vector<profile_fact>& profile);

    bool match_gf(spot::formula f, spot::formula& body) const;
    bool match_flat_until(spot::formula body,
                          spot::formula& lambda,
                          spot::formula& guard,
                          spot::formula& goal) const;
    spot::twa_graph_ptr make_flat_until_monitor(
      spot::formula lambda,
      spot::formula guard,
      spot::formula goal);

    spot::twa_graph_ptr translate_deterministic(spot::formula f);
    spot::twa_graph_ptr translate_buchi(spot::formula f);
    spot::twa_graph_ptr normalize_deterministic(spot::twa_graph_ptr aut);

    spot::twa_graph_ptr compose(const spot::twa_graph_ptr& left,
                                const spot::twa_graph_ptr& right,
                                bool disjunction);

    hardness analyze(const spot::twa_graph_ptr& aut);
    std::vector<separator> collect_separators(spot::formula f) const;
    std::vector<separator> collect_annotation_separators(
      const spot::twa_graph_ptr& aut,
      spot::formula source,
      const hardness& h);
    separator_eval choose_separator(
      spot::formula f,
      const spot::twa_graph_ptr& baseline_aut,
      const hardness& baseline,
      const std::vector<spot::formula>& used);

    std::pair<spot::formula, spot::formula>
    profile_split(spot::formula f, spot::formula guard);

    bool was_used(spot::formula guard,
                  const std::vector<spot::formula>& used) const;

    bool better(const separator_eval& a, const separator_eval& b) const;
    bool makes_progress(const separator_eval& e,
                        const hardness& baseline) const;

    spot::option_map make_cola_options() const;

  private:
    spot::bdd_dict_ptr dict_;
    ltl2dela_options options_;
    spot::tl_simplifier simplifier_;
    spot::option_map cola_options_;
    ltl2dela_stats stats_;
  };
}
