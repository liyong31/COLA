// Copyright (C) 2026  The COLA Authors
//
// Profile-guided LTL -> deterministic Emerson-Lei translation.

#include "ltl2dela.hpp"

#include <spot/tl/print.hh>
#include <spot/tl/delta2.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/matchstates.hh>

#include <algorithm>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <tuple>
#include <utility>

namespace cola
{
  namespace
  {
    static unsigned
    formula_length(spot::formula f)
    {
      std::ostringstream os;
      os << f;
      return static_cast<unsigned>(os.str().size());
    }

    static bool
    formula_less(spot::formula a, spot::formula b)
    {
      if (formula_length(a) != formula_length(b))
        return formula_length(a) < formula_length(b);
      std::ostringstream oa;
      std::ostringstream ob;
      oa << a;
      ob << b;
      return oa.str() < ob.str();
    }
  }

  void
  ltl2dela_stats::print(std::ostream& out) const
  {
    out << "ltl2dela statistics:\n"
        << "  direct formula components: " << direct_formula_components << '\n'
        << "  Buchi attempts: " << buchi_attempts << '\n'
        << "  elevator components: " << elevator_components << '\n'
        << "  hard Buchi components: " << hard_buchi_components << '\n'
        << "  profile splits: " << profile_splits << '\n'
        << "  profile leaves: " << profile_leaves << '\n'
        << "  deterministic fallbacks: " << deterministic_fallbacks << '\n'
        << "  Delta2 rewrites: " << delta2_rewrites << '\n'
        << "  annotated NA states: " << annotated_na_states << '\n'
        << "  Buchi states examined: " << buchi_states_examined << '\n'
        << "  largest NA SCC: " << max_na_scc_states << '\n';
  }

  ltl2dela_translator::ltl2dela_translator(spot::bdd_dict_ptr dict,
                                           ltl2dela_options options)
    : dict_(std::move(dict)),
      options_(options),
      simplifier_(dict_),
      cola_options_(make_cola_options())
  {
  }

  bool
  ltl2dela_translator::delta2_available() const
  {
    return true;
  }

  spot::option_map
  ltl2dela_translator::make_cola_options() const
  {
    spot::option_map om;
    om.set(USE_SIMULATION, 1);
    om.set(USE_SCC_INFO, 1);
    om.set(USE_STUTTER, 1);
    om.set(USE_UNAMBIGUITY, 0);
    om.set(USE_DELAYED_SIMULATION, 0);
    om.set(MORE_ACC_EDGES, 0);
    om.set(NUM_TRANS_PRUNING, 512);
    om.set(MSTATE_REARRANGE, 0);
    om.set(VERBOSE_LEVEL, options_.verbose >= 3 ? 1 : 0);
    om.set(SCC_REACH_MEMORY_LIMIT, 0);
    om.set(NUM_SCC_LIMIT_MERGER, 0);
    om.set(MAX_NUM_SIMULATION, std::numeric_limits<int>::max());
    om.set(USE_FORMULA_ANNOTATIONS, options_.use_state_annotations ? 1 : 0);
    om.set(USE_EXACT_STATE_LANGUAGES,
           options_.use_exact_state_languages ? 1 : 0);
    om.set(EXACT_STATE_LANG_SCC_LIMIT,
           static_cast<int>(options_.exact_state_lang_scc_limit));
    om.set(EXACT_CONTAINMENT_BUDGET,
           static_cast<int>(options_.exact_containment_budget));
    return om;
  }

  spot::formula
  ltl2dela_translator::prepare(spot::formula f)
  {
    // Spot's simplifier is semantics preserving and already performs many
    // pure-eventuality / purely-universal rewrites useful before profiling.
    f = simplifier_.simplify(f);

    // Spot implements the Esparza-Rubio-Sickert Delta2 normalization.
    // Keep the normalized formula only when it is not excessively larger:
    // Delta2 is used here as an SCC-shaping rewrite, not as a mandatory
    // normal form.
    if (options_.use_delta2
        && formula_length(f) <= options_.delta2_input_limit
        && !f.is_delta2())
      {
        auto d = spot::to_delta2(f, &simplifier_);
        unsigned old_len = formula_length(f);
        unsigned new_len = formula_length(d);
        if (new_len <= options_.delta2_growth_limit * std::max(1U, old_len))
          {
            ++stats_.delta2_rewrites;
            f = simplifier_.simplify(d);
          }
      }
    return f;
  }

  bool
  ltl2dela_translator::is_direct_fragment(spot::formula f) const
  {
    // These classes are precisely the kind of formulas for which Spot has
    // specialized deterministic constructions or particularly cheap generic
    // deterministic translations.
    return f.is_syntactic_safety()
      || f.is_syntactic_guarantee()
      || f.is_syntactic_obligation()
      || f.is_syntactic_recurrence()
      || f.is_syntactic_persistence();
  }

  spot::twa_graph_ptr
  ltl2dela_translator::translate_deterministic(spot::formula f)
  {
    spot::translator trans(dict_);
    trans.set_type(spot::postprocessor::Generic);
    trans.set_pref(spot::postprocessor::Deterministic);
    trans.set_level(spot::postprocessor::Low);
    return trans.run(f);
  }

  spot::twa_graph_ptr
  ltl2dela_translator::translate_buchi(spot::formula f)
  {
    ++stats_.buchi_attempts;
    spot::translator trans(dict_);
    trans.set_type(spot::postprocessor::Buchi);
    trans.set_pref(spot::postprocessor::Small);
    trans.set_level(spot::postprocessor::Low);
    auto aut = trans.run(f);
    stats_.buchi_states_examined += aut->num_states();
    return aut;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::normalize_deterministic(spot::twa_graph_ptr aut)
  {
    spot::simplify_acceptance_here(aut);
    spot::postprocessor p;
    p.set_type(spot::postprocessor::Generic);
    p.set_pref(spot::postprocessor::Deterministic);
    p.set_level(spot::postprocessor::Low);
    return p.run(aut);
  }

  spot::twa_graph_ptr
  ltl2dela_translator::compose(const spot::twa_graph_ptr& left,
                               const spot::twa_graph_ptr& right,
                               bool disjunction)
  {
    spot::twa_graph_ptr res = disjunction
      ? spot::product_or(left, right)
      : spot::product(left, right);
    return normalize_deterministic(res);
  }

  ltl2dela_translator::hardness
  ltl2dela_translator::analyze(const spot::twa_graph_ptr& aut)
  {
    hardness h;
    h.states = aut->num_states();

    spot::scc_info si(aut, spot::scc_info_options::ALL);
    std::string types = cola::get_scc_types(si);

    for (unsigned sc = 0; sc < si.scc_count(); ++sc)
      {
        if (cola::is_accepting_nondetscc(types, sc))
          {
            ++h.na_sccs;
            unsigned n = static_cast<unsigned>(si.states_of(sc).size());
            h.na_states += n;
            h.max_na_states = std::max(h.max_na_states, n);
          }
      }

    h.elevator = (h.na_sccs == 0) && cola::is_elevator_automaton(si, types);
    stats_.max_na_scc_states =
      std::max(stats_.max_na_scc_states, h.max_na_states);
    return h;
  }

  std::vector<ltl2dela_translator::separator>
  ltl2dela_translator::collect_separators(spot::formula f) const
  {
    std::vector<separator> out;

    auto add = [&](spot::formula g, unsigned priority)
      {
        if (g.is_tt() || g.is_ff())
          return;
        if (formula_length(g) > options_.profile_guard_max_length)
          return;
        for (const auto& e: out)
          if (e.guard == g)
            return;
        out.push_back({g, priority});
      };

    f.traverse([&](spot::formula sf)
      {
        // The body of an explicit G is the primary Master-Theorem-style
        // asymptotic commitment candidate.
        if (sf.is(spot::op::G) && sf.size() == 1)
          add(sf[0], 100);

        // For a recurrent strong-until / strong-release choice, persistence
        // of the left guard often determines whether the obligation collapses
        // to an eventuality after the commitment point.
        if ((sf.is(spot::op::U) || sf.is(spot::op::M)) && sf.size() == 2)
          add(sf[0], 85);

        // For weak-until/release, the right side is the natural invariant-like
        // guard.  Splitting on it is always sound even when it is not useful.
        if ((sf.is(spot::op::W) || sf.is(spot::op::R)) && sf.size() == 2)
          add(sf[1], 75);

        // Existing persistence/safety subformulas are useful fallback profile
        // predicates, but receive lower priority to control branching.
        if (sf != f && (sf.is_syntactic_persistence()
                        || sf.is_syntactic_safety()))
          add(sf, 50);

        return false;
      });

    std::stable_sort(out.begin(), out.end(),
      [](const separator& a, const separator& b)
      {
        if (a.priority != b.priority)
          return a.priority > b.priority;
        return formula_less(a.guard, b.guard);
      });

    if (out.size() > options_.profile_lookahead)
      out.resize(options_.profile_lookahead);
    return out;
  }

  std::pair<spot::formula, spot::formula>
  ltl2dela_translator::profile_split(spot::formula f, spot::formula guard)
  {
    // Exhaustive asymptotic dichotomy:
    //
    //   FG guard  OR  GF !guard
    //
    // is valid on every infinite word.  Therefore
    //
    //   f == (f & FG guard) | (f & GF !guard).
    //
    // The first branch commits to a stabilization profile, while the second
    // records that the negated guard occurs infinitely often.
    auto stable =
      spot::formula::F(spot::formula::G(guard));
    auto recurring_not =
      spot::formula::G(
        spot::formula::F(spot::formula::Not(guard)));

    return {
      prepare(spot::formula::And({f, stable})),
      prepare(spot::formula::And({f, recurring_not}))
    };
  }


  std::vector<ltl2dela_translator::separator>
  ltl2dela_translator::collect_annotation_separators(
    const spot::twa_graph_ptr& aut,
    spot::formula source,
    const hardness&)
  {
    std::vector<separator> out;
    if (!options_.use_state_annotations)
      return out;

    // match_states() is sound in the direction we need: when source
    // over-approximates L(aut), every word accepted from state q satisfies
    // annotations[q].  The annotation itself may be an over-approximation,
    // so it is used only to propose asymptotic separators, never to prune.
    auto annotations = spot::match_states(aut, source);
    if (annotations.size() != aut->num_states())
      return out;

    spot::scc_info si(aut, spot::scc_info_options::ALL);
    std::string types = cola::get_scc_types(si);

    auto add = [&](spot::formula g, unsigned priority)
      {
        if (g.is_tt() || g.is_ff())
          return;
        if (formula_length(g) > options_.profile_guard_max_length)
          return;
        for (const auto& e: out)
          if (e.guard == g)
            return;
        out.push_back({g, priority});
      };

    for (unsigned sc = 0; sc < si.scc_count(); ++sc)
      {
        if (!cola::is_accepting_nondetscc(types, sc))
          continue;
        for (unsigned s: si.states_of(sc))
          {
            ++stats_.annotated_na_states;
            spot::formula ann = annotations[s];
            ann.traverse([&](spot::formula sf)
              {
                if (sf.is(spot::op::G) && sf.size() == 1)
                  add(sf[0], 120);
                if ((sf.is(spot::op::U) || sf.is(spot::op::M))
                    && sf.size() == 2)
                  add(sf[0], 105);
                if ((sf.is(spot::op::W) || sf.is(spot::op::R))
                    && sf.size() == 2)
                  add(sf[1], 95);
                if (sf != ann
                    && (sf.is_syntactic_persistence()
                        || sf.is_syntactic_safety()))
                  add(sf, 70);
                return false;
              });
          }
      }

    std::stable_sort(out.begin(), out.end(),
      [](const separator& a, const separator& b)
      {
        if (a.priority != b.priority)
          return a.priority > b.priority;
        return formula_less(a.guard, b.guard);
      });
    if (out.size() > options_.profile_lookahead)
      out.resize(options_.profile_lookahead);
    return out;
  }

  bool
  ltl2dela_translator::was_used(
    spot::formula guard,
    const std::vector<spot::formula>& used) const
  {
    return std::find(used.begin(), used.end(), guard) != used.end();
  }

  bool
  ltl2dela_translator::better(const separator_eval& a,
                              const separator_eval& b) const
  {
    if (!a.valid)
      return false;
    if (!b.valid)
      return true;

    // Lexicographic objective:
    //   1. make more branches elevator immediately;
    //   2. minimize the largest remaining NA state mass;
    //   3. minimize total NA state mass;
    //   4. minimize total BA size;
    //   5. prefer shorter guards.
    return std::make_tuple(
             static_cast<int>(-a.easy_branches),
             a.worst_na_states,
             a.total_na_states,
             a.total_states,
             a.guard_length)
         < std::make_tuple(
             static_cast<int>(-b.easy_branches),
             b.worst_na_states,
             b.total_na_states,
             b.total_states,
             b.guard_length);
  }

  bool
  ltl2dela_translator::makes_progress(const separator_eval& e,
                                      const hardness& baseline) const
  {
    if (!e.valid)
      return false;
    if (e.easy_branches > 0)
      return true;
    if (e.worst_na_states < baseline.na_states)
      return true;
    return e.total_na_states < 2U * baseline.na_states;
  }

  ltl2dela_translator::separator_eval
  ltl2dela_translator::choose_separator(
    spot::formula f,
    const spot::twa_graph_ptr& baseline_aut,
    const hardness& baseline,
    const std::vector<spot::formula>& used)
  {
    separator_eval best;

    auto candidates = collect_annotation_separators(baseline_aut, f, baseline);
    auto syntactic = collect_separators(f);
    for (const auto& s: syntactic)
      {
        bool found = false;
        for (const auto& e: candidates)
          if (e.guard == s.guard)
            { found = true; break; }
        if (!found)
          candidates.push_back(s);
      }
    std::stable_sort(candidates.begin(), candidates.end(),
      [](const separator& a, const separator& b)
      {
        if (a.priority != b.priority)
          return a.priority > b.priority;
        return formula_less(a.guard, b.guard);
      });
    if (candidates.size() > options_.profile_lookahead)
      candidates.resize(options_.profile_lookahead);

    for (const auto& sep: candidates)
      {
        if (was_used(sep.guard, used))
          continue;

        auto branches = profile_split(f, sep.guard);
        auto a0 = translate_buchi(branches.first);
        auto a1 = translate_buchi(branches.second);
        auto h0 = analyze(a0);
        auto h1 = analyze(a1);

        separator_eval cur;
        cur.valid = true;
        cur.sep = sep;
        cur.easy_branches =
          static_cast<unsigned>(h0.elevator)
          + static_cast<unsigned>(h1.elevator);
        cur.worst_na_states = std::max(h0.na_states, h1.na_states);
        cur.total_na_states = h0.na_states + h1.na_states;
        cur.total_states = h0.states + h1.states;
        cur.guard_length = formula_length(sep.guard);

        if ((!options_.require_profile_progress
             || makes_progress(cur, baseline))
            && better(cur, best))
          best = cur;
      }

    return best;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::compile(
    spot::formula f,
    unsigned depth,
    const std::vector<spot::formula>& used,
    bool allow_boolean_split)
  {
    f = prepare(f);

    // Boolean decomposition is safe because the deterministic results are
    // combined directly with Emerson-Lei acceptance instead of first forcing
    // their conjunction/disjunction through a monolithic Buchi automaton.
    if (allow_boolean_split && options_.boolean_decomposition
        && (f.is(spot::op::And) || f.is(spot::op::Or))
        && f.size() > 1)
      {
        bool disjunction = f.is(spot::op::Or);
        auto res = compile(f[0], depth, used, true);
        for (unsigned i = 1; i < f.size(); ++i)
          res = compose(res, compile(f[i], depth, used, true), disjunction);
        return res;
      }

    // Spot first: exploit its specialized translations for known easy
    // fragments instead of forcing them through Buchi.
    if (is_direct_fragment(f))
      {
        ++stats_.direct_formula_components;
        return normalize_deterministic(translate_deterministic(f));
      }

    // Try the small-Buchi route.  We only use CoLA's local elevator
    // determinizer if the generated SCC structure is certified suitable.
    auto ba = translate_buchi(f);
    auto h = analyze(ba);
    if (h.elevator)
      {
        ++stats_.elevator_components;
        if (options_.use_state_annotations)
          return normalize_deterministic(
            cola::determinize_televator(ba, cola_options_, f));
        return normalize_deterministic(
          cola::determinize_televator(ba, cola_options_));
      }

    ++stats_.hard_buchi_components;

    // Refine only difficult residuals.  Note that recursive profile branches
    // are not Boolean-decomposed at their top level: doing so would throw away
    // the stabilizing context we just introduced.
    if (options_.use_profiles
        && depth < options_.profile_depth
        && stats_.profile_splits < options_.profile_budget)
      {
        auto choice = choose_separator(f, ba, h, used);
        if (choice.valid)
          {
            ++stats_.profile_splits;
            auto branches = profile_split(f, choice.sep.guard);
            auto next_used = used;
            next_used.push_back(choice.sep.guard);

            if (options_.verbose >= 1)
              std::cerr << "ltl2dela: profile split on "
                        << choice.sep.guard
                        << " (NA states " << h.na_states
                        << " -> worst " << choice.worst_na_states
                        << ")\n";

            auto left = compile(branches.first, depth + 1,
                                next_used, false);
            auto right = compile(branches.second, depth + 1,
                                 next_used, false);
            ++stats_.profile_leaves;
            return compose(left, right, true);
          }
      }

    // Total, Safra-free-at-the-LTL-level fallback: ask Spot to translate this
    // residual formula directly to a deterministic generic automaton.  This
    // intentionally avoids determinizing the hard BA we just inspected.
    ++stats_.deterministic_fallbacks;
    if (options_.verbose >= 1)
      std::cerr << "ltl2dela: deterministic formula fallback for "
                << f << '\n';
    return normalize_deterministic(translate_deterministic(f));
  }

  spot::twa_graph_ptr
  ltl2dela_translator::run(spot::formula f)
  {
    if (!f.is_ltl_formula())
      throw std::runtime_error("ltl2dela requires an LTL formula");

    stats_ = {};
    std::vector<spot::formula> used;
    return compile(prepare(f), 0, used, true);
  }
}
