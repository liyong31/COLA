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
#include <spot/twa/formula2bdd.hh>
#include <spot/twa/twagraph.hh>

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
        << "  recurrence rewrites: " << recurrence_rewrites << '\n'
        << "  recurrence splits: " << recurrence_splits << '\n'
        << "  flat-Until monitors: " << flat_until_monitors << '\n'
        << "  Master profile bundles: " << master_profile_bundles << '\n'
        << "  Master profile splits: " << master_profile_splits << '\n'
        << "  Master profile facts: " << master_profile_facts << '\n'
        << "  syntactic profile splits: " << syntactic_profile_splits << '\n'
        << "  profile-context rewrites: " << profile_context_rewrites << '\n'
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
    om.set(EXACT_UNION_COVER_LIMIT,
           static_cast<int>(options_.exact_union_cover_limit));
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
  ltl2dela_translator::match_fg(spot::formula f, spot::formula& body) const
  {
    if (!f.is(spot::op::F) || f.size() != 1)
      return false;
    auto x = f[0];
    if (!x.is(spot::op::G) || x.size() != 1)
      return false;
    body = x[0];
    return true;
  }

  bool
  ltl2dela_translator::match_gf_not(spot::formula f,
                                    spot::formula& guard) const
  {
    spot::formula body;
    if (!match_gf(f, body))
      return false;
    if (!body.is(spot::op::Not) || body.size() != 1)
      return false;
    guard = body[0];
    return true;
  }

  bool
  ltl2dela_translator::choose_syntactic_profile(
    spot::formula f,
    const std::vector<spot::formula>& used,
    spot::formula& guard) const
  {
    struct candidate
    {
      spot::formula guard;
      unsigned occurrences = 0;
      unsigned length = 0;
    };

    std::vector<candidate> candidates;
    auto add = [&](spot::formula g)
      {
        if (g.is_tt() || g.is_ff()
            || was_used(g, used)
            || formula_length(g) > options_.profile_guard_max_length)
          return;
        for (auto& c: candidates)
          if (c.guard == g)
            {
              ++c.occurrences;
              return;
            }
        candidates.push_back({g, 1U, formula_length(g)});
      };

    // Only inspect G-obligations that occur inside a recurrent GF kernel.
    // Those are precisely the commitments whose eventual truth value can
    // simplify all sufficiently late witnesses of the outer recurrence.
    f.traverse([&](spot::formula sf)
      {
        spot::formula body;
        if (!match_gf(sf, body))
          return false;

        body.traverse([&](spot::formula x)
          {
            if (x.is(spot::op::G) && x.size() == 1)
              add(x[0]);
            return false;
          });
        return false;
      });

    if (candidates.empty())
      return false;

    // Prefer predicates that occur in several recurrent kernels; ties go to
    // shorter guards to keep the profile monitors small.
    std::stable_sort(candidates.begin(), candidates.end(),
      [](const candidate& a, const candidate& b)
      {
        if (a.occurrences != b.occurrences)
          return a.occurrences > b.occurrences;
        return a.length < b.length;
      });

    guard = candidates.front().guard;
    return true;
  }

  void
  ltl2dela_translator::add_profile_fact(
    std::vector<profile_fact>& profile,
    spot::formula guard,
    bool stable) const
  {
    for (const auto& p: profile)
      if (p.guard == guard && p.stable == stable)
        return;
    profile.push_back({guard, stable});
  }

  spot::formula
  ltl2dela_translator::rewrite_recurrence_with_profile(
    spot::formula in,
    const std::vector<profile_fact>& profile) const
  {
    for (const auto& p: profile)
      {
        auto gg = spot::formula::G(p.guard);
        if (in == gg)
          return p.stable ? spot::formula::tt() : spot::formula::ff();

        // Under FG(gamma), F(gamma) is eventually always true.
        if (p.stable && in == spot::formula::F(p.guard))
          return spot::formula::tt();

        // Under GF(!gamma), every suffix contains a !gamma-position.
        if (!p.stable
            && in == spot::formula::F(spot::formula::Not(p.guard)))
          return spot::formula::tt();
      }

    return in.map([&](spot::formula child)
      {
        return rewrite_recurrence_with_profile(child, profile);
      });
  }



  spot::formula
  ltl2dela_translator::rewrite_formula_with_profile(
    spot::formula f,
    const std::vector<profile_fact>& profile) const
  {
    spot::formula body;
    if (match_gf(f, body))
      {
        auto r = rewrite_recurrence_with_profile(body, profile);
        if (r != body)
          return spot::formula::G(spot::formula::F(r));
      }

    return f.map([&](spot::formula child)
      {
        return rewrite_formula_with_profile(child, profile);
      });
  }

  spot::formula
  ltl2dela_translator::find_master_separator(
    spot::formula f,
    const std::vector<spot::formula>& used,
    const std::vector<profile_fact>& profile) const
  {
    spot::formula chosen = spot::formula::ff();
    bool found = false;

    auto already_known = [&](spot::formula g)
      {
        for (const auto& p: profile)
          if (p.guard == g)
            return true;
        return was_used(g, used);
      };

    // Search only inside a GF obligation.  This is the exact place where the
    // Master-Theorem advice is intended to simplify recurrent behavior.
    spot::formula gf_body;
    if (match_gf(f, gf_body))
      {
        gf_body.traverse([&](spot::formula sf)
          {
            if (found)
              return true;
            if (sf.is(spot::op::G) && sf.size() == 1)
              {
                auto g = sf[0];
                if (!g.is_tt() && !g.is_ff()
                    && !already_known(g)
                    && formula_length(g) <= options_.profile_guard_max_length)
                  {
                    chosen = g;
                    found = true;
                    return true;
                  }
              }
            return false;
          });
        if (found)
          return chosen;
      }

    // Recurse structurally to find the first recurrent component containing a
    // still-unresolved G-obligation.  The recursion is syntactic and bounded
    // by the ordinary profile depth/budget in compile().
    for (unsigned i = 0; i < f.size(); ++i)
      {
        auto g = find_master_separator(f[i], used, profile);
        if (!g.is_ff())
          return g;
      }
    return chosen;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::compile_master_bundle(
    spot::formula f,
    unsigned depth,
    const std::vector<spot::formula>& used,
    bool& handled,
    const std::vector<profile_fact>& inherited_profile)
  {
    handled = false;
    if (!options_.use_master_profiles
        || !f.is(spot::op::And)
        || f.size() < 2)
      return nullptr;

    auto profile = inherited_profile;
    unsigned recurrence_terms = 0;
    unsigned facts_before = static_cast<unsigned>(profile.size());

    // First collect the asymptotic facts so every conjunct is compiled under
    // the same profile, independent of its syntactic position.
    for (unsigned i = 0; i < f.size(); ++i)
      {
        spot::formula g;
        if (match_fg(f[i], g))
          add_profile_fact(profile, g, true);
        else if (match_gf_not(f[i], g))
          add_profile_fact(profile, g, false);

        spot::formula body;
        if (match_gf(f[i], body))
          ++recurrence_terms;
      }

    unsigned new_facts =
      static_cast<unsigned>(profile.size()) - facts_before;

    // This is the exact post-commitment shape we can exploit already:
    // conjunctions containing recurrence obligations and/or explicit
    // asymptotic profile facts.  Splitting here is intentionally before
    // Delta2 normalization.
    if (recurrence_terms == 0 && new_facts == 0
        && inherited_profile.empty())
      return nullptr;

    handled = true;
    ++stats_.master_profile_bundles;
    stats_.master_profile_facts += new_facts;

    if (options_.verbose >= 2 && new_facts)
      {
        std::cerr << "ltl2dela: Master profile facts:";
        for (unsigned i = facts_before; i < profile.size(); ++i)
          std::cerr << ' ' << (profile[i].stable ? "FG(" : "GF!(")
                    << profile[i].guard << ')';
        std::cerr << '\n';
      }

    // Compile all obligations independently but under the same asymptotic
    // context.  The conjunction with the explicit FG/GF profile monitors
    // makes every conditional recurrence rewrite globally sound.
    auto res = compile(f[0], depth, used, true, profile);
    for (unsigned i = 1; i < f.size(); ++i)
      res = compose(res, compile(f[i], depth, used, true, profile), false);
    return res;
  }

  bool
  ltl2dela_translator::match_gf(spot::formula f, spot::formula& body) const
  {
    if (!f.is(spot::op::G) || f.size() != 1)
      return false;
    auto x = f[0];
    if (!x.is(spot::op::F) || x.size() != 1)
      return false;
    body = x[0];
    return true;
  }

  bool
  ltl2dela_translator::match_flat_until(spot::formula body,
                                        spot::formula& lambda,
                                        spot::formula& guard,
                                        spot::formula& goal) const
  {
    if (!body.is(spot::op::And) || body.size() < 2)
      return false;

    int until = -1;
    std::vector<spot::formula> local;
    for (unsigned i = 0; i < body.size(); ++i)
      {
        auto x = body[i];
        if ((x.is(spot::op::U) || x.is(spot::op::M))
            && x.size() == 2
            && x[0].is_boolean() && x[1].is_boolean())
          {
            if (until >= 0)
              return false;
            until = static_cast<int>(i);
            if (x.is(spot::op::U))
              {
                guard = x[0];
                goal = x[1];
              }
            else
              {
                // alpha M beta == beta U (alpha & beta)
                guard = x[1];
                goal = spot::formula::And({x[0], x[1]});
              }
          }
        else
          {
            if (!x.is_boolean())
              return false;
            local.push_back(x);
          }
      }

    if (until < 0 || local.empty())
      return false;

    lambda = local.size() == 1
      ? local.front()
      : spot::formula::And(local);
    return lambda.is_boolean();
  }

  spot::twa_graph_ptr
  ltl2dela_translator::make_flat_until_monitor(spot::formula lambda,
                                                spot::formula guard,
                                                spot::formula goal)
  {
    // Recognizes GF(lambda & (guard U goal)).
    //
    // State 0: no still-live witness started at a previous lambda-position.
    // State 1: one such witness is pending and guard has held at every
    //          position since it was started.
    //
    // On the current letter a witness succeeds iff
    //   goal & (lambda | pending).
    // If it does not succeed, the pending bit becomes
    //   guard & (lambda | pending).
    //
    // This is deterministic and complete, and an accepting transition is
    // taken exactly whenever a finite witness for lambda & (guard U goal)
    // finishes.  Buchi acceptance therefore gives precisely GF of the body.
    auto aut = spot::make_twa_graph(dict_);
    aut->new_states(2);
    aut->set_init_state(0);
    aut->set_buchi();

    bdd l = spot::formula_to_bdd(lambda, dict_, aut);
    bdd g = spot::formula_to_bdd(guard, dict_, aut);
    bdd h = spot::formula_to_bdd(goal, dict_, aut);
    aut->register_aps_from_dict();

    auto accepting_edge = [&](unsigned src, unsigned dst, bdd cond)
      {
        if (cond == bddfalse)
          return;
        unsigned e = aut->new_edge(src, dst, cond);
        aut->edge_storage(e).acc.set(0);
      };
    auto plain_edge = [&](unsigned src, unsigned dst, bdd cond)
      {
        if (cond != bddfalse)
          aut->new_edge(src, dst, cond);
      };

    // pending = 0
    bdd success0 = h & l;
    bdd wait0 = (-h) & g & l;
    accepting_edge(0, 0, success0);
    plain_edge(0, 1, wait0);
    plain_edge(0, 0, -(success0 | wait0));

    // pending = 1
    bdd success1 = h;
    bdd wait1 = (-h) & g;
    accepting_edge(1, 0, success1);
    plain_edge(1, 1, wait1);
    plain_edge(1, 0, -(success1 | wait1));

    aut->prop_universal(true);
    aut->prop_complete(true);
    aut->prop_state_acc(false);
    aut->merge_edges();
    return aut;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::compile_recurrence(
    spot::formula f,
    unsigned depth,
    const std::vector<spot::formula>& used,
    bool& handled,
    const std::vector<profile_fact>& profile)
  {
    handled = false;
    spot::formula body;
    if (!match_gf(f, body))
      return nullptr;

    auto gf = [](spot::formula x)
      {
        return spot::formula::G(spot::formula::F(x));
      };

    if (!profile.empty())
      {
        auto rewritten =
          simplifier_.simplify(rewrite_recurrence_with_profile(body, profile));
        if (rewritten != body)
          {
            handled = true;
            ++stats_.profile_context_rewrites;
            return compile(gf(rewritten), depth, used, false, profile);
          }
      }

    // GF X phi = GF phi; GF F phi = GF phi.
    if ((body.is(spot::op::X) || body.is(spot::op::F))
        && body.size() == 1)
      {
        handled = true;
        ++stats_.recurrence_rewrites;
        return compile(gf(body[0]), depth, used, false, profile);
      }

    // GF(G phi) = FG phi.  This is the simplest exact Master-style
    // commitment: infinitely many positions satisfying G phi are equivalent
    // to one suffix from which phi holds forever.
    if (body.is(spot::op::G) && body.size() == 1)
      {
        handled = true;
        ++stats_.recurrence_rewrites;
        auto fg = spot::formula::F(spot::formula::G(body[0]));
        return compile(fg, depth, used, false, profile);
      }

    // GF(alpha U beta) = GF beta.
    if (body.is(spot::op::U) && body.size() == 2)
      {
        handled = true;
        ++stats_.recurrence_rewrites;
        return compile(gf(body[1]), depth, used, false, profile);
      }

    // alpha M beta == beta U (alpha & beta), hence
    // GF(alpha M beta) = GF(alpha & beta).
    if (body.is(spot::op::M) && body.size() == 2)
      {
        handled = true;
        ++stats_.recurrence_rewrites;
        return compile(gf(spot::formula::And({body[0], body[1]})),
                       depth, used, false, profile);
      }

    // GF distributes over finite disjunction.  This turns a repeated
    // nondeterministic choice into one deterministic Emerson-Lei OR-product
    // of independently compiled recurrence monitors.
    if (body.is(spot::op::Or) && body.size() > 1)
      {
        handled = true;
        ++stats_.recurrence_splits;
        auto res = compile(gf(body[0]), depth, used, false, profile);
        for (unsigned i = 1; i < body.size(); ++i)
          res = compose(res, compile(gf(body[i]), depth, used, false, profile), true);
        return res;
      }

    // Flat Until kernel:
    //   GF(lambda & (g U h))
    // with propositional lambda,g,h has a two-state deterministic
    // transition-Buchi monitor.  Use it before generic translation.
    spot::formula lambda;
    spot::formula guard;
    spot::formula goal;
    if (match_flat_until(body, lambda, guard, goal))
      {
        handled = true;
        ++stats_.flat_until_monitors;
        return normalize_deterministic(
          make_flat_until_monitor(lambda, guard, goal));
      }

    // GF(lambda & G beta) = GF lambda & FG beta.  More generally all
    // top-level G-conjuncts can be factored out.  This is an exact
    // post-commitment decomposition and directly materializes part of the
    // Master-Theorem Y-profile without enumerating Y.
    if (body.is(spot::op::And) && body.size() > 1)
      {
        std::vector<spot::formula> stable;
        std::vector<spot::formula> rest;
        for (unsigned i = 0; i < body.size(); ++i)
          {
            auto x = body[i];
            if (x.is(spot::op::G) && x.size() == 1)
              stable.push_back(x[0]);
            else
              rest.push_back(x);
          }

        if (!stable.empty())
          {
            handled = true;
            ++stats_.recurrence_splits;
            spot::twa_graph_ptr res;
            bool have = false;

            if (!rest.empty())
              {
                auto rr = rest.size() == 1
                  ? rest.front()
                  : spot::formula::And(rest);
                res = compile(gf(rr), depth, used, false, profile);
                have = true;
              }

            for (auto x: stable)
              {
                auto fg = spot::formula::F(spot::formula::G(x));
                auto next = compile(fg, depth, used, false, profile);
                if (!have)
                  {
                    res = next;
                    have = true;
                  }
                else
                  res = compose(res, next, false);
              }
            return res;
          }
      }

    // GF(lambda & F beta) = GF lambda & GF beta.  More generally, if a
    // conjunction contains several F-obligations, all of them can be peeled
    // off at once.  The identity is exact because GF beta implies that from
    // every position there is a future beta-position.
    if (body.is(spot::op::And) && body.size() > 1)
      {
        std::vector<spot::formula> future;
        std::vector<spot::formula> rest;
        for (unsigned i = 0; i < body.size(); ++i)
          {
            auto x = body[i];
            if (x.is(spot::op::F) && x.size() == 1)
              future.push_back(x[0]);
            else
              rest.push_back(x);
          }

        if (!future.empty())
          {
            handled = true;
            ++stats_.recurrence_splits;

            spot::twa_graph_ptr res;
            bool have = false;

            if (!rest.empty())
              {
                auto r = rest.size() == 1
                  ? rest.front()
                  : spot::formula::And(rest);
                res = compile(gf(r), depth, used, false, profile);
                have = true;
              }

            for (auto x: future)
              {
                auto next = compile(gf(x), depth, used, false, profile);
                if (!have)
                  {
                    res = next;
                    have = true;
                  }
                else
                  res = compose(res, next, false);
              }
            return res;
          }
      }

    return nullptr;
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

    // Keep the raw profile conjunct visible until compile() has had a chance
    // to extract it as a Master-profile fact.  Delta2 normalization happens
    // later, after structural compilation.
    return {
      simplifier_.simplify(spot::formula::And({f, stable})),
      simplifier_.simplify(spot::formula::And({f, recurring_not}))
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
    bool allow_boolean_split,
    const std::vector<profile_fact>& profile)
  {
    // Preserve GF(mu)-style syntax long enough for exact structural
    // recurrence rules and small hand-built deterministic monitors.
    f = simplifier_.simplify(f);

    if (!profile.empty())
      {
        auto rewritten =
          simplifier_.simplify(rewrite_formula_with_profile(f, profile));
        if (rewritten != f)
          {
            ++stats_.profile_context_rewrites;
            f = rewritten;
          }
      }
    if (options_.use_recurrence_compiler)
      {
        bool handled = false;
        auto special = compile_recurrence(f, depth, used, handled, profile);
        if (handled)
          return special;
      }

    // Recognize the post-commitment Master-Theorem shape before Delta2
    // normalization can obscure its individual recurrence obligations.
    if (options_.use_master_profiles)
      {
        bool handled = false;
        auto special =
          compile_master_bundle(f, depth, used, handled, profile);
        if (handled)
          return special;
      }

    // Before building any Buchi automaton, perform the most direct
    // Master-Theorem-style refinement: if a G(gamma) occurs inside a GF
    // obligation, split the language into the exhaustive asymptotic modes
    // FG(gamma) and GF(!gamma).  The profile facts are then available to the
    // recurrence compiler in both branches.
    if (options_.use_master_profiles
        && options_.use_profiles
        && depth < options_.profile_depth
        && stats_.profile_splits < options_.profile_budget)
      {
        auto gamma = find_master_separator(f, used, profile);
        if (gamma)
          {
            ++stats_.profile_splits;
            ++stats_.master_profile_splits;

            auto branches = profile_split(f, gamma);
            auto next_used = used;
            next_used.push_back(gamma);

            auto left_profile = profile;
            auto right_profile = profile;
            add_profile_fact(left_profile, gamma, true);
            add_profile_fact(right_profile, gamma, false);

            if (options_.verbose >= 1)
              std::cerr << "ltl2dela: pre-Buchi Master split on "
                        << gamma << '\n';

            auto left = compile(branches.first, depth + 1,
                                next_used, false, left_profile);
            auto right = compile(branches.second, depth + 1,
                                 next_used, false, right_profile);
            return compose(left, right, true);
          }
      }

    // A remaining nested G inside a GF kernel is a genuine Y-profile
    // candidate.  Split before constructing any Buchi automaton.  The split
    // is exhaustive and therefore correctness-independent from this heuristic.
    if (options_.use_profiles
        && depth < options_.profile_depth
        && stats_.profile_splits < options_.profile_budget)
      {
        spot::formula guard;
        if (choose_syntactic_profile(f, used, guard))
          {
            ++stats_.profile_splits;
            ++stats_.syntactic_profile_splits;

            auto branches = profile_split(f, guard);
            auto next_used = used;
            next_used.push_back(guard);

            auto left_profile = profile;
            auto right_profile = profile;
            add_profile_fact(left_profile, guard, true);
            add_profile_fact(right_profile, guard, false);

            if (options_.verbose >= 1)
              std::cerr << "ltl2dela: syntactic Y-profile split on "
                        << guard << '\n';

            auto left = compile(branches.first, depth + 1,
                                next_used, false, left_profile);
            auto right = compile(branches.second, depth + 1,
                                 next_used, false, right_profile);
            ++stats_.profile_leaves;
            return compose(left, right, true);
          }
      }

    // Only now apply optional Delta2 normalization.
    f = prepare(f);

    // Boolean decomposition is safe because the deterministic results are
    // combined directly with Emerson-Lei acceptance instead of first forcing
    // their conjunction/disjunction through a monolithic Buchi automaton.
    if (allow_boolean_split && options_.boolean_decomposition
        && (f.is(spot::op::And) || f.is(spot::op::Or))
        && f.size() > 1)
      {
        bool disjunction = f.is(spot::op::Or);
        auto res = compile(f[0], depth, used, true, profile);
        for (unsigned i = 1; i < f.size(); ++i)
          res = compose(res, compile(f[i], depth, used, true, profile), disjunction);
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

            auto left_profile = profile;
            auto right_profile = profile;
            add_profile_fact(left_profile, choice.sep.guard, true);
            add_profile_fact(right_profile, choice.sep.guard, false);

            auto left = compile(branches.first, depth + 1,
                                next_used, false, left_profile);
            auto right = compile(branches.second, depth + 1,
                                 next_used, false, right_profile);
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
    // Do not normalize to Delta2 here: compile() must see the original
    // GF/profile syntax before deciding which structural compiler to use.
    return compile(simplifier_.simplify(f), 0, used, true, {});
  }
}
