// Copyright (C) 2026  The COLA Authors
//
// Profile-guided LTL -> deterministic Emerson-Lei translation.

#include "ltl2dela.hpp"
#include "owl_annotations.hpp"
#include "slaa_frontend.hpp"

#include <spot/tl/print.hh>
#include <spot/twaalgos/ltlf2dfa.hh>
#include <spot/tl/delta2.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/gfguarantee.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/matchstates.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twa/twagraph.hh>

#include <algorithm>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <sstream>
#include <stdexcept>
#include <tuple>
#include <utility>

namespace cola
{
  namespace
  {
    // Budget exhaustion abandons the entire construction, never a language
    // branch.  It is deliberately distinct from logic/API errors.
    struct x_advice_limit {};

    // Symbolic af: a disjoint, complete BDD partition of letters, with one
    // residual per region.  Boolean residuals are canonicalized modulo
    // propositional equivalence, treating temporal formulas as opaque atoms.
    // In particular, no temporal simplification may rename an X obligation.
    class symbolic_after
    {
      using formula = spot::formula;
      using partition = std::map<formula, bdd>;
      spot::twa_graph_ptr owner_;
      unsigned limit_;
      std::map<formula, bdd> encoded_;
      std::map<int, formula> atoms_;
      std::map<int, formula> decoded_;
      std::map<formula, partition> after_;

      bdd encode(formula f)
      {
        if (f.is_tt()) return bddtrue;
        if (f.is_ff()) return bddfalse;
        auto old = encoded_.find(f);
        if (old != encoded_.end()) return old->second;
        if (encoded_.size() >= limit_) throw x_advice_limit{};
        bdd res;
        if (f.is(spot::op::And) || f.is(spot::op::Or))
          {
            bool conjunction = f.is(spot::op::And);
            res = conjunction ? bdd(bddtrue) : bdd(bddfalse);
            for (auto c: f)
              res = conjunction ? res & encode(c) : res | encode(c);
          }
        else
          {
            int v = owner_->get_dict()->register_anonymous_variables(1, this);
            atoms_.emplace(v, f);
            res = bdd_ithvar(v);
          }
        encoded_.emplace(f, res);
        return res;
      }

      formula decode(bdd b)
      {
        if (b == bddtrue) return formula::tt();
        if (b == bddfalse) return formula::ff();
        auto old = decoded_.find(b.id());
        if (old != decoded_.end()) return old->second;
        if (decoded_.size() >= limit_) throw x_advice_limit{};
        // All skeletons are positive in their opaque atoms: low implies high.
        // Thus low | (atom & high) is the Shannon expansion without introducing
        // negated temporal operators into the NNF residual.
        auto f = formula::Or({decode(bdd_low(b)),
          formula::And({atoms_.at(bdd_var(b)), decode(bdd_high(b))})});
        decoded_.emplace(b.id(), f);
        return f;
      }

      void add(partition& out, formula f, bdd letters)
      {
        if (letters == bddfalse) return;
        f = canonical(f);
        auto it = out.find(f);
        if (it == out.end()) out.emplace(f, letters);
        else it->second |= letters;
        if (out.size() > limit_) throw x_advice_limit{};
      }

      partition combine(const partition& a, const partition& b, bool is_and)
      {
        partition out;
        for (const auto& x: a)
          for (const auto& y: b)
            {
              auto letters = x.second & y.second;
              if (letters == bddfalse) continue;
              add(out, is_and ? formula::And({x.first, y.first})
                              : formula::Or({x.first, y.first}), letters);
            }
        return out;
      }

    public:
      symbolic_after(spot::twa_graph_ptr owner, unsigned limit)
        : owner_(std::move(owner)), limit_(limit) {}
      ~symbolic_after()
      {
        owner_->get_dict()->unregister_all_my_variables(this);
      }
      symbolic_after(const symbolic_after&) = delete;
      symbolic_after& operator=(const symbolic_after&) = delete;

      formula canonical(formula f) { return decode(encode(f)); }

      const partition& after(formula f)
      {
        auto old = after_.find(f);
        if (old != after_.end()) return old->second;
        if (after_.size() >= limit_) throw x_advice_limit{};
        partition out;
        using op = spot::op;
        if (f.is_boolean())
          {
            bdd letters = spot::formula_to_bdd(f, owner_->get_dict(), owner_);
            add(out, formula::tt(), letters);
            add(out, formula::ff(), !letters);
          }
        else if (f.is(op::X))
          add(out, f[0], bddtrue);
        else if (f.is(op::And) || f.is(op::Or))
          {
            bool is_and = f.is(op::And);
            out.emplace(is_and ? formula::tt() : formula::ff(), bddtrue);
            for (auto c: f) out = combine(out, after(c), is_and);
          }
        else if (f.is(op::F) || f.is(op::G))
          out = combine(after(f[0]), {{f, bddtrue}}, f.is(op::G));
        else if (f.is(op::U) || f.is(op::W))
          out = combine(after(f[1]),
                        combine(after(f[0]), {{f, bddtrue}}, true), false);
        else if (f.is(op::M) || f.is(op::R))
          out = combine(after(f[1]),
                        combine(after(f[0]), {{f, bddtrue}}, false), true);
        else
          throw std::logic_error("symbolic af requires NNF LTL");
        return after_.emplace(f, std::move(out)).first->second;
      }
    };

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

    bool boolean_gf_fg(spot::formula f)
    {
      if (f.is_tt() || f.is_ff()) return true;
      if (f.is(spot::op::And) || f.is(spot::op::Or))
        {
          for (auto c: f) if (!boolean_gf_fg(c)) return false;
          return true;
        }
      if (f.is(spot::op::Not)) return boolean_gf_fg(f[0]);
      return ((f.is(spot::op::G) && f[0].is(spot::op::F))
              || (f.is(spot::op::F) && f[0].is(spot::op::G)))
        && f[0][0].is_boolean();
    }

    bool guarded_conjunction(spot::formula f)
    {
      if (!f.is(spot::op::And)) return false;
      bool safety = false, other = false;
      for (auto c: f) (c.is_syntactic_safety() ? safety : other) = true;
      return safety && other;
    }

    bool no_larger(const spot::twa_graph_ptr& left,
                   const spot::twa_graph_ptr& right)
    {
      auto l = spot::complete(left), r = spot::complete(right);
      return std::make_tuple(l->num_states(), l->num_sets(), l->num_edges())
          <= std::make_tuple(r->num_states(), r->num_sets(), r->num_edges());
    }
  }

  void
  ltl2dela_stats::print(std::ostream& out) const
  {
    out << "ltl2dela statistics:\n"
        << "  direct formula components: " << direct_formula_components << '\n'
        << "  Buchi attempts: " << buchi_attempts << '\n'
        << "  elevator components: " << elevator_components << '\n'
        << "  elevator validation fallbacks: " << elevator_validation_fallbacks << '\n'
        << "  hard Buchi components: " << hard_buchi_components << '\n'
        << "  profile splits: " << profile_splits << '\n'
        << "  profile leaves: " << profile_leaves << '\n'
        << "  deterministic fallbacks: " << deterministic_fallbacks << '\n'
        << "  Delta2 rewrites: " << delta2_rewrites << '\n'
        << "  recurrence rewrites: " << recurrence_rewrites << '\n'
        << "  recurrence splits: " << recurrence_splits << '\n'
        << "  flat-Until monitors: " << flat_until_monitors << '\n'
        << "  finite-witness monitors: " << finite_witness_monitors << '\n'
        << "  finite-witness duals: " << finite_witness_duals << '\n'
        << "  finite-witness aborts: " << finite_witness_aborts << '\n'
        << "  Boolean GF/FG components: " << boolean_gf_fg_components << '\n'
        << "  specialized GF components: " << specialized_gf_components << '\n'
        << "  specialized FG components: " << specialized_fg_components << '\n'
        << "  DBA attempts: " << dba_attempts << '\n'
        << "  DBA components: " << dba_components << '\n'
        << "  DBA candidates constructed: " << dba_candidates << '\n'
        << "  DBA attempts without result: " << dba_fallbacks << '\n'
        << "  guarded conjunctions retained: " << guarded_conjunctions << '\n'
        << "  acceptance-limit fallbacks: " << acceptance_limit_fallbacks << '\n'
        << "  SLAA attempts: " << slaa_attempts << '\n'
        << "  SLAA frontend failures: " << slaa_failures << '\n'
        << "  SLAA non-elevator candidates: " << slaa_non_elevator << '\n'
        << "  SLAA validation failures: " << slaa_validation_failures << '\n'
        << "  SLAA backend attempts: " << slaa_backend_attempts << '\n'
        << "  SLAA candidates: " << slaa_candidates << '\n'
        << "  SLAA components: " << slaa_components << '\n'
        << "  SLAA negative attempts: " << slaa_negative_attempts << '\n'
        << "  SLAA negative candidates: " << slaa_negative_candidates << '\n'
        << "  SLAA negative components: " << slaa_negative_components << '\n'
        << "  SLAA formula candidates: " << slaa_formula_candidates << '\n'
        << "  SLAA formula components: " << slaa_formula_components << '\n'
        << "  SLAA formula failures: " << slaa_formula_failures << '\n'
        << "  colour-choice attempts: " << colour_choice_attempts << '\n'
        << "  colour-choice SCCs rewritten: " << colour_choice_sccs << '\n'
        << "  colour-choice elevator repairs: " << colour_choice_repairs << '\n'
        << "  colour-choice validation failures: " << colour_choice_validation_failures << '\n'
        << "  co-Buchi SCCs weakified: " << cobuchi_weak_sccs << '\n'
        << "  co-Buchi states added: " << cobuchi_weak_states << '\n'
        << "  co-Buchi elevator repairs: " << cobuchi_weak_repairs << '\n'
        << "  co-Buchi validation failures: " << cobuchi_weak_validation_failures << '\n'
        << "  LDGBA attempts: " << ldgba_attempts << '\n'
        << "  LDGBA frontend/construction failures: " << ldgba_failures << '\n'
        << "  LDGBA rejected candidates: " << ldgba_rejected << '\n'
        << "  LDGBA backend attempts: " << ldgba_backend_attempts << '\n'
        << "  LDGBA validation failures: " << ldgba_validation_failures << '\n'
        << "  LDGBA candidates: " << ldgba_candidates << '\n'
        << "  LDGBA annotations certified: " << ldgba_annotations_certified << '\n'
        << "  LDGBA annotations rejected: " << ldgba_annotations_rejected << '\n'
        << "  LDGBA annotation pair proofs: " << ldgba_annotation_pair_proofs << '\n'
        << "  LDGBA annotation union proofs: " << ldgba_annotation_union_proofs << '\n'
        << "  LDGBA cross-SCC proofs: " << ldgba_cross_scc_proofs << '\n'
        << "  LDGBA components: " << ldgba_components << '\n'
        << "  LDGBA cache hits: " << ldgba_cache_hits << '\n'
        << "  LDGBA budget skips: " << ldgba_budget_skips << '\n'
        << "  Master Y-advice rewrites: " << master_advice_rewrites << '\n'
        << "  X-advice components: " << x_advice_components << '\n'
        << "  X-advice profiles: " << x_advice_profiles << '\n'
        << "  X-advice budget fallbacks: " << x_advice_aborts << '\n'
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
        if (p.stable && in == p.guard)
          return spot::formula::tt();

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

        if (in.size() == 2)
          {
            // Once gamma is permanently true:
            //   gamma U beta  == F beta
            //   alpha M gamma == F alpha
            //   gamma W beta  == true
            //   alpha R gamma == true
            if (p.stable)
              {
                if (in.is(spot::op::U) && in[0] == p.guard)
                  return spot::formula::F(
                    rewrite_recurrence_with_profile(in[1], profile));

                if (in.is(spot::op::M) && in[1] == p.guard)
                  return spot::formula::F(
                    rewrite_recurrence_with_profile(in[0], profile));

                if (in.is(spot::op::W) && in[0] == p.guard)
                  return spot::formula::tt();

                if (in.is(spot::op::R) && in[1] == p.guard)
                  return spot::formula::tt();
              }
            else
              {
                // Under GF(!gamma), G gamma is false on every suffix.
                // Therefore the weak alternatives cannot discharge via the
                // "forever gamma" branch:
                //   gamma W beta  == gamma U beta
                //   alpha R gamma == alpha M gamma.
                if (in.is(spot::op::W) && in[0] == p.guard)
                  return spot::formula::U(
                    rewrite_recurrence_with_profile(in[0], profile),
                    rewrite_recurrence_with_profile(in[1], profile));

                if (in.is(spot::op::R) && in[1] == p.guard)
                  return spot::formula::M(
                    rewrite_recurrence_with_profile(in[0], profile),
                    rewrite_recurrence_with_profile(in[1], profile));
              }
          }
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


  void
  ltl2dela_translator::collect_nu_subformulas(
    spot::formula f,
    std::vector<spot::formula>& out) const
  {
    if (f.is(spot::op::G) || f.is(spot::op::W) || f.is(spot::op::R))
      {
        if (std::find(out.begin(), out.end(), f) == out.end())
          out.push_back(f);
      }
    for (unsigned i = 0; i < f.size(); ++i)
      collect_nu_subformulas(f[i], out);
  }

  void
  ltl2dela_translator::collect_mu_subformulas(
    spot::formula f, std::vector<spot::formula>& out) const
  {
    if (f.is(spot::op::F) || f.is(spot::op::U) || f.is(spot::op::M))
      if (std::find(out.begin(), out.end(), f) == out.end())
        out.push_back(f);
    for (auto c: f) collect_mu_subformulas(c, out);
  }

  spot::formula
  ltl2dela_translator::advice_nu(
    spot::formula f, const std::vector<spot::formula>& x) const
  {
    using formula = spot::formula;
    if (f.is(spot::op::F) || f.is(spot::op::U) || f.is(spot::op::M))
      {
        if (std::find(x.begin(), x.end(), f) == x.end())
          return formula::ff();
        if (f.is(spot::op::F)) return formula::tt();
        auto a = advice_nu(f[0], x);
        auto b = advice_nu(f[1], x);
        return f.is(spot::op::U) ? formula::W(a, b) : formula::R(a, b);
      }
    return f.map([&](formula c) { return advice_nu(c, x); });
  }

  spot::twa_graph_ptr
  ltl2dela_translator::make_x_advice_monitor(
    spot::formula f, const std::vector<spot::formula>& x)
  {
    auto aut = spot::make_twa_graph(dict_);
    auto rejecting = aut->set_co_buchi();
    symbolic_after af(aut, options_.x_advice_work_limit);
    using state = std::pair<spot::formula, spot::formula>;
    std::map<state, unsigned> numbers;
    std::vector<state> states;
    auto intern = [&](state s)
      {
        s.first = af.canonical(s.first);
        s.second = af.canonical(s.second);
        auto old = numbers.find(s);
        if (old != numbers.end()) return old->second;
        if (states.size() >= options_.x_advice_state_limit)
          throw x_advice_limit{};
        unsigned n = aut->new_state();
        numbers.emplace(s, n);
        states.push_back(s);
        return n;
      };
    aut->set_init_state(intern({f, advice_nu(f, x)}));
    for (unsigned src = 0; src < states.size(); ++src)
      {
        // Copy: intern() may reallocate states.  Maps in af retain references.
        auto current = states[src];
        bool reset = current.second.is_ff();
        auto safety = reset ? advice_nu(current.first, x) : current.second;
        const auto& main_steps = af.after(current.first);
        const auto& safety_steps = af.after(safety);
        for (const auto& a: main_steps)
          for (const auto& b: safety_steps)
            {
              bdd letters = a.second & b.second;
              if (letters == bddfalse) continue;
              unsigned dst = intern({a.first, b.first});
              aut->new_edge(src, dst, letters,
                            reset ? rejecting : spot::acc_cond::mark_t{});
            }
      }
    aut->register_aps_from_dict();
    aut->merge_edges();
    aut->prop_universal(true);
    aut->prop_complete(true);
    return aut;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::compile_x_advice(spot::formula f)
  {
    if (!options_.use_master_profiles || !options_.use_x_advice)
      return nullptr;
    // Keep identities of mu-subformulas throughout af and advice.  Only NNF
    // conversion precedes collection; temporal simplification is forbidden
    // inside the progression layer.
    f = simplifier_.negative_normal_form(f);
    std::vector<spot::formula> mus;
    collect_mu_subformulas(f, mus);
    if (mus.empty() || mus.size() > options_.x_advice_max_mu
        || mus.size() >= std::numeric_limits<unsigned>::digits)
      return nullptr;
    try
      {
        spot::twa_graph_ptr result;
        unsigned profiles = 1U << mus.size();
        for (unsigned mask = 0; mask < profiles; ++mask)
          {
            std::vector<spot::formula> x;
            std::vector<spot::formula> guards;
            for (unsigned i = 0; i < mus.size(); ++i)
              {
                bool selected = mask & (1U << i);
                if (selected) x.push_back(mus[i]);
                // Exactly X = {mu : w |= GF mu}.  The negative branch is
                // FG !mu, NOT GF !mu; eventual truth is not recurrence.
                guards.push_back(selected
                  ? spot::formula::G(spot::formula::F(mus[i]))
                  : spot::formula::F(spot::formula::G(
                      spot::formula::Not(mus[i]))));
              }
            auto monitor = make_x_advice_monitor(f, x);
            // Existing generic translation checks the profile independently.
            // Do not call compile(): that would recursively enumerate the
            // very obligations used to certify this construction.
            auto guard = translate_deterministic(spot::formula::And(guards));
            auto fits_acceptance = [](const spot::twa_graph_ptr& a,
                                      const spot::twa_graph_ptr& b)
              {
                return a->num_sets() + b->num_sets()
                  <= spot::acc_cond::mark_t::max_accsets();
              };
            if (!fits_acceptance(monitor, guard)) throw x_advice_limit{};
            auto branch = compose(monitor, guard, false);
            if (result && !fits_acceptance(result, branch))
              throw x_advice_limit{};
            result = result ? compose(result, branch, true) : branch;
          }
        ++stats_.x_advice_components;
        stats_.x_advice_profiles += profiles;
        return result;
      }
    catch (const x_advice_limit&)
      {
        ++stats_.x_advice_aborts;
        return nullptr;
      }
  }

  bool
  ltl2dela_translator::nu_profile_value(
    spot::formula nu,
    const std::vector<profile_fact>& profile,
    bool& stable) const
  {
    for (const auto& p: profile)
      {
        if (p.guard == nu)
          {
            stable = p.stable;
            return true;
          }

        // FG(G gamma) == FG gamma and GF !G gamma == GF !gamma.
        if (nu.is(spot::op::G) && nu.size() == 1
            && p.guard == nu[0])
          {
            stable = p.stable;
            return true;
          }
      }
    return false;
  }

  spot::formula
  ltl2dela_translator::advice_mu(
    spot::formula f,
    const std::vector<spot::formula>& y) const
  {
    auto in_y = [&](spot::formula x)
      {
        return std::find(y.begin(), y.end(), x) != y.end();
      };

    if (f.is(spot::op::G) && f.size() == 1)
      return in_y(f) ? spot::formula::tt() : spot::formula::ff();

    if (f.is(spot::op::W) && f.size() == 2)
      {
        if (in_y(f))
          return spot::formula::tt();
        return spot::formula::U(advice_mu(f[0], y),
                                advice_mu(f[1], y));
      }

    if (f.is(spot::op::R) && f.size() == 2)
      {
        if (in_y(f))
          return spot::formula::tt();
        return spot::formula::M(advice_mu(f[0], y),
                                advice_mu(f[1], y));
      }

    return f.map([&](spot::formula child)
      {
        return advice_mu(child, y);
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
        // First complete the exact Y-advice profile for all nu-subformulas.
        std::vector<spot::formula> nus;
        collect_nu_subformulas(gf_body, nus);
        for (auto nu: nus)
          {
            bool stable = false;
            if (!nu_profile_value(nu, profile, stable)
                && !was_used(nu, used)
                && formula_length(nu) <= options_.profile_guard_max_length)
              return nu;
          }

        // First prefer explicit G-obligations.
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

        // If there is no explicit G, use the persistent guard of a recurrent
        // fixed-point obligation.  U/W use their left guard; M/R are the
        // corresponding release forms and use their right guard.
        gf_body.traverse([&](spot::formula sf)
          {
            if (found)
              return true;

            spot::formula g = spot::formula::ff();
            if ((sf.is(spot::op::U) || sf.is(spot::op::W))
                && sf.size() == 2)
              g = sf[0];
            else if ((sf.is(spot::op::M) || sf.is(spot::op::R))
                     && sf.size() == 2)
              g = sf[1];

            if (!g.is_ff() && !g.is_tt()
                && !already_known(g)
                && formula_length(g) <= options_.profile_guard_max_length)
              {
                chosen = g;
                found = true;
                return true;
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
    bdd wait0 = (!h) & g & l;
    accepting_edge(0, 0, success0);
    plain_edge(0, 1, wait0);
    plain_edge(0, 0, !(success0 | wait0));

    // pending = 1
    bdd success1 = h;
    bdd wait1 = (!h) & g;
    accepting_edge(1, 0, success1);
    plain_edge(1, 1, wait1);
    plain_edge(1, 0, !(success1 | wait1));

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

    // Exact Master-Theorem Y-advice.  Once every nu-subformula of the GF body
    // has an asymptotic truth value, rewrite the body to mu-LTL exactly as in
    // the EKS advice function.
    {
      std::vector<spot::formula> nus;
      collect_nu_subformulas(body, nus);
      if (!nus.empty())
        {
          bool complete = true;
          std::vector<spot::formula> y;
          for (auto nu: nus)
            {
              bool stable = false;
              if (!nu_profile_value(nu, profile, stable))
                {
                  complete = false;
                  break;
                }
              if (stable)
                y.push_back(nu);
            }

          if (complete)
            {
              auto advised = simplifier_.simplify(advice_mu(body, y));
              if (advised != body)
                {
                  handled = true;
                  ++stats_.master_advice_rewrites;
                  return compile(gf(advised), depth, used, false, profile);
                }
            }
        }
    }

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

  namespace
  {
    struct finite_witness_limit {};

    // Convert only after infinite-word NNF.  Never apply the ordinary LTL
    // simplifier afterwards: X tt and strong_X tt differ on finite traces.
    spot::formula strong_finite_next(spot::formula f)
    {
      if (f.is(spot::op::X))
        return spot::formula::strong_X(strong_finite_next(f[0]));
      return f.map(strong_finite_next);
    }
  }

  spot::twa_graph_ptr
  ltl2dela_translator::make_finite_witness_monitor(spot::formula body,
                                                 bool persistence)
  {
    try
      {
        if (!options_.finite_witness_state_limit
            || !options_.finite_witness_work_limit)
          throw finite_witness_limit{};
        auto aut = spot::make_twa_graph(dict_);
        body.traverse([&](spot::formula x) {
          if (x.is(spot::op::ap)) aut->register_ap(x);
          return false;
        });
        auto initial = spot::formula::F(strong_finite_next(body));
        // Spot's terminal has both a continuation formula and a may-stop bit.
        // The latter, not the continuation's infinite-word truth value, says
        // whether the finite prefix just consumed is accepted.
        spot::ltlf_translator trans(dict_);
        std::map<spot::formula, unsigned> ids;
        std::vector<spot::formula> pending;
        auto state = [&](spot::formula f) -> unsigned {
          auto old = ids.find(f);
          if (old != ids.end()) return old->second;
          if (pending.size() >= options_.finite_witness_state_limit)
            throw finite_witness_limit{};
          unsigned id = aut->new_state();
          ids.emplace(f, id);
          pending.push_back(f);
          return id;
        };
        state(initial);
        aut->set_init_state(0);
        aut->set_acceptance(1, persistence ? spot::acc_cond::acc_code::cobuchi()
                                           : spot::acc_cond::acc_code::buchi());
        unsigned work = 0;
        for (unsigned src = 0; src < pending.size(); ++src)
          {
            bdd root = trans.ltlf_to_mtbdd(pending[src]);
            std::vector<std::pair<bdd, bdd>> todo{{root, bddtrue}};
            while (!todo.empty())
              {
                if (++work > options_.finite_witness_work_limit)
                  throw finite_witness_limit{};
                auto node = todo.back();
                todo.pop_back();
                bdd b = node.first;
                bdd guard = node.second;
                if (b == bddtrue || b == bddfalse || bdd_is_terminal(b))
                  {
                    auto leaf = trans.leaf_to_formula(b.id(),
                      bdd_is_terminal(b) ? bdd_get_terminal(b) : 0);
                    // Accepting destinations are redirected immediately; no
                    // letter is consumed twice and no pending witness survives.
                    unsigned dst = leaf.second ? 0 : state(leaf.first);
                    aut->new_edge(src, dst, guard,
                      leaf.second ? spot::acc_cond::mark_t{0}
                                  : spot::acc_cond::mark_t{});
                  }
                else
                  {
                    bdd var = bdd_ithvar(bdd_var(b));
                    todo.emplace_back(bdd_low(b), guard & !var);
                    todo.emplace_back(bdd_high(b), guard & var);
                  }
              }
          }
        aut->prop_universal(true);
        aut->prop_complete(true);
        aut->prop_state_acc(false);
        aut->merge_edges();
        ++stats_.finite_witness_monitors;
        if (persistence) ++stats_.finite_witness_duals;
        return aut;
      }
    catch (const finite_witness_limit&)
      {
        ++stats_.finite_witness_aborts;
        return nullptr;
      }
  }

  spot::twa_graph_ptr
  ltl2dela_translator::compile_finite_witness(spot::formula f)
  {
    spot::formula body;
    bool persistence = false;
    if (!match_gf(f, body))
      {
        if (!match_fg(f, body)) return nullptr;
        persistence = true;
        body = spot::formula::Not(body);
      }
    body = simplifier_.negative_normal_form(body);
    // Keep propositional recurrence/persistence on Spot's one-state path.
    if (body.is_boolean() || !body.is_syntactic_guarantee()) return nullptr;
    // The dual should retain the existing flat monitor as a fast path too.
    spot::formula lambda, guard, goal;
    if (persistence && options_.use_recurrence_compiler
        && match_flat_until(body, lambda, guard, goal))
      {
        auto aut = make_flat_until_monitor(lambda, guard, goal);
        aut->set_acceptance(1, spot::acc_cond::acc_code::cobuchi());
        ++stats_.flat_until_monitors;
        return aut;
      }
    return make_finite_witness_monitor(body, persistence);
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
  ltl2dela_translator::compile_specialized(spot::formula f)
  {
    // Boolean combinations of GF/FG over propositional predicates admit
    // one-state Emerson-Lei monitors.  Compile them together before profile
    // commitments turn FG predicates into multi-state products.
    if (!f.is_boolean() && boolean_gf_fg(f))
      {
        spot::option_map om;
        om.set("gf-guarantee", 1);
        spot::translator trans(dict_, &om);
        trans.set_type(spot::postprocessor::Generic);
        trans.set_pref(spot::postprocessor::Deterministic);
        trans.set_level(spot::postprocessor::Low);
        ++stats_.boolean_gf_fg_components;
        return normalize_deterministic(trans.run(f));
      }

    spot::formula body;
    if (match_gf(f, body) && body.is_syntactic_guarantee())
      if (auto aut = spot::gf_guarantee_to_ba_maybe(f, dict_, true, false))
        {
          ++stats_.specialized_gf_components;
          return normalize_deterministic(aut);
        }
    if (match_fg(f, body) && body.is_syntactic_safety())
      if (auto aut = spot::fg_safety_to_dca_maybe(f, dict_, false))
        {
          ++stats_.specialized_fg_components;
          return normalize_deterministic(aut);
        }

    // Syntactic recurrence is sufficient for DBA recognizability, but does
    // not exhaust it.  Other residuals get the same checked attempt after
    // their small BA is available, below.
    if (is_direct_fragment(f) && !match_gf(f, body) && !match_fg(f, body))
      {
        spot::twa_graph_ptr dba;
        if (options_.use_dba && f.is_syntactic_recurrence()
            && !f.is_syntactic_obligation())
          dba = try_dba(f, translate_buchi(f));
        if (guarded_conjunction(f)) ++stats_.guarded_conjunctions;
        ++stats_.direct_formula_components;
        auto direct = normalize_deterministic(translate_deterministic(f));
        // Recognized fragments are terminal: generic SLAA/LDGBA routes
        // are reserved for residuals without a specialized construction.
        if (dba && no_larger(dba, direct))
          {
            ++stats_.dba_components;
            return dba;
          }
        return direct;
      }
    return nullptr;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::try_dba(spot::formula f, spot::twa_graph_ptr ba)
  {
    if (!options_.use_dba || !options_.dba_state_limit
        || !options_.dba_cycle_limit || ba->num_states() > options_.dba_input_limit
        || ba->num_states() > options_.dba_state_limit)
      return nullptr;
    ++stats_.dba_attempts;
    auto accept = [&](spot::twa_graph_ptr aut)
      {
        ++stats_.dba_candidates;
        return normalize_deterministic(aut);
      };
    if (spot::is_deterministic(ba)) return accept(ba);

    // Bound the subset graph AND the follow-up products in the weak-DBA
    // attempt.  Spot's default deterministic preference does not apply its
    // ordinary wdba-det-max bound.
    spot::output_aborter aborter(options_.dba_state_limit);
    auto weak = spot::minimize_obligation(ba, f, nullptr, false, &aborter);
    if (weak && spot::is_deterministic(weak)) return accept(weak);

    // A bounded semantic attempt also covers DBA languages outside the
    // syntactically recognized recurrence fragment.  The checked API rejects
    // inequivalent acceptance assignments; an unchecked powerset is unsound.
    if (!ba->acc().is_buchi()) ba = spot::degeneralize_tba(ba);
    if (ba->num_states() <= options_.dba_input_limit
        && ba->num_states() <= options_.dba_state_limit)
      {
        unsigned factor = options_.dba_state_limit / ba->num_states();
        auto det = spot::tba_determinize_check(ba, factor,
                                             options_.dba_cycle_limit, f);
        if (det && spot::is_deterministic(det)) return accept(det);
      }
    ++stats_.dba_fallbacks;
    return nullptr;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::translate_deterministic(spot::formula f)
  {
    // COLA decides which Boolean components may be separated.  Preserve
    // safety guards in the residual handed to Spot: splitting them away can
    // make a tiny constrained BA have an enormous intermediate powerset.
    spot::option_map om;
    om.set("ltl-split", guarded_conjunction(f) ? 0 : 1);
    om.set("gf-guarantee", 1);
    spot::translator trans(dict_, &om);
    trans.set_type(spot::postprocessor::Generic);
    trans.set_pref(spot::postprocessor::Deterministic);
    // More optimization is not a monotone size improvement: on literature
    // examples Low yields 8/50 states where High yields 20/65.  Retain both
    // candidates and compare complete reachable sizes, then marks and edges.
    trans.set_level(spot::postprocessor::Low);
    auto low = trans.run(f);
    trans.set_level(spot::postprocessor::High);
    auto high = trans.run(f);
    return no_larger(low, high) ? low : high;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::try_slaa(spot::formula f, bool& negative)
  {
    negative = false;
    if (options_.slaa_tool.empty() || !options_.slaa_timeout_ms
        || !options_.slaa_state_limit) return nullptr;
    auto candidate = [&](bool negate) -> spot::twa_graph_ptr
      {
        ++stats_.slaa_attempts;
        if (negate) ++stats_.slaa_negative_attempts;
        try
          {
            auto source = negate ? spot::formula::Not(f) : f;
            auto tela = slaa_frontend(source, dict_, options_.slaa_tool,
                                     options_.slaa_timeout_ms, options_.slaa_state_limit);
            if (!tela) { ++stats_.slaa_failures; return nullptr; }
            bool colours_rewritten = false;
            if (options_.use_colour_choice)
              {
                ++stats_.colour_choice_attempts;
                bool was_elevator = cola::is_elevator_automaton(tela);
                auto rewritten = eliminate_colour_choices(tela, options_.colour_choices);
                if (!rewritten.equivalent) ++stats_.colour_choice_validation_failures;
                stats_.colour_choice_sccs += rewritten.rewritten;
                colours_rewritten = rewritten.rewritten != 0;
                tela = rewritten.automaton;
                if (!was_elevator && cola::is_elevator_automaton(tela))
                  ++stats_.colour_choice_repairs;
              }
            if (options_.use_cobuchi_weak)
              {
                bool was_elevator = cola::is_elevator_automaton(tela);
                auto weak = weakify_cobuchi_sccs(tela, options_.cobuchi_weak);
                if (!weak.equivalent) ++stats_.cobuchi_weak_validation_failures;
                stats_.cobuchi_weak_sccs += weak.rewritten;
                stats_.cobuchi_weak_states += weak.automaton->num_states() - tela->num_states();
                tela = weak.automaton;
                if (!was_elevator && cola::is_elevator_automaton(tela)) ++stats_.cobuchi_weak_repairs;
              }
            if (!cola::is_elevator_automaton(tela))
              { ++stats_.slaa_non_elevator; return nullptr; }
            // Certify both boundaries. In particular, a deterministic but wrong
            // frontend result must not bypass validation.
            if (!spot::are_equivalent(tela, source))
              { ++stats_.slaa_validation_failures; return nullptr; }
            auto generic_options = cola_options_;
            // The existing delayed simulation is a Buchi-specific algorithm.
            // Neither it nor the optional simulation preprocessing certifies
            // pruning for arbitrary Fin/Inf acceptance on this new boundary.
            generic_options.set(USE_SIMULATION, 0);
            generic_options.set(USE_DELAYED_SIMULATION, 0);
            generic_options.set(USE_STUTTER, 0);
            if (colours_rewritten) generic_options.set(USE_OBSERVED_RANKS, 1);
            if (options_.use_colour_choice) generic_options.set(USE_LOCAL_COLOURS, 1);
            if (!spot::is_deterministic(tela)) ++stats_.slaa_backend_attempts;
            auto result = spot::is_deterministic(tela) ? tela
              : cola::determinize_televator(tela, generic_options);
            if (!spot::is_deterministic(result) || !spot::are_equivalent(result, tela))
              { ++stats_.slaa_validation_failures; return nullptr; }
            result = normalize_deterministic(result);
            if (negate)
              {
                // Missing transitions reject the negative language. They must
                // reach a rejecting sink BEFORE acceptance is complemented.
                result = spot::complete(result);
                result->set_acceptance(result->num_sets(),
                                       result->acc().get_acceptance().complement());
                if (!spot::are_equivalent(result, f))
                  { ++stats_.slaa_validation_failures; return nullptr; }
                ++stats_.slaa_negative_candidates;
              }
            ++stats_.slaa_candidates;
            return result;
          }
        catch (const std::runtime_error&)
          {
            // An optional candidate (including acceptance-capacity exhaustion)
            // never replaces or discards any branch of the residual language.
            ++stats_.slaa_failures;
            return nullptr;
          }
      };
    auto positive = candidate(false);
    if (!options_.slaa_portfolio) return positive;
    auto dual = candidate(true);
    // Exact size ties retain positive polarity; never lose an available
    // positive result because the additional attempt fails or is larger.
    if (dual && (!positive || (no_larger(dual, positive) && !no_larger(positive, dual))))
      { negative = true; return dual; }
    return positive;
  }

  spot::twa_graph_ptr
  ltl2dela_translator::try_ldgba(spot::formula f)
  {
    if (options_.ldgba_tool.empty() || !options_.ldgba_timeout_ms
        || !options_.ldgba_state_limit || !options_.ldgba_attempt_limit) return nullptr;
    auto cached = ldgba_cache_.find(f);
    if (cached != ldgba_cache_.end())
      { ++stats_.ldgba_cache_hits; return cached->second; }
    spot::twa_graph_ptr best;
    for (bool negative : {false, true})
    for (const std::string construction : {"SEJK16", "EKS20"})
      {
        if (negative && !options_.ldgba_portfolio) continue;
        if (options_.ldgba_construction != "both"
            && options_.ldgba_construction != construction) continue;
        if (stats_.ldgba_attempts >= options_.ldgba_attempt_limit)
          { ++stats_.ldgba_budget_skips; break; }
        ++stats_.ldgba_attempts;
        try
          {
            auto source_formula = negative ? spot::formula::Not(f) : f;
            auto input = owl_ldgba_frontend(source_formula, dict_, options_.ldgba_tool, construction,
                                           options_.ldgba_timeout_ms, options_.ldgba_state_limit);
            if (!input) { ++stats_.ldgba_failures; continue; }
            if (!input->acc().is_generalized_buchi() || !cola::is_elevator_automaton(input))
              { ++stats_.ldgba_rejected; continue; }
            if (!spot::are_equivalent(input, source_formula))
              { ++stats_.ldgba_validation_failures; continue; }
            auto om = cola_options_;
            om.set(USE_SIMULATION, 0);
            om.set(USE_DELAYED_SIMULATION, 0);
            om.set(USE_STUTTER, 0);
            om.set(USE_OBSERVED_RANKS, 1);
            om.set(USE_OWL_ANNOTATIONS, options_.ldgba_annotations);
            om.set(USE_OWL_CROSS_SCC, options_.ldgba_cross_scc);
            if (options_.ldgba_pruning)
              {
                om.set(USE_LOCAL_COLOURS, 1);
                om.set(EXACT_STATE_LANG_SCC_LIMIT, 256);
                om.set(EXACT_UNION_COVER_LIMIT, 256);
                om.set(EXACT_CONTAINMENT_BUDGET, 512);
              }
            bool deterministic = spot::is_deterministic(input);
            if (!deterministic) ++stats_.ldgba_backend_attempts;
            auto result = deterministic ? input : cola::determinize_televator(input, om);
            bool cross_changed = false;
            if (auto a = result->get_named_prop<owl_annotation_stats>("cola-owl-annotation-stats"))
              {
                stats_.ldgba_annotations_certified += a->certified;
                stats_.ldgba_annotations_rejected += a->rejected;
                stats_.ldgba_annotation_pair_proofs += a->pair_proofs;
                stats_.ldgba_annotation_union_proofs += a->union_proofs;
                stats_.ldgba_cross_scc_proofs += a->cross_scc_proofs;
                cross_changed = a->cross_scc_proofs > 0;
              }
            result = normalize_deterministic(result);
            if (!spot::is_deterministic(result) || !spot::are_equivalent(result, input))
              { ++stats_.ldgba_validation_failures; continue; }
            if (negative)
              {
                // Postprocessing may remove a rejecting sink. Explicitly
                // complete before dualising, as at the SLAA boundary.
                result = spot::complete(result);
                result->set_acceptance(result->num_sets(),
                                      result->acc().get_acceptance().complement());
                result = normalize_deterministic(result);
                if (!spot::are_equivalent(result, f))
                  { ++stats_.ldgba_validation_failures; continue; }
              }
            if (options_.ldgba_cross_scc && cross_changed)
              {
                // Certified pruning preserves language, but need not reduce
                // reachable macrostates. Compare the original SCC construction
                // on the same input; no additional frontend call is required.
                try
                  {
                    auto baseline_options = om;
                    baseline_options.set(USE_OWL_CROSS_SCC, 0);
                    ++stats_.ldgba_backend_attempts;
                    auto baseline = normalize_deterministic(
                      cola::determinize_televator(input, baseline_options));
                    if (negative)
                      {
                        baseline = spot::complete(baseline);
                        baseline->set_acceptance(baseline->num_sets(),
                          baseline->acc().get_acceptance().complement());
                        baseline = normalize_deterministic(baseline);
                      }
                    if (!spot::is_deterministic(baseline) || !spot::are_equivalent(baseline, f))
                      ++stats_.ldgba_validation_failures;
                    else
                      {
                        baseline = spot::complete(baseline);
                        result = spot::complete(result);
                        if (no_larger(baseline, result)) result = baseline;
                      }
                  }
                catch (const std::runtime_error&) { ++stats_.ldgba_failures; }
              }
            ++stats_.ldgba_candidates;
            if (!best || (no_larger(result, best) && !no_larger(best, result))) best = result;
          }
        catch (const std::runtime_error&)
          { ++stats_.ldgba_failures; }
      }
    // Cache failed attempts too: profile refinement often revisits the same
    // residual without changing its language. Reset this cache for each run.
    ldgba_cache_.emplace(f, best);
    return best;
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
        if (sf.is(spot::op::U) && sf.size() == 2)
          add(sf[0], 85);
        if (sf.is(spot::op::M) && sf.size() == 2)
          add(sf[1], 85);

        // W has the same persistent left guard as U.  R is the dual release
        // form and its persistent guard is the right operand.
        if (sf.is(spot::op::W) && sf.size() == 2)
          add(sf[0], 75);
        if (sf.is(spot::op::R) && sf.size() == 2)
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
                if (sf.is(spot::op::U) && sf.size() == 2)
                  add(sf[0], 105);
                if (sf.is(spot::op::M) && sf.size() == 2)
                  add(sf[1], 105);
                if (sf.is(spot::op::W) && sf.size() == 2)
                  add(sf[0], 95);
                if (sf.is(spot::op::R) && sf.size() == 2)
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
    // Basic simplification can fold Boolean GF/FG combinations into G/F
    // bodies, hiding this fragment before its one-state route sees it.
    if (options_.use_specialized_fragments && !f.is_boolean()
        && boolean_gf_fg(f))
      return compile_specialized(f);
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

    if (options_.use_finite_witness)
      if (auto witness = compile_finite_witness(f))
        return normalize_deterministic(witness);

    if (options_.use_specialized_fragments)
      if (auto special = compile_specialized(f)) return special;

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

    // Try the exact derivative construction before heuristic profile splits
    // and Delta2 normalization can obscure the original mu obligations.
    // Keep easy fragments on their existing specialized translation path.
    if (!is_direct_fragment(f))
      if (auto advised = compile_x_advice(f)) return advised;

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
        if (!gamma.is_ff())
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

    // Retain safety constraints with the other conjuncts.  Their labels
    // prune impossible histories during translation; a later product cannot
    // recover the time/memory spent exploring unconstrained components.
    bool retain_guard = options_.use_specialized_fragments
      && guarded_conjunction(f);
    if (retain_guard) ++stats_.guarded_conjunctions;

    // Boolean decomposition is safe because the deterministic results are
    // combined directly with Emerson-Lei acceptance instead of first forcing
    // their conjunction/disjunction through a monolithic Buchi automaton.
    if (allow_boolean_split && options_.boolean_decomposition
        && !retain_guard
        && (f.is(spot::op::And) || f.is(spot::op::Or))
        && f.size() > 1)
      {
        bool disjunction = f.is(spot::op::Or);
        auto res = compile(f[0], depth, used, true, profile);
        for (unsigned i = 1; i < f.size(); ++i)
          res = compose(res, compile(f[i], depth, used, true, profile), disjunction);
        return res;
      }

    // A prepared residual can expose a fragment hidden before Delta2.
    // Recheck it before admitting either external generic frontend.
    if (options_.use_specialized_fragments)
      if (auto special = compile_specialized(f)) return special;

    // Checked DBA recognition takes priority over generic dealternation.
    // Reuse its BA if recognition fails and native elevator analysis is needed.
    spot::twa_graph_ptr ba;
    if (options_.use_dba)
      {
        ba = translate_buchi(f);
        if (auto dba = try_dba(f, ba))
          {
            ++stats_.dba_components;
            return dba;
          }
      }

    // Exhaust available profile decompositions before generic frontends.
    // Each child repeats the specialized checks with its refined context.
    if (!ba) ba = translate_buchi(f);
    auto h = analyze(ba);
    if (!h.elevator)
      {
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
      }

    auto ldgba = try_ldgba(f);
    auto finish = [&](spot::twa_graph_ptr result)
      {
        // Keep the established residual construction on exact ties. A
        // successful LDGBA is a candidate, not a minimality certificate.
        if (ldgba && no_larger(ldgba, result) && !no_larger(result, ldgba))
          { ++stats_.ldgba_components; return ldgba; }
        return result;
      };

    bool negative = false;
    auto slaa = try_slaa(f, negative);
    if (slaa)
      {
        ++stats_.slaa_components;
        if (negative) ++stats_.slaa_negative_components;
        return finish(slaa);
      }

    // With early specialization disabled, retain a direct fallback after
    // the explicitly requested generic experiments.
    if (is_direct_fragment(f))
      {
        ++stats_.direct_formula_components;
        return finish(normalize_deterministic(translate_deterministic(f)));
      }

    // Try the small-Buchi route.  We only use CoLA's local elevator
    // determinizer if the generated SCC structure is certified suitable.
    if (h.elevator)
      {
        ++stats_.elevator_components;
        auto result = normalize_deterministic(options_.use_state_annotations
          ? cola::determinize_televator(ba, cola_options_, f)
          : cola::determinize_televator(ba, cola_options_));
        // The pre-existing elevator route fails language equivalence on some
        // profile-generated residuals (see the smoke regression).  SCC shape
        // alone does not certify the implementation's pruning.  Retain it
        // only after an exact check against its source BA; otherwise use the
        // generic formula translation.  Annotations never certify this gate.
        if (spot::are_equivalent(result, ba))
          {
            // An elevator certificate establishes applicability, not minimal
            // size. Dwyer 50 is 12 via this BA but 11 via formula translation.
            if (options_.slaa_portfolio && !options_.slaa_tool.empty()
                && options_.slaa_timeout_ms && options_.slaa_state_limit)
              {
                ++stats_.slaa_formula_candidates;
                try
                  {
                    auto direct = normalize_deterministic(translate_deterministic(f));
                    if (no_larger(direct, result))
                      { ++stats_.slaa_formula_components; return finish(direct); }
                  }
                catch (const std::runtime_error&)
                  { ++stats_.slaa_formula_failures; }
              }
            return finish(result);
          }
        ++stats_.elevator_validation_fallbacks;
        ++stats_.deterministic_fallbacks;
        return finish(normalize_deterministic(translate_deterministic(f)));
      }

    // Total, Safra-free-at-the-LTL-level fallback: ask Spot to translate this
    // residual formula directly to a deterministic generic automaton.  This
    // intentionally avoids determinizing the hard BA we just inspected.
    ++stats_.deterministic_fallbacks;
    if (options_.verbose >= 1)
      std::cerr << "ltl2dela: deterministic formula fallback for "
                << f << '\n';
    return finish(normalize_deterministic(translate_deterministic(f)));
  }

  spot::twa_graph_ptr
  ltl2dela_translator::run(spot::formula f)
  {
    if (!f.is_ltl_formula())
      throw std::runtime_error("ltl2dela requires an LTL formula");

    stats_ = {};
    ldgba_cache_.clear();
    std::vector<spot::formula> used;
    // Do not normalize to Delta2 here: compile() must see the original
    // GF/profile syntax before deciding which structural compiler to use.
    try
      {
        return compile(f, 0, used, true, {});
      }
    catch (const std::runtime_error& e)
      {
        // A profile product can exceed the installed acceptance-set limit
        // even when the whole formula has a small deterministic translation.
        // Abandon every partial branch and translate the original formula.
        if (std::string(e.what()).find("Too many acceptance sets used.") != 0)
          throw;
        ++stats_.acceptance_limit_fallbacks;
        ++stats_.deterministic_fallbacks;
        return normalize_deterministic(translate_deterministic(f));
      }
  }
}
