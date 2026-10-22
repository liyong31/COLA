// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#include "colour_choice.hpp"
#include "cola.hpp"
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <algorithm>
#include <map>
#include <stdexcept>
#include <utility>

namespace cola
{
  namespace
  {
    using mark = spot::acc_cond::mark_t;
    using code = spot::acc_cond::acc_code;
    using op = spot::acc_cond::acc_op;
    struct limit { const char* reason; };
    struct clause { mark bad{}, good{}; };
    using dnf = std::vector<clause>;

    // Budget every intermediate sum/product, before expanding it. In Spot,
    // Inf({x,y}) means Inf(x)&Inf(y), but Fin({x,y}) means Fin(x)|Fin(y).
    dnf bounded_dnf(const code& f, unsigned budget)
    {
      if (f.is_f()) return {};
      if (f.is_t()) return {clause{}};
      auto root = f.back().sub.op;
      if (root == op::Inf) return {{mark{}, f.used_sets()}};
      if (root == op::Fin)
        {
          dnf out;
          for (unsigned c : f.used_sets().sets())
            {
              if (out.size() >= budget) throw limit{"clause-budget"};
              out.push_back({mark{c}, mark{}});
            }
          return out;
        }
      if (root != op::And && root != op::Or) throw limit{"negative-mark-literal"};
      dnf out = root == op::And ? dnf{clause{}} : dnf{};
      auto children = root == op::And ? f.top_conjuncts() : f.top_disjuncts();
      for (const auto& child : children)
        {
          auto rhs = bounded_dnf(child, budget);
          if (root == op::Or)
            {
              if (out.size() + rhs.size() > budget) throw limit{"clause-budget"};
              out.insert(out.end(), rhs.begin(), rhs.end());
            }
          else
            {
              if (!rhs.empty() && out.size() > budget / rhs.size())
                throw limit{"clause-budget"};
              dnf product;
              for (const auto& a : out)
                for (const auto& b : rhs)
                  {
                    clause c{a.bad | b.bad, a.good | b.good};
                    if (!(c.bad & c.good)) product.push_back(c);
                  }
              out = std::move(product);
            }
        }
      return out;
    }

    struct edge { unsigned src, dst; bdd guard; mark colours{}; };
    struct plan
    {
      bool active = false;
      code acceptance = code::f();
      std::vector<edge> edges;
    };

    bool target_deterministic(const spot::const_twa_graph_ptr& a,
                              const spot::scc_info& si, unsigned sc)
    {
      for (unsigned q : si.states_of(sc))
        {
          std::map<unsigned, bdd> targets;
          for (const auto& e : a->out(q))
            if (si.scc_of(e.dst) == sc && e.cond != bddfalse)
              {
                auto found = targets.find(e.dst);
                if (found == targets.end()) targets.emplace(e.dst, e.cond);
                else found->second |= e.cond;
              }
          bdd seen = bddfalse;
          for (const auto& t : targets)
            {
              if ((seen & t.second) != bddfalse) return false;
              seen |= t.second;
            }
        }
      return true;
    }
  }

  colour_choice_result eliminate_colour_choices(
    const spot::const_twa_graph_ptr& input, const colour_choice_options& options)
  {
    colour_choice_result result;
    result.automaton = spot::make_twa_graph(input, spot::twa::prop_set::all());
    if (!input->is_existential()) return result;
    spot::scc_info si(input, spot::scc_info_options::ALL);
    auto types = get_scc_types(si);
    std::vector<plan> plans(si.scc_count());
    unsigned original = input->num_sets();
    unsigned bound = std::min(options.max_colours, mark::max_accsets());
    unsigned next = original + 1; // one shared selector for unchanged SCCs
    for (unsigned sc = 0; sc < si.scc_count(); ++sc)
      {
        colour_scc_certificate cert;
        cert.scc = sc;
        cert.states = si.states_of(sc).size();
        cert.target_deterministic = target_deterministic(input, si, sc);
        if (types[sc] & SCC_INSIDE_DET_TYPE) cert.reason = "deterministic";
        else if (types[sc] & SCC_WEAK_TYPE) cert.reason = "inherently-weak";
        else if (!cert.target_deterministic) cert.reason = "multiple-internal-targets";
        else
          {
            unsigned local_next = next;
            try
              {
                if (!options.max_clauses || !options.max_regions || !options.max_formula_words)
                  throw limit{"zero-budget"};
                mark occurring{}, common = input->acc().all_sets();
                for (unsigned q : si.states_of(sc))
                  for (const auto& e : input->out(q))
                    if (si.scc_of(e.dst) == sc && e.cond != bddfalse)
                      { occurring |= e.acc; common &= e.acc; }
                auto local = input->acc().get_acceptance()
                  .remove(input->acc().all_sets() - occurring, true).remove(common, false);
                if (local.size() > options.max_formula_words) throw limit{"formula-budget"};
                auto clauses = bounded_dnf(local, options.max_clauses);
                cert.clauses = clauses.size();
                auto fresh = [&]() -> unsigned
                  {
                    if (local_next >= bound) throw limit{"colour-budget"};
                    return local_next++;
                  };
                unsigned selector = fresh();
                struct output_clause { clause source; unsigned bad; std::vector<std::pair<unsigned, unsigned>> goods; };
                std::vector<output_clause> outputs;
                code beta = code::f();
                for (const auto& c : clauses)
                  {
                    output_clause out{c, bound, {}};
                    code term = code::t();
                    if (c.bad)
                      { out.bad = fresh(); term &= code::fin({out.bad}); }
                    for (unsigned g : c.good.sets())
                      {
                        unsigned colour = fresh();
                        out.goods.emplace_back(g, colour);
                        term &= code::inf({colour});
                      }
                    outputs.push_back(std::move(out));
                    beta |= term;
                  }
                auto& p = plans[sc];
                p.acceptance = code::inf({selector}) & beta;
                if (p.acceptance.size() > options.max_formula_words) throw limit{"formula-budget"};
                for (unsigned q : si.states_of(sc))
                  {
                    std::map<unsigned, std::vector<const spot::twa_graph::edge_storage_t*>> targets;
                    for (const auto& e : input->out(q))
                      if (si.scc_of(e.dst) == sc && e.cond != bddfalse)
                        targets[e.dst].push_back(&e);
                    for (const auto& target : targets)
                      {
                        bdd enabled = bddfalse;
                        for (const auto* e : target.second) enabled |= e->cond;
                        std::vector<std::pair<unsigned, bdd>> predicates;
                        for (const auto& c : outputs)
                          {
                            bdd safe = bddfalse;
                            std::vector<bdd> good(c.goods.size(), bddfalse);
                            for (const auto* e : target.second)
                              if (!(e->acc & c.source.bad))
                                {
                                  safe |= e->cond;
                                  for (unsigned j = 0; j < good.size(); ++j)
                                    if (e->acc.has(c.goods[j].first)) good[j] |= e->cond;
                                }
                            if (c.bad < bound) predicates.emplace_back(c.bad, enabled & !safe);
                            for (unsigned j = 0; j < good.size(); ++j)
                              predicates.emplace_back(c.goods[j].second, good[j]);
                          }
                        std::vector<std::pair<bdd, mark>> regions{{enabled, mark{selector}}};
                        for (const auto& pred : predicates)
                          {
                            std::vector<std::pair<bdd, mark>> split;
                            for (const auto& r : regions)
                              {
                                bdd yes = r.first & pred.second, no = r.first & !pred.second;
                                if (no != bddfalse) split.emplace_back(no, r.second);
                                if (yes != bddfalse) split.emplace_back(yes, r.second | mark{pred.first});
                                if (p.edges.size() + split.size() > options.max_regions)
                                  throw limit{"region-budget"};
                              }
                            regions = std::move(split);
                          }
                        for (const auto& r : regions)
                          {
                            if (p.edges.size() >= options.max_regions) throw limit{"region-budget"};
                            p.edges.push_back({q, target.first, r.first, r.second});
                          }
                      }
                  }
                p.active = true;
                cert.regions = p.edges.size();
                cert.fresh_colours = local_next - next;
                next = local_next;
                cert.reason = "rewritten";
                ++result.rewritten;
              }
            catch (const limit& e)
              { plans[sc] = {}; cert.reason = e.reason; }
          }
        result.sccs.push_back(std::move(cert));
      }
    if (!result.rewritten) return result;
    auto out = spot::make_twa_graph(input->get_dict());
    out->copy_ap_of(input);
    out->new_states(input->num_states());
    out->set_init_state(input->get_init_state_number());
    code acceptance = code::inf({original}) & input->acc().get_acceptance();
    for (const auto& e : input->edges())
      {
        unsigned sc = si.scc_of(e.src);
        if (sc < plans.size() && si.scc_of(e.dst) == sc && plans[sc].active) continue;
        mark colours = e.acc;
        if (sc < plans.size() && si.scc_of(e.dst) == sc) colours.set(original);
        out->new_edge(e.src, e.dst, e.cond, colours);
      }
    for (const auto& p : plans)
      if (p.active)
        {
          acceptance |= p.acceptance;
          for (const auto& e : p.edges) out->new_edge(e.src, e.dst, e.guard, e.colours);
        }
    out->set_acceptance(next, acceptance);
    out->merge_edges();
    spot::cleanup_acceptance_here(out);
    bool equivalent;
    try { equivalent = spot::are_equivalent(input, out); }
    catch (const std::runtime_error& error)
      {
        // Language checking can need a product with more colours than either
        // input alone. Retain the unchanged, trivially equivalent graph.
        if (std::string(error.what()).find("Too many acceptance sets used.") != 0) throw;
        result.rewritten = 0;
        for (auto& c : result.sccs)
          if (c.reason == "rewritten") c.reason = "verification-capacity";
        return result;
      }
    if (!equivalent)
      {
        result.equivalent = false;
        result.rewritten = 0;
        for (auto& c : result.sccs) if (c.reason == "rewritten") c.reason = "equivalence-rejected";
        return result;
      }
    result.automaton = out;
    return result;
  }
}
