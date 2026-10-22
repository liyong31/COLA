// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#include "cobuchi_weak.hpp"
#include "cola.hpp"
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/contains.hh>
#include <algorithm>
#include <stdexcept>

namespace cola
{
  namespace
  {
    using mark = spot::acc_cond::mark_t;
    using code = spot::acc_cond::acc_code;
    using op = spot::acc_cond::acc_op;
    struct limit {};

    std::vector<mark> fin_clauses(const code& f, unsigned bound)
    {
      if (f.is_t()) return {mark{}};
      if (f.is_f()) return {};
      auto root = f.back().sub.op;
      if (root == op::Fin)
        {
          std::vector<mark> out;
          for (unsigned c : f.used_sets().sets())
            { if (out.size() >= bound) throw limit{}; out.push_back(mark{c}); }
          return out;
        }
      if (root != op::And && root != op::Or) throw limit{};
      std::vector<mark> out = root == op::And ? std::vector<mark>{mark{}} : std::vector<mark>{};
      for (const auto& c : root == op::And ? f.top_conjuncts() : f.top_disjuncts())
        {
          auto rhs = fin_clauses(c, bound);
          if (root == op::Or)
            {
              if (out.size() + rhs.size() > bound) throw limit{};
              out.insert(out.end(), rhs.begin(), rhs.end());
            }
          else
            {
              if (!rhs.empty() && out.size() > bound / rhs.size()) throw limit{};
              std::vector<mark> product;
              for (auto a : out) for (auto b : rhs) product.push_back(a | b);
              out = std::move(product);
            }
        }
      return out;
    }
  }

  colour_choice_result weakify_cobuchi_sccs(
    const spot::const_twa_graph_ptr& input, const cobuchi_weak_options& options)
  {
    colour_choice_result result;
    result.automaton = spot::make_twa_graph(input, spot::twa::prop_set::all());
    if (!input->is_existential()) return result;
    spot::scc_info si(input, spot::scc_info_options::ALL);
    auto types = get_scc_types(si);
    std::vector<std::vector<mark>> plans(si.scc_count());
    unsigned total_states = input->num_states(), total_edges = input->num_edges();
    for (unsigned sc = 0; sc < si.scc_count(); ++sc)
      {
        colour_scc_certificate cert;
        cert.scc = sc; cert.states = si.states_of(sc).size();
        if (types[sc] & SCC_INSIDE_DET_TYPE) cert.reason = "deterministic";
        else if (types[sc] & SCC_WEAK_TYPE) cert.reason = "inherently-weak";
        else
          {
            mark occurring{}, common = input->acc().all_sets();
            for (unsigned q : si.states_of(sc)) for (const auto& e : input->out(q))
              if (si.scc_of(e.dst) == sc && e.cond != bddfalse)
                { occurring |= e.acc; common &= e.acc; }
            auto local = input->acc().get_acceptance()
              .remove(input->acc().all_sets() - occurring, true).remove(common, false);
            if (local.used_inf_fin_sets().first) cert.reason = "requires-recurring-good-colours";
            else if (!options.max_clauses) cert.reason = "clause-budget";
            else if (input->num_sets() + 2 > std::min(options.max_colours, mark::max_accsets()))
              cert.reason = "colour-budget";
            else
              try
                {
                  auto clauses = fin_clauses(local, options.max_clauses);
                  cert.clauses = clauses.size();
                  if (total_states > options.max_states ||
                      clauses.size() > (options.max_states - total_states) / cert.states)
                    cert.reason = "state-budget";
                  else
                    {
                      unsigned added_edges = 0;
                      for (auto bad : clauses)
                        for (unsigned q : si.states_of(sc))
                          for (const auto& e : input->out(q))
                            if (si.scc_of(e.dst) != sc || !(e.acc & bad)) ++added_edges;
                      // Jump after any original internal transition; its mark
                      // belongs to the finite prefix and may still be bad.
                      for (unsigned q : si.states_of(sc)) for (const auto& e : input->out(q))
                        if (si.scc_of(e.dst) == sc) added_edges += clauses.size();
                      if (added_edges > options.max_edges || total_edges > options.max_edges - added_edges)
                        cert.reason = "edge-budget";
                      else
                        {
                          total_edges += added_edges;
                          total_states += clauses.size() * cert.states;
                          plans[sc] = std::move(clauses);
                          cert.reason = "co-buchi-weakified";
                          cert.fresh_colours = 2; // shared across all converted SCCs
                          ++result.rewritten;
                        }
                    }
                }
              catch (const limit&) { cert.reason = "clause-budget"; }
          }
        result.sccs.push_back(std::move(cert));
      }
    if (!result.rewritten) return result;
    unsigned original_selector = input->num_sets(), committed = original_selector + 1;
    auto out = spot::make_twa_graph(input->get_dict()); out->copy_ap_of(input);
    out->new_states(total_states); out->set_init_state(input->get_init_state_number());
    for (const auto& e : input->edges())
      {
        mark colours = e.acc;
        unsigned sc = si.scc_of(e.src);
        if (sc < plans.size() && sc == si.scc_of(e.dst) && plans[sc].empty())
          colours.set(original_selector);
        out->new_edge(e.src, e.dst, e.cond, colours);
      }
    unsigned next = input->num_states();
    for (unsigned sc = 0; sc < plans.size(); ++sc)
      for (auto bad : plans[sc])
        {
          std::vector<unsigned> copy(input->num_states(), 0);
          for (unsigned q : si.states_of(sc)) copy[q] = next++;
          for (unsigned q : si.states_of(sc))
            for (const auto& e : input->out(q))
              if (si.scc_of(e.dst) == sc)
                {
                  out->new_edge(q, copy[e.dst], e.cond);
                  if (!(e.acc & bad)) out->new_edge(copy[q], copy[e.dst], e.cond, {committed});
                }
              else out->new_edge(copy[q], e.dst, e.cond, e.acc);
        }
    out->set_acceptance(committed + 1,
      (code::inf({original_selector}) & input->acc().get_acceptance()) | code::inf({committed}));
    out->merge_edges(); spot::cleanup_acceptance_here(out);
    bool equivalent;
    try { equivalent = spot::are_equivalent(input, out); }
    catch (const std::runtime_error& error)
      {
        if (std::string(error.what()).find("Too many acceptance sets used.") != 0) throw;
        result.rewritten = 0;
        for (auto& c : result.sccs)
          if (c.reason == "co-buchi-weakified") c.reason = "verification-capacity";
        return result;
      }
    if (!equivalent)
      {
        result.equivalent = false; result.rewritten = 0;
        for (auto& c : result.sccs)
          if (c.reason == "co-buchi-weakified") c.reason = "equivalence-rejected";
        return result;
      }
    result.automaton = out;
    return result;
  }
}
