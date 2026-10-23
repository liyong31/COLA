#include "cola.hpp"
#include "owl_annotations.hpp"
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/isdet.hh>
#include <iostream>
#include <stdexcept>

static void require(bool b, const char* message)
{
  if (!b) throw std::runtime_error(message);
}

// All three ranked states are in one deterministic, non-weak SCC.
// Their exact languages are S & GF d, b & S & GF d, !b & S & GF d.
// The first is covered by the union of the other two, but neither alone.
static spot::twa_graph_ptr fixture(bool unusual_aps)
{
  auto a = spot::make_twa_graph(spot::make_bdd_dict());
  std::vector<bdd> vars;
  for (const auto& name : (unusual_aps
       ? std::vector<std::string>{"p1", "odd,]", "b", "d"}
       : std::vector<std::string>{"a", "c", "b", "d"}))
    vars.push_back(bdd_ithvar(a->register_ap(name)));
  a->new_states(4); a->set_init_state(3); a->set_buchi();
  a->new_edge(3, 3, bddtrue);
  for (unsigned q = 0; q < 3; ++q) a->new_edge(3, q, bddtrue);
  for (unsigned q = 0; q < 3; ++q)
    for (unsigned mask = 0; mask < 16; ++mask)
      {
        if ((q == 1 && !(mask & 4)) || (q == 2 && (mask & 4))) continue;
        bdd guard = bddtrue;
        for (unsigned j = 0; j < 4; ++j) guard &= (mask & (1U << j)) ? vars[j] : !vars[j];
        auto dst = (mask & 1) ? ((mask & 2) ? 1 : 2) : 0;
        a->new_edge(q, dst, guard, (mask & 8) ? spot::acc_cond::mark_t{0} : spot::acc_cond::mark_t{});
      }
  auto names = new std::vector<std::string>(4, "A[unparsed prefix]");
  for (unsigned q = 0; q < 3; ++q)
    (*names)[q] = "B[([G((p0 & p1) -> Xp2) & G((p0 & !p1) -> X!p2), GFp3], [], [], Fixpoints{}) [C="
      + std::string(q == 0 ? "true" : q == 1 ? "b" : "!b") + "]]";
  a->set_named_prop("state-names", names);
  return a;
}

int main()
{
  unsigned checked = 0;
  for (bool unusual : {false, true})
    {
      auto a = fixture(unusual);
      cola::owl_language_oracle oracle(a);
      require(oracle.stats.certified == 3 && !oracle.stats.rejected, "state languages not certified");
      require(oracle.covers(0, {1, 2}), "joint Boolean coverage was missed");
      require(!oracle.covers(0, {1}) && !oracle.covers(0, {2}), "unsound pair coverage");
      require(!oracle.covers(3, {0, 1, 2}), "unknown prefix used as exact formula");
      checked += 4;
      for (bool annotations : {false, true})
        {
          spot::option_map om;
          om.set(USE_SIMULATION, 0); om.set(USE_STUTTER, 0);
          om.set(USE_DELAYED_SIMULATION, 0); om.set(USE_OBSERVED_RANKS, 1);
          om.set(USE_LOCAL_COLOURS, 1); om.set(USE_EXACT_STATE_LANGUAGES, 0);
          om.set(EXACT_CONTAINMENT_BUDGET, 0); om.set(EXACT_UNION_COVER_LIMIT, 0);
          om.set(EXACT_STATE_LANG_SCC_LIMIT, 0); om.set(USE_OWL_ANNOTATIONS, annotations);
          auto out = cola::determinize_televator(a, om);
          require(spot::is_deterministic(out) && spot::are_equivalent(a, out), "annotation determinisation mismatch");
          if (annotations)
            {
              auto stats = out->get_named_prop<cola::owl_annotation_stats>("cola-owl-annotation-stats");
              require(stats && stats->certified == 3 && stats->union_proofs,
                      "annotations did not prove coverage with exact checking disabled");
            }
          ++checked;
        }
      for (auto invalid : {"B[", "B[ ]", "B[([], [], [], Fixpoints{}) [C=false]]",
                           "B[([Gp999], [], [], Fixpoints{}) []]"})
        {
          auto b = fixture(unusual);
          (*b->get_named_prop<std::vector<std::string>>("state-names"))[0] = invalid;
          cola::owl_language_oracle bad(b);
          require(!bad.known(0) && !bad.covers(0, {1, 2}), "invalid annotation enabled deletion");
          ++checked;
        }
    }
  // EKS20 safety and pending-round-robin fields, plus indexed AP mapping.
  auto a = spot::make_twa_graph(spot::make_bdd_dict());
  auto p = bdd_ithvar(a->register_ap("actual"));
  a->new_state(); a->set_init_state(0); a->set_buchi(); a->new_edge(0, 0, p, {0});
  for (const auto& label : {"B[<[], []> [GWR=Gactual]]",
                          "B[<[], [GFp0]> [GWR=Gactual, FUM=RoundRobinState{index=0, state=Factual}]]"})
    {
      a->set_named_prop("state-names", new std::vector<std::string>{label});
      cola::owl_language_oracle symmetric(a);
      require(symmetric.stats.certified == 1, "symmetric label not certified"); ++checked;
    }
  for (const auto& op : {"U", "W", "R", "M"})
    {
      std::string label = "B[([G(p0" + std::string(op) + "p0)], [], [], Fixpoints{}) []]";
      a->set_named_prop("state-names", new std::vector<std::string>{label});
      cola::owl_language_oracle adjacent(a);
      require(adjacent.stats.certified == 1, "unspaced indexed temporal operator was not decoded"); ++checked;
    }
  std::cout << checked << " OWL annotation certification and coverage regressions passed\n";
}
