#include "cola.hpp"
#include <iostream>
#include <stdexcept>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/isdet.hh>

// Several deterministic components compete for ranked runs. Their lifetimes
// and colours are independent; some ranks disappear and are spawned again.
static spot::twa_graph_ptr fixture(const char* acceptance)
{
  auto a = spot::make_twa_graph(spot::make_bdd_dict());
  a->new_state();
  a->set_init_state(0);
  a->set_acceptance(4, spot::acc_cond::acc_code(acceptance));
  a->new_edge(0, 0, bddtrue);
  for (unsigned size : {1U, 2U})
    {
      auto guard = bdd_ithvar(a->register_ap("g" + std::to_string(size)));
      auto p = bdd_ithvar(a->register_ap("p" + std::to_string(size)));
      auto q = bdd_ithvar(a->register_ap("q" + std::to_string(size)));
      auto start = a->new_states(size);
      a->new_edge(0, start, bddtrue);
      for (unsigned j = 0; j < size; ++j)
        for (unsigned mask = 0; mask < 4; ++mask)
          {
            auto label = guard & ((mask & 1) ? p : !p) & ((mask & 2) ? q : !q);
            spot::acc_cond::mark_t marks;
            if (mask & 1) marks.set(0);
            if (mask & 2) marks.set(1);
            if (mask == 0) marks.set(2);
            // Colour 3 is declared but never emitted.
            a->new_edge(start + j, start + (j + 1) % size, label, marks);
          }
    }
  return a;
}

static spot::twa_graph_ptr rejecting_fin_scc()
{
  auto a = spot::make_twa_graph(spot::make_bdd_dict());
  a->new_states(3);
  a->set_init_state(0);
  a->set_acceptance(2, spot::acc_cond::acc_code("Fin(0)&Fin(1)"));
  auto p = bdd_ithvar(a->register_ap("p"));
  auto q = bdd_ithvar(a->register_ap("q"));
  a->new_edge(0, 0, bddtrue, {0});
  a->new_edge(0, 1, bddtrue);
  a->new_edge(1, 1, p, {0});
  a->new_edge(1, 1, !p, {1});
  a->new_edge(1, 2, q);
  a->new_edge(2, 2, bddtrue);
  a->prop_complete(true);
  return a;
}

int main()
{
  unsigned checked = 0;
  for (const char* condition : {"Inf(0)", "Fin(0)", "Inf(0)&Fin(1)",
       "Fin(0)|Inf(1)", "(Inf(0)&Fin(1))|(Fin(0)&Inf(2))",
       "(Inf(0)|Fin(1))&(Inf(2)|Fin(3))", "Inf(3)", "Fin(3)", "t", "f"})
    for (bool exact : {false, true})
      {
        auto aut = fixture(condition);
        if (!cola::is_elevator_automaton(aut))
          throw std::runtime_error("fixture is not elevator");
        spot::option_map options;
        options.set(USE_EXACT_STATE_LANGUAGES, exact);
        options.set(USE_SIMULATION, 0);
        options.set(USE_DELAYED_SIMULATION, 0);
        auto result = cola::determinize_televator(aut, options);
        if (!spot::is_deterministic(result) || !spot::are_equivalent(aut, result))
          throw std::runtime_error(std::string("generic elevator mismatch: ") + condition);
        ++checked;
      }
  for (bool exact : {false, true})
    {
      auto aut = rejecting_fin_scc();
      spot::option_map options;
      options.set(USE_EXACT_STATE_LANGUAGES, exact);
      auto result = cola::determinize_televator(aut, options);
      if (!spot::is_deterministic(result) || !spot::are_equivalent(aut, result))
        throw std::runtime_error("rejecting Fin SCC mismatch");
      ++checked;
    }
  std::cout << checked << " generic elevator acceptance regressions passed\n";
}
