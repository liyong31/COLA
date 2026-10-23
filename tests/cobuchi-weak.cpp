#include "cobuchi_weak.hpp"
#include "cola.hpp"
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/tl/parse.hh>
#include <iostream>
#include <random>
#include <stdexcept>

using mark = spot::acc_cond::mark_t;
using code = spot::acc_cond::acc_code;

static void require(bool ok, const char* why)
{ if (!ok) throw std::runtime_error(why); }

static spot::twa_graph_ptr fixture(const char* acceptance, bool exit)
{
  auto a = spot::make_twa_graph(spot::make_bdd_dict());
  a->new_states(exit ? 3 : 2); a->set_init_state(0);
  a->set_acceptance(2, code(acceptance));
  auto p = bdd_ithvar(a->register_ap("p"));
  auto r = bdd_ithvar(a->register_ap("r"));
  for (unsigned q : {0U,1U})
    {
      bdd stay = bddtrue;
      if (exit) stay = !r;
      a->new_edge(q, 0, p & stay);
      a->new_edge(q, 1, p & stay, {0,1});
      a->new_edge(q, 0, !p & stay, {0,1});
      a->new_edge(q, 1, !p & stay, {0,1});
      if (exit) a->new_edge(q, 2, r);
    }
  if (exit) a->new_edge(2, 2, bddtrue, {0,1});
  return a;
}

int main()
{
  unsigned checked = 0;
  auto unreachable=fixture("Fin(0)",false);
  unsigned unused=unreachable->new_state();unreachable->new_edge(unused,unused,bddtrue,{0});
  auto retained=cola::weakify_cobuchi_sccs(unreachable);
  require(retained.rewritten==1&&retained.automaton->num_states()==5
          &&spot::are_equivalent(unreachable,retained.automaton),"unreachable weakification state lost");
  ++checked;
  for (const char* condition : {"Fin(0)", "Fin(0)&Fin(1)", "Fin(0)|Fin(1)"})
    for (bool exit : {false,true})
      {
        auto input = fixture(condition, exit);
        require(!cola::is_elevator_automaton(input), "fixture already elevator");
        auto result = cola::weakify_cobuchi_sccs(input);
        require(result.rewritten == 1 && result.equivalent, "co-Buchi SCC not converted");
        require(cola::is_elevator_automaton(result.automaton), "weakification remains non-elevator");
        require(spot::are_equivalent(result.automaton,
          spot::parse_infix_psl(exit ? "G!r & FG p" : "FG p").f), "weakification independent oracle mismatch");
        spot::option_map options;
        options.set(USE_SIMULATION,0); options.set(USE_DELAYED_SIMULATION,0);
        auto det = cola::determinize_televator(result.automaton, options);
        require(spot::is_deterministic(det) && spot::are_equivalent(input, det), "weakification backend mismatch");
        ++checked;
      }
  for (unsigned kind = 0; kind < 4; ++kind)
    {
      auto input = fixture("Fin(0)", false);
      cola::cobuchi_weak_options options;
      if (kind == 0) options.max_states = 3;
      if (kind == 1) options.max_edges = 1;
      if (kind == 2) options.max_clauses = 0;
      if (kind == 3) options.max_colours = 2;
      auto r = cola::weakify_cobuchi_sccs(input,options);
      require(!r.rewritten && r.automaton->num_states() == 2 && spot::are_equivalent(input,r.automaton), "budget changed input");
      ++checked;
    }
  auto mixed = fixture("Fin(0)&Inf(1)",false);
  auto unsupported = cola::weakify_cobuchi_sccs(mixed);
  // This particular fixture rejects every path, and is correctly weak already.
  require(!unsupported.rewritten && spot::are_equivalent(mixed,unsupported.automaton), "mixed input changed");
  ++checked;
  auto recurring = spot::make_twa_graph(spot::make_bdd_dict());
  recurring->new_states(2); recurring->set_init_state(0);
  recurring->set_acceptance(2, code("Fin(0)&Inf(1)"));
  auto recurring_p = bdd_ithvar(recurring->register_ap("p"));
  for (unsigned q : {0U,1U})
    {
      recurring->new_edge(q,0,recurring_p,{1}); recurring->new_edge(q,1,recurring_p,{0,1});
      recurring->new_edge(q,0,!recurring_p); recurring->new_edge(q,1,!recurring_p,{0});
    }
  auto not_cobuchi = cola::weakify_cobuchi_sccs(recurring);
  require(!not_cobuchi.rewritten && not_cobuchi.sccs[0].reason == "requires-recurring-good-colours",
          "recurring good obligation was discarded");
  ++checked;
  auto exponential = spot::make_twa_graph(spot::make_bdd_dict());
  exponential->new_states(2); exponential->set_init_state(0);
  code many = code::t(); mark evens{}, odds{};
  for (unsigned i = 0; i < 8; ++i)
    { many &= code::fin({2*i}) | code::fin({2*i+1}); evens.set(2*i); odds.set(2*i+1); }
  exponential->set_acceptance(16,many);
  for (unsigned q : {0U,1U})
    { exponential->new_edge(q,0,bddtrue,evens); exponential->new_edge(q,1,bddtrue,odds); }
  auto bounded = cola::weakify_cobuchi_sccs(exponential);
  require(!bounded.rewritten && bounded.sccs[0].reason == "clause-budget", "co-Buchi DNF budget failed");
  ++checked;
  std::mt19937 rng(20261022);
  for (unsigned sample = 0; sample < 200; ++sample)
    {
      auto a = spot::make_twa_graph(spot::make_bdd_dict());
      a->new_states(3);a->set_init_state(0);
      a->set_acceptance(3, code(sample%2 ? "Fin(0)|(Fin(1)&Fin(2))" : "Fin(0)&(Fin(1)|Fin(2))"));
      auto p = bdd_ithvar(a->register_ap("p"));
      for (unsigned q = 0; q < 3; ++q)
        for (unsigned d = 0; d < 3; ++d)
          for (unsigned letter = 0; letter < 2; ++letter)
            {
              mark m{};unsigned n = rng()%8;
              for (unsigned c = 0; c < 3; ++c) if (n&(1U<<c)) m.set(c);
              a->new_edge(q,d,letter?p:!p,m);
            }
      auto result = cola::weakify_cobuchi_sccs(a);
      require(result.equivalent && spot::are_equivalent(a,result.automaton), "random weakification mismatch");
      require(cola::is_elevator_automaton(result.automaton), "pure Fin input not made elevator");
      ++checked;
    }
  std::cout << checked << " co-Buchi weakification checks passed\n";
}
