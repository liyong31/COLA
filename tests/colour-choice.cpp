#include "colour_choice.hpp"
#include "cola.hpp"
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/tl/parse.hh>
#include <iostream>
#include <random>
#include <stdexcept>

using mark = spot::acc_cond::mark_t;
using code = spot::acc_cond::acc_code;

static mark bits(unsigned n)
{
  mark out{};
  for (unsigned i = 0; n; ++i, n >>= 1) if (n & 1) out.set(i);
  return out;
}

static void require(bool condition, const char* message)
{
  if (!condition) throw std::runtime_error(message);
}

// Enumerate all possible recurrent edge sets. Each recurrent letter must
// choose at least one of its available marks; any selected finite family
// can be scheduled infinitely often. This oracle does not use the rewrite.
static bool accepts_inf_letters(const spot::twa_graph_ptr& a,
                               unsigned choices_p, unsigned choices_n, unsigned letters)
{
  for (unsigned p = 0; p < 16; ++p)
    for (unsigned n = 0; n < 16; ++n)
      {
        if ((p & ~choices_p) || (n & ~choices_n)) continue;
        if ((bool(p) != bool(letters & 1)) || (bool(n) != bool(letters & 2))) continue;
        unsigned emitted = 0;
        for (unsigned m = 0; m < 4; ++m) if ((p | n) & (1U << m)) emitted |= m;
        if (a->acc().accepting(bits(emitted))) return true;
      }
  return false;
}

static spot::twa_graph_ptr oracle(const spot::twa_graph_ptr& source,
                                 unsigned choices_p, unsigned choices_n)
{
  auto a = spot::make_twa_graph(source->get_dict());
  auto p = bdd_ithvar(a->register_ap("p"));
  a->new_state(); a->set_init_state(0);
  a->new_edge(0, 0, p, {0}); a->new_edge(0, 0, !p, {1});
  code acceptance = code::f();
  for (unsigned letters = 1; letters < 4; ++letters)
    if (accepts_inf_letters(source, choices_p, choices_n, letters))
      acceptance |= ((letters & 1) ? code::inf({0}) : code::fin({0}))
                  & ((letters & 2) ? code::inf({1}) : code::fin({1}));
  a->set_acceptance(2, acceptance);
  return a;
}

static spot::twa_graph_ptr exits()
{
  auto a = spot::make_twa_graph(spot::make_bdd_dict());
  a->new_states(4); a->set_init_state(0);
  a->set_acceptance(2, code("Fin(0)&Inf(1)"));
  auto p = bdd_ithvar(a->register_ap("p"));
  auto q = bdd_ithvar(a->register_ap("q"));
  auto r = bdd_ithvar(a->register_ap("r"));
  a->new_edge(0, 1, q); a->new_edge(0, 2, !q);
  for (unsigned s : {1U, 2U})
    {
      bdd good = (s == 1 ? p : !p) & !r;
      a->new_edge(s, s, good, {1});
      a->new_edge(s, s, good, {0, 1});
      a->new_edge(s, s, !good & !r, {0});
      a->new_edge(s, 3, r);
    }
  a->new_edge(3, 3, bddtrue, {0});
  return a;
}

int main()
{
  unsigned checked = 0, rewritten = 0;
  // All 16 acceptance functions on two colours; all nonempty sets of
  // available marks for each of two letters: 16 * 15 * 15 = 3600.
  for (unsigned truth = 0; truth < 16; ++truth)
    for (unsigned cp = 1; cp < 16; ++cp)
      for (unsigned cn = 1; cn < 16; ++cn)
        {
          auto a = spot::make_twa_graph(spot::make_bdd_dict());
          a->new_state(); a->set_init_state(0);
          code acceptance = code::f();
          for (unsigned value = 0; value < 4; ++value)
            if (truth & (1U << value))
              acceptance |= ((value & 1) ? code::inf({0}) : code::fin({0}))
                          & ((value & 2) ? code::inf({1}) : code::fin({1}));
          a->set_acceptance(2, acceptance);
          auto p = bdd_ithvar(a->register_ap("p"));
          for (unsigned m = 0; m < 4; ++m)
            {
              if (cp & (1U << m)) a->new_edge(0, 0, p, bits(m));
              if (cn & (1U << m)) a->new_edge(0, 0, !p, bits(m));
            }
          auto result = cola::eliminate_colour_choices(a);
          auto expected = oracle(a, cp, cn);
          require(result.equivalent && spot::are_equivalent(result.automaton, expected), "exhaustive oracle mismatch");
          require(result.automaton->num_states() == 1, "state count changed");
          require(cola::is_elevator_automaton(result.automaton), "colour SCC remains non-elevator");
          rewritten += result.rewritten;
          ++checked;
        }
  auto a = exits();
  auto unreachable = exits();
  unsigned unused = unreachable->new_state();
  unreachable->new_edge(unused, unused, bddtrue, {0});
  unreachable->new_edge(unused, 1, bddtrue);
  auto preserved = cola::eliminate_colour_choices(unreachable);
  require(preserved.rewritten == 2 && preserved.automaton->num_states() == 5
          && spot::are_equivalent(unreachable,preserved.automaton), "unreachable state was not preserved");
  ++checked;
  auto result = cola::eliminate_colour_choices(a);
  require(result.rewritten == 2 && result.equivalent, "exit fixture did not rewrite both SCCs");
  require(result.automaton->num_states() == a->num_states(), "exit fixture added states");
  require(spot::are_equivalent(result.automaton,
    spot::parse_infix_psl("(q & X(G!r & FG p)) | (!q & X(G!r & FG!p))").f), "SCC guard/exit mismatch");
  spot::option_map backend;
  backend.set(USE_SIMULATION, 0); backend.set(USE_DELAYED_SIMULATION, 0);
  backend.set(USE_OBSERVED_RANKS, 1);
  auto det = cola::determinize_televator(result.automaton, backend);
  require(spot::is_deterministic(det) && spot::are_equivalent(a, det), "native backend mismatch");
  ++checked;
  for (unsigned kind = 0; kind < 4; ++kind)
    {
      cola::colour_choice_options opts;
      if (kind == 0) opts.max_colours = 2;
      if (kind == 1) opts.max_regions = 1;
      if (kind == 2) opts.max_clauses = 0;
      if (kind == 3) opts.max_formula_words = 1;
      auto fallback = cola::eliminate_colour_choices(a, opts);
      require(!fallback.rewritten && fallback.equivalent && spot::are_equivalent(a, fallback.automaton), "budget fallback changed language");
      ++checked;
    }
  auto hard = spot::make_twa_graph(spot::make_bdd_dict());
  hard->new_states(2); hard->set_init_state(0);
  hard->set_acceptance(2, code("Fin(0)&Inf(1)"));
  for (unsigned s : {0U, 1U})
    { hard->new_edge(s, 0, bddtrue, {0}); hard->new_edge(s, 1, bddtrue, {1}); }
  auto rejected = cola::eliminate_colour_choices(hard);
  require(!rejected.rewritten && !rejected.sccs[0].target_deterministic
          && rejected.sccs[0].reason == "multiple-internal-targets", "target overlap not rejected");
  ++checked;
  auto expanded = spot::make_twa_graph(spot::make_bdd_dict());
  expanded->new_state(); expanded->set_init_state(0);
  code condition = code::t(); mark even{}, odd{};
  for (unsigned i = 0; i < 8; ++i)
    { condition &= code::inf({2*i}) | code::fin({2*i+1}); even.set(2*i); odd.set(2*i+1); }
  expanded->set_acceptance(16, condition);
  expanded->new_edge(0, 0, bddtrue, even); expanded->new_edge(0, 0, bddtrue, odd);
  auto bounded = cola::eliminate_colour_choices(expanded);
  require(!bounded.rewritten && bounded.sccs[0].reason == "clause-budget", "DNF expansion was not bounded");
  ++checked;
  // The rewrite itself fits 32 colours, but independent equivalence may
  // require a larger acceptance product. That is a fallback, not a failure.
  auto capacity = spot::make_twa_graph(spot::make_bdd_dict());
  capacity->new_states(3); capacity->set_init_state(2);
  capacity->set_acceptance(8, code("(Fin(5)|Fin(6))&(Inf(4)|Fin(3))&(Inf(7)|Fin(2))&(Inf(1)|Fin(0))"));
  std::vector<bdd> ap;
  for (const char* name : {"a", "b", "c", "d", "e", "f"}) ap.push_back(bdd_ithvar(capacity->register_ap(name)));
  capacity->new_edge(0, 0, ap[0]&!ap[1], {0});
  capacity->new_edge(0, 0, ap[0]&ap[1], {1});
  capacity->new_edge(0, 0, !ap[0], {5,6});
  capacity->new_edge(1, 1, ap[2]&!ap[3]&!ap[5], {2,3,5});
  capacity->new_edge(1, 1, ap[2]&!ap[3]&ap[5], {2,4,5});
  capacity->new_edge(1, 1, ap[2]&!ap[3]&ap[4], {2,6});
  capacity->new_edge(1, 1, !ap[2], {5,6});
  capacity->new_edge(1, 1, ap[2]&ap[3]&!ap[5], {3,5,7});
  capacity->new_edge(1, 1, ap[2]&ap[3]&ap[5], {4,5,7});
  capacity->new_edge(1, 1, ap[2]&ap[3]&ap[4], {6,7});
  capacity->new_edge(2, 0, bddtrue); capacity->new_edge(2, 1, bddtrue);
  auto verification = cola::eliminate_colour_choices(capacity);
  require(verification.equivalent, "capacity fallback was treated as inequivalence");
  if (mark::max_accsets() == 32)
    require(!verification.rewritten && verification.automaton->num_sets() == 8,
            "verification capacity did not retain original automaton");
  ++checked;
  // Multi-state target-deterministic SCCs with recurring mark choices.
  std::mt19937 rng(20261022);
  for (unsigned sample = 0; sample < 100; ++sample)
    {
      auto r = spot::make_twa_graph(spot::make_bdd_dict());
      r->new_states(3); r->set_init_state(0);
      r->set_acceptance(3, code(sample % 2 ? "(Fin(0)&Inf(1))|Inf(2)" : "Fin(0)&(Inf(1)|Fin(2))"));
      auto p = bdd_ithvar(r->register_ap("p"));
      for (unsigned s = 0; s < 3; ++s)
        for (unsigned letter = 0; letter < 2; ++letter)
          for (unsigned choice = 0; choice < 3; ++choice)
            r->new_edge(s, (s + 1 + letter) % 3, letter ? p : !p, bits(rng() % 8));
      auto rewritten_r = cola::eliminate_colour_choices(r);
      require(rewritten_r.equivalent && spot::are_equivalent(r, rewritten_r.automaton), "multi-state mismatch");
      require(rewritten_r.automaton->num_states() == 3 && cola::is_elevator_automaton(rewritten_r.automaton), "multi-state target structure changed");
      ++checked;
    }
  std::cout << checked << " colour-choice checks passed; " << rewritten << " exhaustive SCCs rewritten\n";
}
