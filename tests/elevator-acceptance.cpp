#include "cola.hpp"

#include <iostream>
#include <stdexcept>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/isdet.hh>

// Each branch is a deterministic nonweak accepting cycle.  The initial
// state can spawn fresh runs forever, while !guard kills all runs in a
// branch.  Thus a branch's rank-discontinuation colours cannot be borrowed
// from a different SCC, even when both have the same local rank number.
static spot::twa_graph_ptr
branches(const std::vector<unsigned>& sizes, bool weak)
{
  auto aut = spot::make_twa_graph(spot::make_bdd_dict());
  aut->new_state();
  aut->set_init_state(0);
  aut->set_buchi();
  aut->new_edge(0, 0, bddtrue);
  for (unsigned i = 0; i < sizes.size(); ++i)
    {
      auto guard = bdd_ithvar(aut->register_ap("g" + std::to_string(i)));
      auto accept = bdd_ithvar(aut->register_ap("a" + std::to_string(i)));
      unsigned first = aut->new_states(sizes[i]);
      aut->new_edge(0, first, bddtrue);
      for (unsigned j = 0; j < sizes[i]; ++j)
        {
          unsigned next = first + (j + 1) % sizes[i];
          aut->new_edge(first + j, next, guard & accept, {0});
          aut->new_edge(first + j, next, guard & !accept);
        }
    }
  if (weak)
    {
      unsigned s = aut->new_state();
      auto guard = bdd_ithvar(aut->register_ap("w"));
      aut->new_edge(0, s, bddtrue);
      aut->new_edge(s, s, guard, {0});
    }
  return aut;
}

int main()
{
  unsigned checked = 0;
  for (const auto& sizes : {std::vector<unsigned>{1, 1},
                            std::vector<unsigned>{1, 2},
                            std::vector<unsigned>{2, 1},
                            std::vector<unsigned>{1, 2, 3}})
    for (bool weak : {false, true})
      {
        auto aut = branches(sizes, weak);
        spot::scc_info si(aut);
        auto types = cola::get_scc_types(si);
        unsigned da = 0;
        for (auto t : types)
          if ((t & SCC_ACC) && (t & SCC_INSIDE_DET_TYPE)
              && !(t & SCC_WEAK_TYPE))
            ++da;
        if (da != sizes.size() || !cola::is_elevator_automaton(aut))
          throw std::runtime_error("fixture lost its deterministic accepting SCCs");
        // Bypass the LTL front-end and its validation fallback entirely.
        spot::option_map options;
        auto det = cola::determinize_televator(aut, options);
        if (!spot::is_deterministic(det) || !spot::are_equivalent(aut, det))
          {
            std::cerr << "elevator acceptance mismatch: case " << checked
                      << ", DA SCCs=" << da << ", weak=" << weak << '\n';
            return 1;
          }
        ++checked;
      }
  std::cout << checked << " raw elevator acceptance regressions passed\n";
}
