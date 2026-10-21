// Experimental raw TELA boundary. No LTL routing or fallback can mask errors.
#include "cola.hpp"
#include <spot/parseaut/public.hh>
#include <spot/tl/parse.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/isdet.hh>
#include <iostream>
#include <stdexcept>
#include <string>

int main(int argc, char** argv)
{
  if (argc < 3 || argc > 5) return 1;
  bool integrated = false, compact = false;
  for (int i = 3; i < argc; ++i)
    if (std::string(argv[i]) == "--integrated") integrated = true;
    else if (std::string(argv[i]) == "--compact-ranks") compact = true;
    else return 1;
  try
    {
      auto dict = spot::make_bdd_dict();
      auto parsed = spot::parse_aut(argv[1], dict);
      auto formula = spot::parse_infix_psl(argv[2]);
      if (!parsed || parsed->format_errors(std::cerr) || !parsed->aut
          || formula.format_errors(std::cerr)) return 1;
      auto input = parsed->aut;
      if (!input->is_existential() || input->num_states() > 256) return 5;
      spot::scc_info si(input, spot::scc_info_options::ALL);
      auto types = cola::get_scc_types(si);
      unsigned hard = 0, weak = 0, deterministic_sccs = 0;
      for (auto t : types)
        {
          if (t & SCC_WEAK_TYPE) ++weak;
          else if (t & SCC_INSIDE_DET_TYPE) ++deterministic_sccs;
          else ++hard;
        }
      std::cerr << "input-sccs: " << si.scc_count()
                << "\ninput-weak-sccs: " << weak
                << "\ninput-deterministic-sccs: " << deterministic_sccs
                << "\ninput-hard-sccs: " << hard << '\n';
      if (!spot::are_equivalent(input, formula.f)) return 3;
      std::cerr << "input-equivalent: 1\n";
      if (!cola::is_elevator_automaton(input)) return 2;
      bool deterministic = spot::is_deterministic(input);
      std::cerr << "input-deterministic: " << deterministic << '\n';
      spot::option_map options;
      options.set(USE_SIMULATION, 0);
      options.set(USE_DELAYED_SIMULATION, 0);
      options.set(USE_STUTTER, 0);
      options.set(USE_EXACT_STATE_LANGUAGES, 1);
      // Historical raw measurements used only the options above. The new
      // shape ablation can also match the integrated boundary's SCC pruning.
      options.set(USE_SCC_INFO, integrated);
      options.set(USE_OBSERVED_RANKS, compact);
      auto output = deterministic ? input : cola::determinize_televator(input, options);
      spot::print_hoa(std::cout, output);
      if (!spot::is_deterministic(output) || !spot::are_equivalent(input, output)) return 4;
      return 0;
    }
  catch (const std::runtime_error& error)
    {
      std::cerr << error.what() << '\n';
      return 6;
    }
}
