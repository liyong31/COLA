#include "ltl2dela.hpp"

#include <iostream>
#include <stdexcept>
#include <spot/tl/parse.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/isdet.hh>

int main()
{
  unsigned checked = 0;
  auto check = [&](const char* text, cola::ltl2dela_options options,
                   unsigned max_states, unsigned route)
    {
      auto parsed = spot::parse_infix_psl(text);
      if (parsed.format_errors(std::cerr))
        throw std::runtime_error("invalid regression formula");
      cola::ltl2dela_translator translator(spot::make_bdd_dict(), options);
      auto aut = translator.run(parsed.f);
      if (!spot::is_deterministic(aut)
          || !spot::are_equivalent(aut, parsed.f)
          || aut->num_states() > max_states)
        throw std::runtime_error(std::string("specialized language/size failure: ") + text);
      const auto& stats = translator.stats();
      if ((route == 1 && stats.boolean_gf_fg_components != 1)
          || (route == 2 && stats.specialized_gf_components != 1)
          || (route == 3 && stats.specialized_fg_components != 1)
          || (route == 4 && (!stats.dba_components || !aut->acc().is_buchi()))
          || (route == 5 && stats.dba_components)
          || (route == 6 && stats.acceptance_limit_fallbacks != 1)
          || (route != 6 && stats.master_profile_splits != 0))
        throw std::runtime_error(std::string("specialized routing failure: ") + text);
      ++checked;
    };
  cola::ltl2dela_options options;
  check("GF a", options, 1, 1);
  check("FG a", options, 1, 1);
  check("GF a | FG b", options, 1, 1);
  check("!(GF a & FG b)", options, 1, 1);
  check("(FGa & GFb) | (((FGc & GFd) | FGe | GFf) & (FGg | GFh))",
        options, 1, 1);
  check("GF(a & X X b)", options, 4, 2);
  check("FG(!a | X X !b)", options, 4, 3);
  check("G(a -> F b)", options, 2, 4);
  check("G(a -> F b) & G(c -> X d)", options, 8, 4);
  check("G(a -> X b)", options, 3, 0);
  check("F(a & X b)", options, 4, 0);
#if SPOT_MAX_ACCSETS == 32
  // Real profile products can exhaust the installed mark capacity after
  // several successful branches.  Fallback must restart the whole formula.
  check("G(!a | ((!b | (!c U (!c & d & !e & X((!c & !e) U f)))) U "
        "(c | G(!b | (d & !e & X(!e U f))))))", options, 13, 6);
#endif

  // Both zero budgets and an unsuccessful recognition attempt must keep
  // the original language.  DBA recognizability is not assumed for all LTL.
  options.dba_state_limit = 0;
  check("G(a -> F b)", options, 4, 5);
  options.dba_state_limit = 1;
  check("G(a -> F b)", options, 4, 5);
  options.dba_state_limit = 512;
  options.dba_cycle_limit = 0;
  check("G(a -> F b)", options, 4, 5);
  options.dba_cycle_limit = 4096;
  options.use_dba = false;
  check("G(a -> F b)", options, 4, 5);
  check("FG a", options, 1, 1);
  std::cout << checked << " specialized fragment language/routing regressions passed\n";
}
