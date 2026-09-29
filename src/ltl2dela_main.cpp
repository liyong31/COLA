// Copyright (C) 2026  The COLA Authors
//
// Command-line front-end for profile-guided LTL -> DELA translation.

#include "config.h"

#include "ltl2dela.hpp"

#include <spot/misc/version.hh>
#include <spot/tl/parse.hh>
#include <spot/twaalgos/hoa.hh>

#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace
{
  void usage(std::ostream& out)
  {
    out <<
R"(Usage:
  ltl2dela [OPTIONS] FORMULA
  ltl2dela [OPTIONS] -f FORMULA
  ltl2dela [OPTIONS] -F FILE

Translate LTL to a deterministic automaton with generic (Emerson-Lei)
acceptance.  The translator first exploits Spot's easy deterministic
fragments, then tries a Buchi automaton and CoLA's elevator-SCC
construction.  Hard residuals are refined with asymptotic profiles
FG(gamma) / GF(!gamma) before falling back to direct deterministic
formula translation.

Options:
  -f FORMULA              translate one formula
  -F FILE                 translate one formula per nonempty, non-comment line
  -o FILE                 write output to FILE (single-formula mode)
  --profile-depth=N       maximum recursive profile depth (default: 4)
  --profile-budget=N      maximum number of selected profile splits (default: 24)
  --profile-lookahead=N   number of separator candidates scored per residual
  --guard-max-length=N    maximum printed length of a separator formula
  --no-profiles           disable SCC-guided profile refinement
  --no-delta2             disable Spot's Delta2 normalization
  --no-recurrence         disable structural GF recurrence compilation
  --no-master-profiles     disable explicit Master-profile propagation
  --no-annotations        disable match_states() formula annotations
  --no-exact-languages    disable exact state-language containment
  --exact-scc-limit=N     exact containment only in DA SCCs of size <= N
  --exact-union-limit=N   exact union cover uses at most N earlier runs
  --exact-budget=N        maximum exact containment queries
  --no-boolean-split      disable top-level Boolean decomposition
  --allow-flat-profiles   accept a split even without measured SCC improvement
  --stats                 print translation statistics to stderr
  -v, --verbose           show selected profile splits
  -h, --help              show this help
  --version               show versions
)";
  }

  unsigned parse_uint(const std::string& s, const std::string& name)
  {
    try
      {
        std::size_t p = 0;
        unsigned long x = std::stoul(s, &p);
        if (p != s.size())
          throw std::invalid_argument("suffix");
        return static_cast<unsigned>(x);
      }
    catch (...)
      {
        throw std::runtime_error("invalid value for " + name + ": " + s);
      }
  }

  std::vector<std::string> read_formulae(const std::string& path)
  {
    std::ifstream in(path);
    if (!in)
      throw std::runtime_error("cannot open formula file: " + path);

    std::vector<std::string> out;
    std::string line;
    while (std::getline(in, line))
      {
        auto first = line.find_first_not_of(" \t\r\n");
        if (first == std::string::npos)
          continue;
        if (line[first] == '#')
          continue;
        out.emplace_back(line.substr(first));
      }
    return out;
  }

  spot::formula parse(const std::string& text)
  {
    spot::parsed_formula pf = spot::parse_infix_psl(text);
    if (pf.format_errors(std::cerr))
      throw std::runtime_error("invalid LTL formula");
    if (!pf.f.is_ltl_formula())
      throw std::runtime_error("input is PSL but not LTL");
    return pf.f;
  }
}

int main(int argc, char** argv)
{
  try
    {
      cola::ltl2dela_options opts;
      bool show_stats = false;
      std::string formula_arg;
      std::string file_arg;
      std::string output_arg;

      for (int i = 1; i < argc; ++i)
        {
          std::string a = argv[i];

          auto value_after = [&](const std::string& prefix) -> std::string
            {
              return a.substr(prefix.size());
            };

          if (a == "-h" || a == "--help")
            {
              usage(std::cout);
              return 0;
            }
          if (a == "--version")
            {
              std::cout << "ltl2dela (COLA) using Spot "
                        << spot::version() << '\n';
              return 0;
            }
          if (a == "-v" || a == "--verbose")
            {
              ++opts.verbose;
              continue;
            }
          if (a == "--stats")
            {
              show_stats = true;
              continue;
            }
          if (a == "--no-profiles")
            {
              opts.use_profiles = false;
              continue;
            }
          if (a == "--no-delta2")
            {
              opts.use_delta2 = false;
              continue;
            }
          if (a == "--no-recurrence")
            {
              opts.use_recurrence_compiler = false;
              continue;
            }
          if (a == "--no-master-profiles")
            {
              opts.use_master_profiles = false;
              continue;
            }
          if (a == "--no-master-profiles")
            {
              opts.use_master_profiles = false;
              continue;
            }
          if (a == "--no-annotations")
            {
              opts.use_state_annotations = false;
              continue;
            }
          if (a == "--no-exact-languages")
            {
              opts.use_exact_state_languages = false;
              continue;
            }
          if (a.rfind("--exact-scc-limit=", 0) == 0)
            {
              opts.exact_state_lang_scc_limit =
                parse_uint(value_after("--exact-scc-limit="),
                           "--exact-scc-limit");
              continue;
            }
          if (a.rfind("--exact-union-limit=", 0) == 0)
            {
              opts.exact_union_cover_limit =
                parse_uint(value_after("--exact-union-limit="),
                           "--exact-union-limit");
              continue;
            }
          if (a.rfind("--exact-budget=", 0) == 0)
            {
              opts.exact_containment_budget =
                parse_uint(value_after("--exact-budget="),
                           "--exact-budget");
              continue;
            }
          if (a == "--no-boolean-split")
            {
              opts.boolean_decomposition = false;
              continue;
            }
          if (a == "--allow-flat-profiles")
            {
              opts.require_profile_progress = false;
              continue;
            }
          if (a.rfind("--profile-depth=", 0) == 0)
            {
              opts.profile_depth =
                parse_uint(value_after("--profile-depth="), "--profile-depth");
              continue;
            }
          if (a.rfind("--profile-budget=", 0) == 0)
            {
              opts.profile_budget =
                parse_uint(value_after("--profile-budget="), "--profile-budget");
              continue;
            }
          if (a.rfind("--profile-lookahead=", 0) == 0)
            {
              opts.profile_lookahead =
                parse_uint(value_after("--profile-lookahead="),
                           "--profile-lookahead");
              continue;
            }
          if (a.rfind("--guard-max-length=", 0) == 0)
            {
              opts.profile_guard_max_length =
                parse_uint(value_after("--guard-max-length="),
                           "--guard-max-length");
              continue;
            }
          if (a == "-f")
            {
              if (++i >= argc)
                throw std::runtime_error("-f requires a formula");
              formula_arg = argv[i];
              continue;
            }
          if (a == "-F")
            {
              if (++i >= argc)
                throw std::runtime_error("-F requires a filename");
              file_arg = argv[i];
              continue;
            }
          if (a == "-o")
            {
              if (++i >= argc)
                throw std::runtime_error("-o requires a filename");
              output_arg = argv[i];
              continue;
            }
          if (!a.empty() && a[0] == '-')
            throw std::runtime_error("unknown option: " + a);
          if (!formula_arg.empty())
            throw std::runtime_error("multiple formula arguments");
          formula_arg = a;
        }

      if (!formula_arg.empty() && !file_arg.empty())
        throw std::runtime_error("use either a formula or -F FILE, not both");

      std::vector<std::string> input;
      if (!file_arg.empty())
        input = read_formulae(file_arg);
      else if (!formula_arg.empty())
        input.push_back(formula_arg);
      else
        {
          std::ostringstream ss;
          ss << std::cin.rdbuf();
          auto text = ss.str();
          if (!text.empty())
            input.push_back(text);
        }

      if (input.empty())
        {
          usage(std::cerr);
          return 2;
        }

      if (!output_arg.empty() && input.size() != 1)
        throw std::runtime_error("-o is supported only for one formula");

      auto dict = spot::make_bdd_dict();
      cola::ltl2dela_translator translator(dict, opts);

      std::ofstream fout;
      std::ostream* out = &std::cout;
      if (!output_arg.empty())
        {
          fout.open(output_arg);
          if (!fout)
            throw std::runtime_error("cannot open output file: " + output_arg);
          out = &fout;
        }

      bool first = true;
      for (const auto& text: input)
        {
          auto f = parse(text);
          auto aut = translator.run(f);

          if (!first)
            *out << '\n';
          first = false;

          spot::print_hoa(*out, aut) << '\n';

          if (show_stats || opts.verbose)
            translator.stats().print(std::cerr);
        }

      return 0;
    }
  catch (const std::exception& e)
    {
      std::cerr << "ltl2dela: " << e.what() << '\n';
      return 2;
    }
}
