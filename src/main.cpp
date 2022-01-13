// Copyright (C) 2019-2020  The Seminator Authors
// Copyright (C) 2022  The COLA Authors
//
// This file is a part of cola, a tool for complementation and determinization
// of omega automata.
//
// cola is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// cola is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "config.h"

#include "cola.hpp"
#include "composer.hpp"
#include "optimizer.hpp"
#include "decomposer.hpp"
#include "simulation.hpp"

#include <unistd.h>
#include <fstream>
#include <ctime>
#include <string>
#include <sstream>

#include <spot/twaalgos/simulation.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/isunamb.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/zlktree.hh>
#include <spot/misc/version.hh>

void print_usage(std::ostream &os)
{
  os << "Usage: cola [OPTION...] [FILENAME...]\n";
}

void print_help()
{
  print_usage(std::cout);
  std::cout <<
      R"(The tool transforms TLDBA/TBA into equivalent deterministic automata.

By default, it reads a Büchi automaton from standard input
and converts it into deterministic automata.

Input options:
    -f FILENAME reads the input from FILENAME instead of stdin
    --determinize=[spot|ldba|eba|ba|cola]
                    Use Spot or our algorithm for ldba, eba and ba or let cola decide which one to obtain deterministic automata
    --type 
            Output the type of the input Buchi automaton: limit-deterministic, cut-deterministic, unambiguous or none of them
    --unambiguous
            Check whether the input is unambiguous and use this fact in determinization

Output options:
    --verbose=[INT] Output verbose level (0 = minimal level, 1 = meduim level, 2 = debug level)
    -o FILENAME Write the output to FILENAME instead of stdout
    --generic   Output the automaton with Emenson-Lei acceptance condition (Default)
    --rabin     Output the automaton with Rabin acceptance condition
    --parity    Output the automaton with Pairty acceptance condition
    --acd       Use alternating cylcle decomposition to obtain parity automaton (Default)


Optimizations:
    --simulation          Use direct simulation for determinization
    --stutter             Use stutter invariance for determinization
    --use-scc             Use SCC information for determinization (Spot) or macrostates merging (COLA)
    --more-acc-egdes      Enumerate elementary cycles for obtaining more accepting egdes 
    --delayed-sim         Use delayed simulation for determinization
    --decompose=[NUM-SCC] Use SCC decomposition to determinizing small BAs (deprecated)

Pre- and Post-processing:
    --preprocess[=0|1|2|3]       Simplify the input automaton at different level (default=1)
    --postprocess-det[=0|1|2|3]  Simplify the output of the determinization
                             (default=1)
    --num-states=[INT]       Simplify the output with number of states less than INT 
                             (default: 30000)

Miscellaneous options:
  -h, --help    Print this help
  --version     Print program version
)";
}

void check_cout()
{
  std::cout.flush();
  if (!std::cout)
  {
    std::cerr << "cola: error writing to standard output\n";
    exit(2);
  }
}

unsigned
parse_int(const std::string &arg)
{
  unsigned result;
  // obtain the substring after '='
  std::size_t idx = arg.find('=');
  //std::cout << "Index of = : " << idx << std::endl;
  std::string number = arg.substr(idx + 1, arg.length());
  std::istringstream iss(number);
  iss >> result;
  return result;
}

// determinization
enum determinize_t
{
  NoDeterminize = 0,
  NBA,
  COLA,
  LDBA,
  EBA, // elevator Buchi automata
  Spot
};

spot::twa_graph_ptr
to_deterministic(spot::twa_graph_ptr aut, spot::option_map &om, unsigned aut_type, determinize_t algo)
{
  // determinization
  spot::twa_graph_ptr res;
  if (algo == COLA)
  {
    if (aut_type & INHERENTLY_WEAK)
      res = cola::determinize_twba(aut, om);
    else if (aut_type & LIMIT_DETERMINISTIC)
      res = cola::determinize_televator(aut, om);
    else if (aut_type & ELEVATOR)
      res = cola::determinize_televator(aut, om);
    else
      res = cola::determinize_tnba(aut, om);
  }
  else if (algo == LDBA)
  {
    res = cola::determinize_tldba(aut, om);
  }else if (algo == EBA)
  {
    res = cola::determinize_televator(aut, om);
  }
  else if (algo == NBA)
  {
    res = cola::determinize_tnba(aut, om);
  }
  else if (algo == Spot)
  {
    // pretty_print, use_scc, use_simulation, use_stutter, aborter
    res = spot::tgba_determinize(aut, om.get(VERBOSE_LEVEL) >= 2, om.get(USE_SCC_INFO) > 0, om.get(USE_SIMULATION) > 0, om.get(USE_STUTTER), nullptr);
    if (om.get(VERBOSE_LEVEL) >= 2)
    {
      cola::output_file(res, "dpa_spot.hoa");
    }
  }
  return res;
}

int main(int argc, char *argv[])
{
  // Declaration for input options. The rest is in cola.hpp
  // as they need to be included in other files.
  bool cd_check = false;
  bool high = false;
  std::vector<std::string> path_to_files;

  spot::option_map om;
  // default setting
  om.set(USE_SIMULATION, 0);
  om.set(USE_STUTTER, 0);
  om.set(USE_UNAMBIGUITY, 0);
  om.set(USE_SCC_INFO, 0);
  om.set(VERBOSE_LEVEL, 0);
  om.set(USE_DELAYED_SIMULATION, 0);
  om.set(MORE_ACC_EDGES, 0);

  // Will be deleted
  //  --scc-mem-limit=[INT] 
  //          The memory limit (MB) for computing the SCC reachability (default = 0, no limit)
  //  --scc-num-limit=[INT] 
  //          The largest number of SCCs in the deterministic automaton for merging macrostates (default = 0, no limit)
  om.set(SCC_REACH_MEMORY_LIMIT, 0);
  om.set(NUM_SCC_LIMIT_MERGER, 0);

  determinize_t determinize = NoDeterminize;

  // options
  bool use_simulation = false;
  //bool merge_transitions = false;
  bool debug = false;
  bool aut_type = false;
  bool use_unambiguous = false;
  bool use_stutter = false;
  bool decompose = false;
  bool use_acd = false;

  enum postprocess_level
  {
    None = 0,
    Low,
    Medium,
    High
  };
  postprocess_level preprocess = Low;
  postprocess_level post_process = Low;
  bool use_scc = false;
  unsigned num_post = 30000;

  enum output_aut_type
  {
    Generic = 0,
    Rabin,
    Parity
  };

  output_aut_type output_type = Generic; 

  std::string output_filename = "";

  for (int i = 1; i < argc; i++)
  {
    std::string arg = argv[i];
    if (arg.find("--preprocess=") != std::string::npos)
    {
      unsigned level = parse_int(arg);
      if (level == 0)
      {
        preprocess = None;
      }else if (level == 1)
      {
        preprocess = Low;
      }else if (level == 2)
      {
        preprocess = Medium;
      }else if (level == 3)
      {
        preprocess = High;
      }
    }else if (arg.find("--postprocess-det=") != std::string::npos)
    {
      unsigned level = parse_int(arg);
      if (level == 0)
      {
        post_process = None;
      }else if (level == 1)
      {
        post_process = Low;
      }else if (level == 2)
      {
        post_process = Medium;
      }else if (level == 3)
      {
        post_process = High;
      }
    }
    else if (arg == "--generic")
    {
      output_type = Generic;
    }else if (arg == "--parity")
    {
      output_type = Parity;
    }else if (arg == "--rabin")
    {
      output_type = Rabin;
    }else if (arg == "--simulation")
    {
      use_simulation = true;
      om.set(USE_SIMULATION, 1);
    }
    else if (arg == "--delayed-sim")
    {
      om.set(USE_DELAYED_SIMULATION, 1);
    }
    else if (arg == "--use-scc")
    {
      use_scc = true;
      om.set(USE_SCC_INFO, 1);
    }
    else if (arg == "--more-acc-edges")
    {
      om.set(MORE_ACC_EDGES, 1);
    }
    else if (arg == "--decompose")
    {
      decompose = true;
      om.set(NUM_NBA_DECOMPOSED, -1);
    }
    else if (arg.find("--decompose=") != std::string::npos)
    {
      decompose = true;
      unsigned num_scc = parse_int(arg);
      om.set(NUM_NBA_DECOMPOSED, num_scc);
    }else if (arg == "--acd")
    {
      use_acd = true;
    }
    // Prefered output
    else if (arg == "--d")
      debug = true;
    // else if (arg == "--merge-transitions")
    //   merge_transitions = true;
    else if (arg == "--type")
      aut_type = true;
    else if (arg == "--unambiguous")
    {
      use_unambiguous = true;
      om.set(USE_UNAMBIGUITY, 1);
    }
    else if (arg == "--stutter")
    {
      use_stutter = true;
      om.set(USE_STUTTER, 1);
    }
    else if (arg == "--determinize=ba")
      determinize = NBA;
    else if (arg == "--determinize=ldba")
      determinize = LDBA;
    else if (arg == "--determinize=eba")
      determinize = EBA;
    else if (arg == "--determinize=spot")
      determinize = Spot;
    else if (arg == "--determinize=cola")
      determinize = COLA;
    else if (arg == "-f")
    {
      if (argc < i + 1)
      {
        std::cerr << "cola: Option -f requires an argument.\n";
        return 1;
      }
      else
      {
        path_to_files.emplace_back(argv[i + 1]);
        i++;
      }
    }
    else if (arg == "-o")
    {
      if (argc < i + 1)
      {
        std::cerr << "cola: Option -o requires an argument.\n";
        return 1;
      }
      else
      {
        std::string str(argv[i + 1]);
        output_filename = str;
        i++;
      }
    }
    else if (arg.find("--num-states=") != std::string::npos)
    {
      // obtain the substring after '='
      num_post = parse_int(arg);
      //std::cout << "Input number : " << num_post << std::endl;
    }
    else if (arg.find("--verbose=") != std::string::npos)
    {
      om.set(VERBOSE_LEVEL, parse_int(arg));
    }
    else if (arg.find("--scc-mem-limit=") !=  std::string::npos)
    {
      om.set(SCC_REACH_MEMORY_LIMIT, parse_int(arg));
    }
    else if (arg.find("--scc-num-limit=") !=  std::string::npos)
    {
      om.set(NUM_SCC_LIMIT_MERGER, parse_int(arg));
    }
    else if ((arg == "--help") || (arg == "-h"))
    {
      print_help();
      check_cout();
      return 0;
    }
    else if (arg == "--version")
    {
      std::cout << "cola " PACKAGE_VERSION
                   " (using Spot "
                << spot::version() << ")\n\n"
                                      "Copyright (C) 2020  The cola Authors.\n"
                                      "License GPLv3+: GNU GPL version 3 or later"
                                      " <http://gnu.org/licenses/gpl.html>.\n"
                                      "This is free software: you are free to change "
                                      "and redistribute it.\n"
                                      "There is NO WARRANTY, to the extent permitted by law.\n"
                << std::flush;
      return 0;
    }
    // removed
    else if (arg == "--cy")
    {
      std::cerr << ("cola: "
                    "Invalid option --cy. Use --via-sba -s0 instead.\n");
      return 2;
    }
    // Detection of unsupported options
    else if (arg[0] == '-')
    {
      std::cerr << "cola: Unsupported option " << arg << '\n';
      return 2;
    }
    else
    {
      path_to_files.emplace_back(argv[i]);
    }
  }
  //path_to_files.push_back("base_formula_130_0.hoa");
  //determinize = Parity;
  if (path_to_files.empty())
  {
    if (isatty(STDIN_FILENO))
    {
      std::cerr << "cola: No automaton to process? "
                   "Run 'cola --help' for more help.\n";
      print_usage(std::cerr);
      return 1;
    }
    else
    {
      // Process stdin by default.
      path_to_files.emplace_back("-");
    }
  }
  //path_to_files.push_back("formula_52_nba.hoa");

  auto dict = spot::make_bdd_dict();

  for (std::string &path_to_file : path_to_files)
  {
    if (om.get(VERBOSE_LEVEL))
      std::cout << "File: " << path_to_file << " Algo: " << determinize << std::endl;
    spot::automaton_stream_parser parser(path_to_file);

    for (;;)
    {
      spot::parsed_aut_ptr parsed_aut = parser.parse(dict);

      if (parsed_aut->format_errors(std::cerr))
        return 1;

      // input automata
      spot::twa_graph_ptr aut = parsed_aut->aut;

      if (!aut)
        break;

      if (!aut->acc().is_buchi())
      {
        std::cerr << "cola requires Buchi condition on input.\n";
        return 1;
      }

      if (aut_type)
      {
        bool type = false;
        if (spot::is_deterministic(aut))
        {
          type = true;
          std::cout << "deterministic" << std::endl;
        }
        // if (is_cut_deterministic(aut))
        // {
        //   type = true;
        //   std::cout << "cut-deterministic" << std::endl;
        // }
        if (spot::is_semi_deterministic(aut))
        {
          type = true;
          std::cout << "limit-deterministic" << std::endl;
        }
        if (cola::is_elevator_automaton(aut))
        {
          std::cout << "elevator" << std::endl;
        }
        if (cola::is_weak_automaton(aut))
        {
          std::cout << "inherently weak" << std::endl;
        }
        if (spot::is_unambiguous(aut))
        {
          std::cout << "unambiguous" << std::endl;
        }
        if (!type)
        {
          std::cout << "nondeterministic" << std::endl;
        }
        break;
      }

      // Check if input is TGBA
      if (!aut->acc().is_generalized_buchi())
      {
        aut = spot::degeneralize_tba(aut);
      }

      if (om.get(MORE_ACC_EDGES) > 0)
      {
        const unsigned num = 200;
        // strengther
        spot::scc_info si(aut, spot::scc_info_options::ALL);
        cola::edge_strengther e_strengther(aut, si, 200);
        for (unsigned sc = 0; sc < si.scc_count(); sc++)
        {
          if (si.is_accepting_scc(sc))
          {
            e_strengther.fix_scc(sc);
          }
        }
      }

      else if (!spot::is_deterministic(aut))
      {
        // spot::scc_info si(aut);
        // std::string scc_types = cola::get_scc_types(si);
        // cola::print_scc_types(scc_types, si);
        // //std::cout << "scc types: " << scc_types << "\n";
        // std::cout << "weak: " << cola::is_weak_automaton(si, scc_types) << " " << cola::is_weak_automaton(aut) << std::endl;
        // std::cout << "elevator: " << cola::is_elevator_automaton(si, scc_types) << " " << cola::is_elevator_automaton(aut) << std::endl;
        // std::cout << "ldba: " << cola::is_limit_deterministic_automaton(si, scc_types) << " " << spot::is_semi_deterministic(aut) << std::endl;
        // // exit(1);
        clock_t c_start = clock();
        unsigned aut_type = NONDETERMINISTIC;
        if (cola::is_weak_automaton(aut))
        {
          aut_type |= INHERENTLY_WEAK;
        }
        if (spot::is_semi_deterministic(aut))
        {
          aut_type |= LIMIT_DETERMINISTIC;
        }
        if (cola::is_elevator_automaton(aut))
        {
          aut_type |= ELEVATOR;
        }
        // bool is_semi_det = is_semi_deterministic(aut);
        {
          // preprocessing for the input.
          if (preprocess)
          {
            // only a very low level of preprocessing is allowed
            spot::postprocessor preprocessor;
            if (preprocess == Low)
               preprocessor.set_level(spot::postprocessor::Low);
            else if (preprocess == Medium)
               preprocessor.set_level(spot::postprocessor::Medium);
            else if (preprocess == High)
               preprocessor.set_level(spot::postprocessor::High);
            aut = preprocessor.run(aut);
            if (!cola::is_elevator_automaton(aut) && aut_type == ELEVATOR)
            {
              std::cerr << "Automata after preprocessing that are not elevator..." << std::endl;
              return 1;
            }
          }
        }
        if (om.get(VERBOSE_LEVEL) >= 1)
        {
          if (om.get(VERBOSE_LEVEL) >= 2) cola::output_file(aut, "sim_aut.hoa");
          std::cout << "Output processed automaton (" << aut->num_states() << ", " << aut->num_edges() << ") to sim_aut.hoa\n";
        }
        clock_t c_end = clock();
        if (om.get(VERBOSE_LEVEL) > 0)
        {
          std::cout << "Done for preprocessing the input automaton in " << 1000.0 * (c_end - c_start) / CLOCKS_PER_SEC << " ms..." << std::endl;
        }

        if (determinize != NoDeterminize && decompose && aut->acc().is_buchi())
        {
          cola::decomposer nba_decomposer(aut, om);
          std::vector<spot::twa_graph_ptr> subnbas = nba_decomposer.run();
          std::vector<spot::twa_graph_ptr> dpas;
          for (unsigned i = 0; i < subnbas.size(); i++)
          {
            spot::twa_graph_ptr dpa = to_deterministic(subnbas[i], om, aut_type, determinize);
            dpas.push_back(dpa);
          }
          cola::composer dpa_composer(dpas, om);
          aut = dpa_composer.run();
        }
        else if (determinize != NoDeterminize && aut->acc().is_buchi())
        {
          spot::twa_graph_ptr res = nullptr;
          c_start = clock();
          res = to_deterministic(aut, om, aut_type, determinize);
          c_end = clock();
          if (om.get(VERBOSE_LEVEL) > 0)
          {
            std::cout << "Done for determinizing the input automaton in " << 1000.0 * (c_end - c_start) / CLOCKS_PER_SEC << " ms..." << std::endl;
          }
          aut = res;
        }
        else if (aut->acc().is_all())
        {
          // trivial acceptance condition
          aut = spot::minimize_monitor(aut);
        }
      }
      const char *opts = nullptr;
      aut->merge_edges();
      if (om.get(VERBOSE_LEVEL) > 0)
        std::cout << "Number of (states, transitions, colors) in the result automaton: ("
                  << aut->num_states() << "," << aut->num_edges() << "," << aut->num_sets() << ")" << std::endl;
      // postprocessing, remove dead states
      //aut->purge_unreachable_states();
      if (post_process != None && !decompose)
      {
        clock_t c_start = clock();
        if (aut->acc().is_all())
        {
          aut = spot::minimize_monitor(aut);
        }
        else if (aut->num_states() < num_post)
        {
          spot::postprocessor p;
          if (output_type == Parity)
          {
            if (use_acd)
            {
              p.set_type(spot::postprocessor::Generic);
            }else
            {
              p.set_type(spot::postprocessor::Parity);
            } 
          }else if (output_type == Generic || output_type == Rabin)
          {
            p.set_type(spot::postprocessor::Generic);
          }
          p.set_pref(spot::postprocessor::Deterministic);
          // set postprocess level
          if (post_process == Low)
          {
            p.set_level(spot::postprocessor::Low);
          }
          else if (post_process == Medium)
          {
            p.set_level(spot::postprocessor::Medium);
          }
          else if (post_process == High)
          {
            p.set_level(spot::postprocessor::High);
          }
          aut = p.run(aut);
        }
        if (output_type == Rabin)
        {
          aut = spot::to_generalized_rabin(aut, true);
        }else if (output_type == Parity && use_acd)
        {
          aut = spot::acd_transform(aut);
        }
        clock_t c_end = clock();
        if (om.get(VERBOSE_LEVEL) > 0)
          std::cout << "Done for postprocessing the result automaton in " << 1000.0 * (c_end - c_start) / CLOCKS_PER_SEC << " ms..." << std::endl;
      }
      if (output_filename != "")
      {
        cola::output_file(aut, output_filename.c_str());
      }
      else
      {
        spot::print_hoa(std::cout, aut, opts);
        std::cout << "\n";
      }
    }
  }

  check_cout();

  return 0;
}