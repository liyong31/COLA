// Copyright (c) 2017-2020  The cola Authors
//
// This file is a part of cola, a tool for semi-determinization
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
#include <unistd.h>
#include "seminator.hpp"
#include "cutdet.hpp"
#include <spot/twaalgos/simulation.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/misc/version.hh>
#include <fstream>
#include<ctime>
#define FWZ_DEBUG 0

void print_usage(std::ostream& os) {
  os << "Usage: cola [OPTION...] [FILENAME...]\n";
}

void print_help() {
  print_usage(std::cout);
  std::cout <<
    R"(The tool transforms TLDBA into equivalent deterministic Rabin/Parity automata.

By default, it reads a limit deterministic generalized Büchi automaton (LDGBA) from standard input
and converts it into deterministic Rabin/Parity automata.

Input options:
    -f FILENAME reads the input from FILENAME instead of stdin
    --determinize=[spot|parity|rabin]
                    use Spot or our algorithm to obtain deterministic Parity or Rabin automata

Output options:
    -o FILENAME writes the output from FILENAME instead of stdout

Optimizations:
    --simulation          use simulaition before parity determinization

Pre- and Post-processing:
    --preprocess[=0|1]       simplify the input automaton
    --postprocess[=0|1]      simplify the output of the semi-determinization
                             algorithm (default)
    --postprocess-comp[=0|1] simplify the output of the complementation
                             (default)
    -s0, --no-reductions     same as --postprocess=0 --preprocess=0
                             --postprocess-comp=0
    --merge-transitions      merge transitions in the output automaton

Miscellaneous options:
  -h, --help    print this help
  --version     print program version
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

void output_file(spot::twa_graph_ptr aut, const char* file)
{
  const char* opts = nullptr;
  std::ofstream outfile;
  std::string file_name(file);
  outfile.open(file_name);
          
  spot::print_hoa(outfile, aut, opts);
  outfile.close();
}

int main(int argc, char* argv[])
{
    // clock_t startTime, endTime;
    // startTime = clock();

    // Declaration for input options. The rest is in cola.hpp
    // as they need to be included in other files.
    bool cd_check = false;
    bool high = false;
    std::vector<std::string> path_to_files;

    spot::option_map om;
    bool cut_det = false;
    jobs_type jobs = 0;
    enum complement_t { NoComplement = 0, NCSBBest, NCSBSpot, NCSBPLDI, NCSBPLDIB, NCSBPLDIF, NCSBPLDIBF, NCB, NSBC };
    complement_t complement = NoComplement;

    // determinization
    enum determinize_t { NoDeterminize = 0, Rabin, Parity, Spot };
    determinize_t determinize = NoDeterminize;

    output_type desired_output = TGBA;

    bool use_simulation = false;
    bool merge_transitions = false;
    bool debug = false;

    std::string output_filename = "";

    auto match_opt =
      [&](const std::string& arg, const std::string& opt)
      {
        if (arg.compare(0, opt.size(), opt) == 0)
          {
            if (const char* tmp = om.parse_options(arg.c_str() + 2))
              {
                std::cerr << "cola: failed to process option --"
                          << tmp << '\n';
                exit(2);
              }
            return true;
          }
        return false;
      };

    for (int i = 1; i < argc; i++)
      {
        std::string arg = argv[i];

        // Transformation types
        // if (arg == "--via-sba")
        //   jobs |= ViaSBA;
        // else if (arg == "--via-tba")
        //   jobs |= ViaTBA;
        // else if (arg == "--via-tgba")
        //   jobs |= ViaTGBA;
        // //
        // else if (arg == "--is-cd")
        //   cd_check = true;
        // // Cut edges
        // else if (arg == "--cut-on-SCC-entry") {
        //   om.set("cut-on-SCC-entry", true);
        //   om.set("cut-always", false);
        // }
        // else if (arg == "--cut-always")
        //   om.set("cut-always", true);
        // else if (arg == "--cut-highest-mark")
        //   {
        //     om.set("cut-always", false);
        //     om.set("cut-on-SCC-entry", false);
        //   }
        // // Optimizations
        // else 
        if (
                 match_opt(arg, "--powerset-for-weak")
                 || match_opt(arg, "--jump-to-bottommost")
                 || match_opt(arg, "--bscc-avoid")
                 || match_opt(arg, "--reuse-deterministic")
                 || match_opt(arg, "--skip-levels")
                 || match_opt(arg, "--scc-aware")
                 || match_opt(arg, "--powerset-on-cut")
                 || match_opt(arg, "--preprocess")
                 || match_opt(arg, "--postprocess")
                 || match_opt(arg, "--postprocess-comp"))
          {
          }
        else if (arg == "--scc0")
          om.set("scc-aware", false);
        else if (arg == "--no-scc-aware")
          om.set("scc-aware", false);
        else if (arg == "--pure")
          {
            om.set("bscc-avoid", false);
            om.set("powerset-for-weak", false);
            om.set("reuse-deterministic", false);
            om.set("jump-to-bottommost", false);
            om.set("bscc-avoid", false);
            om.set("skip-levels", false);
            om.set("powerset-on-cut", false);
            om.set("postprocess", false);
            om.set("postprocess-comp", false);
            om.set("preprocess", false);
            om.set("cut-always", false);
            om.set("cut-on-SCC-entry", false);
          }
        else if (arg == "-s0" || arg == "--no-reductions")
          {
            om.set("postprocess", false);
            om.set("preprocess", false);
          }
        else if (arg == "--simplify-input")
          om.set("preprocess", true);
        else if (arg == "--simulation") 
          use_simulation = true;
        // Prefered output
        else if (arg == "--cd")
          cut_det = true;
        else if (arg == "--sd")
          cut_det = false;
        else if (arg == "--d")
          debug = true;
        else if (arg == "--merge-transitions")
          merge_transitions = true;
        // else if (arg == "--complement" || arg == "--complement=best")
        //   complement = NCSBBest;
        // else if (arg == "--complement=spot")
        //   complement = NCSBSpot;
        // else if (arg == "--complement=pldi")
        //   complement = NCSBPLDI;
        // else if(arg == "--complement=pldib")
        //   complement = NCSBPLDIB;
        // else if(arg == "--complement=pldif")
        //   complement = NCSBPLDIF;
        // else if(arg == "--complement=pldibf")
        //   complement = NCSBPLDIBF;
        // else if (arg == "--complement=ncb")
        //   complement = NCB;
        // else if (arg == "--complement=nsbc")
        //   complement = NSBC;

        // determinization
        else if (arg == "--determinize=rabin")
          determinize = Rabin;
        else if (arg == "--determinize=parity")
          determinize = Parity;
        else if (arg == "--determinize=spot")
          determinize = Spot;
        else if (arg == "--ba")
          desired_output = BA;
        else if (arg == "--tba")
          desired_output = TBA;
        else if (arg == "--tgba")
          desired_output = TGBA;

        else if (arg == "--highlight")
          high = true;

        else if (arg == "-f")
          {
            if (argc < i + 1)
              {
                std::cerr << "cola: Option -f requires an argument.\n";
                return 1;
              }
            else
              {
                path_to_files.emplace_back(argv[i+1]);
                i++;
              }
          }
        else if (arg == "-o") 
        {
          if (argc < i +1)
          {
            std::cerr << "cola: Option -o requires an argument.\n";
            return 1;
          }else 
          {
            std::string str(argv[i+1]);
            output_filename = str;
            i ++;
          }
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
              " (using Spot " << spot::version() << ")\n\n"
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

    if (high && complement)
      {
        std::cerr
          << "cola --highlight and --complement are incompatible\n";
        return 1;
      }

    if (jobs == 0)
      jobs = AllJobs;

    om.set("output", complement ? TBA : desired_output);

    auto dict = spot::make_bdd_dict();

    for (std::string& path_to_file: path_to_files)
      {
        spot::automaton_stream_parser parser(path_to_file);

        for (;;)
          {
            spot::parsed_aut_ptr parsed_aut = parser.parse(dict);

            if (parsed_aut->format_errors(std::cerr))
              return 1;

            // input automata
            spot::twa_graph_ptr aut = parsed_aut->aut;
            spot::twa_graph_ptr myaut = parsed_aut->aut;

            if (!aut)
              break;

            // Check if input is TGBA
            if (!aut->acc().is_generalized_buchi())
              {
                if (parsed_aut->filename != "-")
                  std::cerr << parsed_aut->filename << ':';
                std::cerr << parsed_aut->loc
                          << ": cola requires a TGBA on input.\n";
                return 1;
              }

            if (cd_check)
              {
                if (!is_cut_deterministic(aut))
                  continue;
              }
            else
              {
                aut = semi_determinize(aut, cut_det, jobs, &om);
                if (auto old_n = parsed_aut->aut->get_named_prop<std::string>
                    ("automaton-name"))
                  {
                    auto name =
                      new std::string(((aut->num_sets() == 1)
                                       ? "sDBA for " : "sDGBA for ") + *old_n);
                    if (cut_det)
                      (*name)[0] = 'c';
                    aut->set_named_prop("automaton-name", name);
                  }

                if (complement)
                  {
                    spot::twa_graph_ptr res = nullptr;
                    spot::postprocessor postprocessor;
                    // We don't deal with TBA: (1) complement_semidet() returns a
                    // TBA, and (2) in Spot 2.8 spot::postprocessor only knows
                    // about state-based BA and Transition-based GBA.  So TBA/TGBA
                    // are simply simplified as TGBA.
                    postprocessor.set_type(desired_output == BA
                                           ? spot::postprocessor::BA
                                           : spot::postprocessor::TGBA);
                    if (!om.get("postprocess-comp", 1))
                      {
                        // Disable simplifications except acceptance change.
                        postprocessor.set_level(spot::postprocessor::Low);
                        postprocessor.set_pref(spot::postprocessor::Any);
                      }

                    if (complement == NCSBSpot || complement == NCSBBest)
                      {
                        res = spot::complement_semidet(aut);
                        res = postprocessor.run(res);
                        // std::cout << "spot states: " << comp->num_states() << ' ';
                        // std::cout << "    edges: " << comp->num_edges() << '\n';
                      }
                    if(complement == NCSBPLDIB || complement == NCSBBest) 
                    {
                        spot::twa_graph_ptr comp1 =
                          from_spot::complement_semidet_opt(aut);
                        comp1 = postprocessor.run(comp1);
                        if (!res || res->num_states() > comp1->num_states())
                          res = comp1;
                        // std::cout << "pldib states: " << comp->num_states() << ' ';
                        // std::cout << "    edges: " << comp->num_edges() << '\n';
                    }
                    if(complement == NCSBPLDIF || complement == NCSBBest) 
                    {
                        spot::twa_graph_ptr comp3 =
                          from_spot::complement_semidet_onthefly(aut);
                        comp3 = postprocessor.run(comp3);
                        if (!res || res->num_states() > comp3->num_states())
                          res = comp3;
                        // std::cout << "pldif states: " << comp->num_states() << ' ';
                        // std::cout << "    edges: " << comp->num_edges() << '\n';
                    }
                    if(complement == NCSBPLDIBF || complement == NCSBBest) 
                    {
                        spot::twa_graph_ptr comp4 =
                          from_spot::complement_semidet_opt_onthefly(aut);
                        comp4 = postprocessor.run(comp4);
                        if (!res || res->num_states() > comp4->num_states())
                          res = comp4;
                        // std::cout << "pldibf states: " << comp->num_states() << ' ';
                        // std::cout << "    edges: " << comp->num_edges() << '\n';
                    }
                    if (complement == NCSBPLDI || complement == NCSBBest)
                      {
                        spot::twa_graph_ptr comp2 =
                          from_spot::complement_semidet(aut);
                        comp2 = postprocessor.run(comp2);
                        if (!res || res->num_states() > comp2->num_states())
                          res = comp2;
                        // std::cout << "pldi states: " << comp->num_states() << ' ';
                        // std::cout << "    edges: " << comp->num_edges() << '\n';
                      }
                    if (complement == NCB)
                    {
                      // spot::print_hoa(std::cout, aut) << '\n';
                      // myaut is directly input automata
                      // aut is semi_determinize(myaut)
                      res = from_spot::complement_unambiguous(myaut); //, true);
                      res = postprocessor.run(res);
                      // spot::print_hoa(std::cout, comp->num_states()) << '\n';
                      // std::cout << "ncb states: " << comp->num_states() << ' ';
                      // std::cout << "    edges: " << comp->num_edges() << '\n';
                    }
                    if (complement == NSBC)
                    {
                      // #if FWZ_DEBUG
                      // spot::print_hoa(std::cout, aut) << '\n';
                      // #endif
                      res = from_spot::new_complement_semidet(aut); //, true);
                      // comp = postprocessor.run(comp);

                      // comp = from_spot::determinize_tldba(aut, true);
                      // spot::print_hoa(std::cout, comp->num_states()) << '\n';
                      // std::cout << "nsbc states: " << comp->num_states() << ' ';
                      // std::cout << "    edges: " << comp->num_edges() << '\n';
                    }
                    aut = res;
                  }

                if (determinize && !is_deterministic(aut))
                {
                  spot::twa_graph_ptr res = nullptr;
                  spot::postprocessor postprocessor;

                  // if (!om.get("postprocess-comp", 1))
                  //   {
                  //     // Disable simplifications except acceptance change.
                  //     postprocessor.set_level(spot::postprocessor::Low);
                  //     postprocessor.set_pref(spot::postprocessor::Any);
                  //   }

                  if (determinize == Rabin)
                  {
                    if (debug)
                    {
                      spot::print_hoa(std::cout, aut) << '\n';
                    }
                    
                    res = from_spot::determinize_rabin(aut, debug);
                    // comp->merge_edges();
                    // comp = postprocessor.run(comp);
                    // std::cout << "spot states: " << comp->num_states() << ' ';
                    // std::cout << "    edges: " << comp->num_edges() << '\n';
                  }
                  
                  if (determinize == Parity)
                  {
                    if(use_simulation) 
                    {
                      auto aut2 = simulation(aut);
                      aut = aut2;
                    }
                    if(debug)
                    {
                      output_file(aut, "in.hoa");
                    }
                    res = from_spot::determinize_tldba(aut, debug);
                  }else  if(determinize == Spot)
                  {
                    // pretty_print, use_scc, use_simulation, use_stutter, aborter
                    res = spot::tgba_determinize(aut, false, false, use_simulation, false, nullptr);
                  }
                    aut = res;
                }
              }
            const char* opts = nullptr;
            if (high)
              {
                highlight_components(aut);
                opts = "1.1";
              }

            // std::ofstream outfile;
            // std::string comfile = "com.hoa";
            // if (complement == NCSBSpot)
            //   outfile.open("spot/" + comfile);
            // if (complement == NCSBPLDI)
            //   outfile.open("pldi/" + comfile);
            // if (complement == NCSBPLDIB)
            //   outfile.open("pldib/" + comfile);
            // if (complement == NCSBPLDIF)
            //   outfile.open("pldif/" + comfile);
            // if (complement == NCSBPLDIBF)
            //   outfile.open("pldibf/" + comfile);
            
            // if (complement == NCB)
            //   outfile.open("ncb/" + comfile);
            // if (complement == NSBC)
            //   outfile.open("nsbc/" + comfile);
          
            // spot::print_hoa(outfile, aut, opts);
            // outfile.close();
            if(merge_transitions)
            {
              //std::cout << "reach here, merge transitions" << std::endl;
              aut->merge_edges();
            }
            if(output_filename != "")
            {
              std::ofstream outfile;
              outfile.open(output_filename);
              spot::print_hoa(outfile, aut, opts);
              outfile.close();
            }else 
            {
              spot::print_hoa(std::cout, aut, opts);
            }
            
          }
      }

    check_cout();

    // endTime = clock();
    // std::cout << "Run time: " <<(double)(endTime - startTime) / CLOCKS_PER_SEC << "s\n";

    return 0;
}


