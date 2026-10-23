// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#include "slaa_frontend.hpp"
#include <spot/parseaut/public.hh>
#include <spot/tl/print.hh>

#include <cerrno>
#include <chrono>
#include <cstdlib>
#include <fcntl.h>
#include <signal.h>
#include <stdexcept>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>
#include <vector>

namespace cola
{
  static spot::twa_graph_ptr external_frontend(spot::formula f, spot::bdd_dict_ptr dict,
                                             const std::string& tool,
                                             unsigned timeout_ms, unsigned state_limit,
                                             std::vector<std::string> arguments)
  {
    if (tool.empty() || !timeout_ms || !state_limit) return nullptr;
    // mkstemp is private even when several translators run concurrently.
    const char* temp = std::getenv("TMPDIR");
    std::string pattern = std::string(temp ? temp : "/tmp") + "/cola-front-XXXXXX";
    std::vector<char> name(pattern.begin(), pattern.end());
    name.push_back('\0');
    int fd = mkstemp(name.data());
    if (fd < 0) return nullptr;
    struct cleanup
    {
      int fd;
      const char* name;
      ~cleanup() { close(fd); unlink(name); }
    } guard{fd, name.data()};
    arguments.insert(arguments.begin(), tool);
    arguments.emplace_back("-f");
    arguments.push_back(spot::str_psl(f));
    std::vector<char*> argv;
    for (auto& argument : arguments) argv.push_back(argument.data());
    argv.push_back(nullptr);
    // Prepare all strings before fork. No shell or command interpolation.
    pid_t pid = fork();
    if (pid < 0) return nullptr;
    if (pid == 0)
      {
        setpgid(0, 0);
        rlimit bytes{8 * 1024 * 1024, 8 * 1024 * 1024};
        rlimit core{0, 0};
        if (setrlimit(RLIMIT_FSIZE, &bytes) || setrlimit(RLIMIT_CORE, &core)
            || dup2(fd, STDOUT_FILENO) < 0) _exit(126);
        int nullfd = open("/dev/null", O_RDWR);
        if (nullfd < 0 || dup2(nullfd, STDIN_FILENO) < 0
            || dup2(nullfd, STDERR_FILENO) < 0) _exit(126);
        close(nullfd);
        close(fd);
        execvp(tool.c_str(), argv.data());
        _exit(127);
      }
    setpgid(pid, pid);
    auto deadline = std::chrono::steady_clock::now()
      + std::chrono::milliseconds(timeout_ms);
    int status = 0;
    for (;;)
      {
        pid_t done = waitpid(pid, &status, WNOHANG);
        if (done == pid) break;
        if (done < 0 && errno != EINTR) return nullptr;
        if (std::chrono::steady_clock::now() >= deadline)
          {
            kill(-pid, SIGKILL);
            kill(pid, SIGKILL);
            while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
            return nullptr;
          }
        usleep(10000);
      }
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) return nullptr;
    // Inspect parser errors directly, so malformed child output never leaks
    // diagnostics into the caller's HOA stream.
    auto parsed = spot::parse_aut(name.data(), dict);
    if (!parsed || !parsed->errors.empty() || !parsed->aut
        || !parsed->aut->is_existential()
        || parsed->aut->num_states() > state_limit) return nullptr;
    return parsed->aut;
  }

  spot::twa_graph_ptr slaa_frontend(spot::formula f, spot::bdd_dict_ptr dict,
                                  const std::string& tool,
                                  unsigned timeout_ms, unsigned state_limit)
  {
    return external_frontend(f, dict, tool, timeout_ms, state_limit,
                             {"-D0", "-b0", "-n0", "-l0", "-t0", "-p2"});
  }

  spot::twa_graph_ptr owl_ldgba_frontend(spot::formula f, spot::bdd_dict_ptr dict,
                                       const std::string& tool,
                                       const std::string& construction,
                                       unsigned timeout_ms, unsigned state_limit)
  {
    if (construction != "SEJK16" && construction != "EKS20") return nullptr;
    return external_frontend(f, dict, tool, timeout_ms, state_limit,
                             {"ltl2ldgba", "-t", construction, "--skip-translation-portfolio", "--state-labels"});
  }
}
