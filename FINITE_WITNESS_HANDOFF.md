# Finite-witness reset construction: continuation checkpoint

Updated 21 October 2026. Branch: `finite-witness-reset`.
Base: `ltl2dela` at `07960fadd371985ceaf676be8157e78bed380db0`.

## Goal and current status

Continue the existing implementation; do not start again from scratch.
The user requested an optional direct LTL-to-DELA path based on the
finite-witness construction in `liyong31/ltl2dela-scc-decomp/factored.tex`
(introduced in commit `3c2b42f`). Finish validation and benchmarking locally.
The patch is implemented, but the complete regression and performance
campaign is **unfinished**. Do not describe this checkpoint as fully tested.

The construction recognises `GF mu` for syntactic co-safety mu by exploring
the finite-word DFA for `F mu` and resetting to its initial state on each
finite acceptance event. That event emits colour 0. Acceptance is `Inf(0)`.
For `FG nu` with syntactic safety nu, use the monitor for `GF !nu` and `Fin(0)`.

## Implemented

- `src/ltl2dela.cpp`: incremental Spot `ltlf_translator::ltlf_to_mtbdd()`
  exploration, finite `may_stop` acceptance, marked reset transitions,
  persistence dual, and whole-attempt fallback on exploration limits.
- Convert infinite-word X to `strong_X` recursively AFTER infinite-word NNF.
  Do not apply ordinary infinite-word simplification to this converted formula.
- Existing recurrence rewrites and flat-until monitors take priority.
  Propositional GF/FG remains on the established one-state path.
- `src/ltl2dela.hpp` and `src/ltl2dela_main.cpp`: `--finite-witness` (off by
  default), `--finite-witness-state-limit=N` (256), and
  `--finite-witness-work-limit=N` (16384), plus routing/abort statistics.
- The work limit counts MTBDD visits while extracting transitions, not work
  inside one call to Spot's derivative routine. It is not a hard memory limit.
- `tests/finite-witness.py`: fixed equivalence cases, duals, budget fallbacks,
  bypassing fast paths, routing assertions, seeded random kernels, scaling
  families, and CSV measurements checkpointed after each completed case.
- README explains the construction, semantics, budgets and commands.

## Checks actually completed before the interruption

Using Spot 2.14.5 and GCC 13 on Linux:

- Modified C++ compiled and linked.
- All 17 fixed formulas currently listed in `CASES` in the Python script
  passed a separate `spot::are_equivalent(automaton, formula)` check using
  a temporary C++ driver. This checked the enabled path; it was NOT the full
  command-line campaign with baseline, fallback and routing checks.
- `GF(a & X X b)` selected the new path and produced a four-state DBA.
- `FG(!a | X X !b)` selected the dual path and produced a four-state DCA.
- For `GF(a & X((b U c) & (d M (e | F f))))`, observed state counts were
  existing COLA 561, optional reset 13, independent `ltl2tgba -D -G` 13.
  No reliable timing measurements have been retained.
- The existing smoke suite and full Python suite were started, but their
  temporary logs disappeared after a session interruption. Their completion
  has NOT been established; rerun them.

## Local build

First inspect the user's installed Spot and build tools. Prefer an existing
working installation. The implementation uses APIs introduced in Spot 2.14;
Spot 2.14.5 is the version already used successfully. Newer Spot releases may
require a newer C++ standard; inspect their headers and the build configuration.
Do not reuse cloud object files or binaries on the desktop.

With a suitable Spot installation, from the repository root:

```sh
SPOT_PREFIX=/actual/path/to/spot
export PATH="$SPOT_PREFIX/bin:$PATH"
autoreconf -i
./configure --with-spot="$SPOT_PREFIX"
make -j4
./ltl2dela --version
```

Use the desktop's available core count if appropriate. On Windows use a
suitable Linux/WSL environment for this Autotools project. Check the local OS
before choosing dependency installation commands.

If building Spot 2.14.5 from source, shared-only (`--disable-static`), without
Python (`--disable-python`), suffices. Avoid repeatedly rebuilding it in a
transient temporary directory. One cloud rebuild using `--disable-optimizations`
encountered a gnulib `wctype_t` configure-detection problem; a retry supplied
`CFLAGS='-O2 -D_GNU_SOURCE' CXXFLAGS='-O2 -D_GNU_SOURCE'
gl_cv_type_wctype_t=yes`. That retry was not yet validated at this checkpoint;
do not blindly impose those platform-specific settings on the user's machine.

## Remaining work, in order

1. Build locally; fix any compile/runtime errors in the patch.
2. Run existing regressions:

   ```sh
   make check
   sh tests/ltl2dela-smoke.sh
   ```

3. Run the new regressions and comparison, with Spot's tools on PATH:

   ```sh
   python3 tests/finite-witness.py --repeats 5 --stress 10 \
     --csv tests/finite-witness-results.csv
   python3 tests/finite-witness.py --repeats 1 --random-cases 50 \
     --csv tests/finite-witness-random-results.csv
   ```

   These compare the default COLA path, `--finite-witness`, and independent
   `ltl2tgba --deterministic --generic`, using `autfilt --equivalent-to`.
   The random run adds 50 kernels and their 50 duals (seed 20261020).
   Timings are fresh-process medians including startup and HOA output.
   Required fixed-case timeouts are failures. Scaling timeouts are recorded.

4. Examine DFA growth on `GF(a & X^k b)` and correlated-until width families.
   Compare default limits with an increased state budget using
   `--state-limit=4096`; inspect `--stats` to distinguish completed monitors
   from budget fallback. Do not claim an output came from the reset path if
   that attempt was abandoned. The script's work limit remains the default.
5. Report state/edge counts and median times, gains and regressions, the
   consequences of budget exhaustion, and when existing COLA or direct Spot
   should be preferred. Small startup-dominated timing differences should not
   be overinterpreted. Keep the feature optional unless broader evidence
   supports changing its default.
6. Commit test results and fixes to this branch and update its draft PR (or
   create a PR targeting `ltl2dela` if one is absent). Do not merge automatically.

## Sources

- https://github.com/liyong31/ltl2dela-scc-decomp/blob/main/factored.tex
- https://github.com/liyong31/COLA/pull/1
- https://spot.lre.epita.fr/ipynb/ltlf2dfa.html
- https://spot.lre.epita.fr/doxygen/ltlf2dfa_8hh_source.html

The same formulas interpreted on finite traces require strong next. Spot's
MTBDD terminal carries a continuation and a separate finite-acceptance bit;
using only the continuation's infinite-word truth would be incorrect.
