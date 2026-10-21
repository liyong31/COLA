# Finite-witness reset construction: continuation checkpoint

Updated 21 October 2026. Branch: `finite-witness-reset`.
Base: `ltl2dela` at `07960fadd371985ceaf676be8157e78bed380db0`.
Draft PR: https://github.com/liyong31/COLA/pull/2 (retain draft; do not merge).

## Goal and current status

Continue the existing implementation; do not start again from scratch.
The user requested an optional direct LTL-to-DELA path based on the
finite-witness construction in `liyong31/ltl2dela-scc-decomp/factored.tex`
(introduced in commit `3c2b42f`). Finish validation and benchmarking locally.
The patch and requested local regression/benchmark campaigns are complete.
See `tests/finite-witness-benchmarks.md` and the three committed result CSVs
for commands, measured results, routing evidence and resource limitations.
The feature remains optional and off by default.

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

## Historical checks before the interruption

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
  was not established at that checkpoint; the completed local runs below
  supersede this historical status.

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

## Completed local continuation (21 October 2026)

- Built natively on this Apple M3 MacBook Air with Apple Clang 17,
  C++17/O2 and the existing Spot 2.14.1 installation in `/usr/local`.
  Replaced one GNU-only `bits/stdc++.h` include with standard headers.
  No change to the finite-witness algorithm was required.
- Built in `build-local/` to avoid the case-insensitive `cola`/`COLA/`
  executable/directory collision. The nested checkout is untouched.
  The report gives reproducible configure and dynamic-library settings.
- `make check` and the complete smoke suite passed.
- Default budget, five repeats, stress 10: all required regressions passed;
  79 equivalent deterministic outputs, seven installed acceptance-capacity
  failures and one 30-second baseline scaling timeout.
- Seeded run, one repeat: 17 fixed cases plus 50 kernels and their 50 duals;
  all 351 measured outputs passed. Each formula also passed five independent
  fallback/fast-path-bypass checks (585 additional outputs).
- Larger budget, five repeats, stress 10: state budget 4096, work budget
  unchanged at 16384; the 512-state and 1024-state X-window monitors completed
  and passed independent equivalence. There are 81 successful outputs, five
  baseline capacity failures and one baseline timeout. See the CSV for all rows.
- Budget abort assertions now allow multiple retries by profile exploration;
  they require positive aborts and zero completed monitors. The CLI preserves
  routing statistics when fallback translation raises an exception.
- Scaling capacity errors are recorded explicitly. Unexpected failures and
  all required-case failures remain fatal. No resource-limited output is
  described as a completed reset monitor.

The default reset path completes X-window depths through eight; at nine and
ten it falls back, after which the existing translator hits this installed
Spot build's 32-acceptance-set limit. Increasing the reset state budget to
4096 completes both cases. Direct Spot completes all reference cases.
At correlated-until width five the baseline times out, while reset and Spot
both complete and pass equivalence. DFA state growth remains exponential;
budgets still do not bound time/memory inside a derivative call.

Continue from these results if expanding coverage. There is no outstanding
failure in the required local regressions. Broader LTL/version coverage would
be needed before considering a change to the default. Keep PR #2 in draft.

## Broader OWL literature comparison

The subsequent requested six-configuration size experiment is recorded in
`tests/ltl-size-comparison.md`, with the complete input corpus, CSV, summary,
versions and reproducible drivers. It covers 227 distinct formula strings
(237 source entries). On 222 common successful formulas, LTL3TELA has the
smallest-state output most often, followed by Spot; LTL3TELA also has four
timeouts and one repeatable crash in this local configuration. OWL and DELAG
complete all inputs. Reset mode improves no paired state counts over default
COLA on this collection and worsens one (three to four states); only seven
formula runs actually complete reset monitors. No construction changes were
made for this experiment. Consult the report for the matched-cohort caveat
and explicit alternate-reference checks when Spot times out.

## Subsequent GF/FG/DBA routing continuation

The user's requested timeout/size diagnosis and specialized routing are
implemented. Read `tests/ltl-routing-diagnosis.md` first for the current state.
The finite-witness construction is preserved and remains optional.

- Boolean GF/FG is recognized before simplification; GF co-safety and FG
  safety use specialized endpoints before heuristic profiles.
- Checked weak/transition-Buchi candidates use 64 input states, 512 constructed
  states and 4096 cycles per SCC by default. Generic alternatives can be
  smaller even for DBA languages, so known-fragment candidates compete.
- Safety constraints stay attached to other conjuncts. Generic Low/High
  candidates are compared on complete size. Bogus splits on false are fixed;
  acceptance-capacity failure abandons the whole attempt, not language branches.
- All 454 new literature outputs passed; both timeouts are gone. Default
  COLA improves 15 prior successes and ties 210, with no state regressions.
  The matched 222-formula state total is 1036, versus old COLA 1337, Spot 1058
  and LTL3TELA 991. See `ltl-fragment-results.csv` and `ltl-fragment-summary.md`.
- `make check` (eight raw elevator and 17 new fragment fixtures), complete
  smoke suite, both five-repeat kernel campaigns (87 outputs each), seeded
  regressions (351 outputs plus 585 fallback checks), and 77 LTL3TELA ablations
  passed. New CSVs have the `finite-witness-specialized-` prefix.
- LTL3TELA's eleven wins depend mainly on polarity/composition: disabling
  complement worsens eight, disabling splitting worsens two (one overlap),
  and removing U/G merging retains the wins. More optimization alone is not
  enough: Spot Low can be smaller than High.

Keep PR #2 in draft. No merge is authorized. Raw diagnostics and old/new
reference artifacts remain in `build-local/size-diagnosis/`,
`build-local/owl-comparison/`, and `build-local/fragment-comparison/`.

## Sources

- https://github.com/liyong31/ltl2dela-scc-decomp/blob/main/factored.tex
- https://github.com/liyong31/COLA/pull/1
- https://spot.lre.epita.fr/ipynb/ltlf2dfa.html
- https://spot.lre.epita.fr/doxygen/ltlf2dfa_8hh_source.html

The same formulas interpreted on finite traces require strong next. Spot's
MTBDD terminal carries a continuation and a separate finite-acceptance bit;
using only the continuation's infinite-word truth would be incorrect.
