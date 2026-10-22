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

## Subsequent polarity experiment

The user's COLA-neg experiment is complete; see `tests/ltl-polarity-summary.md`.
Translate `!phi`, complete its deterministic graph, then complement acceptance
in a separate command. All 224 completed outputs are equivalent to the original
positive-language references. Three negative translations time out at 30 seconds
(Parametrised-Hardness lines 2, 4, 6); ordinary COLA completes all three.
Among the 224 verified pairs, negative translation is smaller on 11, tied on
206, and larger on seven. On the common 222-formula external-tool cohort,
COLA totals 1036 states, COLA-neg 4016, and selecting the smaller polarity 993,
versus LTL3TELA 991. Keep both candidates rather than forcing negation.
This is a reproducible external experiment; translator defaults and the
implemented finite-witness construction are unchanged. HOA intermediates are
in `build-local/polarity-comparison/`. CSV/manifest and reproduction scripts
are committed. PR #2 remains draft.

## Subsequent SLAA/TELA milestone

The first milestone of the revised architecture is implemented. Read
`tests/ltl-slaa-report.md`. The opt-in `--slaa-tool=PATH` invokes the pinned
LTL3TELA executable as an isolated process with `-D0 -b0 -n0 -l0 -t0 -p2`.
The resulting generic TELA must be elevator and source-equivalent. Native
ELA determinisation preserves shifted acceptance and is independently checked.
Failures retain the established residual route; direct monitors keep priority.
No LTL3TELA source is vendored. Simulation and stutter shortcuts are disabled
on this generic boundary; exact-language preorder/union pruning remains.

- Fixed unresolved Fin-SCC acceptance causing a backend assertion on
  SomenziB00 line 23: determine unknown acceptance before SCC classification.
  Added a three-state rejecting-Fin regression; removed an HOA debug print.
- All 454 default/integrated literature outputs pass. Defaults match the
  prior 227 state counts. Optional SLAA improves one (five to four states)
  and ties 226; common-222 total is 1035 versus default 1036.
- Raw boundary: 170 successes, including 35 genuinely nondeterministic TELA
  inputs; 55 non-elevator inputs, one frontend timeout (Liberouter line 45)
  and one frontend SIGSEGV (Somenzi line 11) are recorded separately.
- `make check`: eight historical, 17 fragment, 22 generic acceptance and
  15 frontend admission/fallback fixtures pass. Full smoke and 387 seeded/
  scaling finite-witness outputs pass. Raw artifacts: `build-local/slaa-comparison/`.

This remains a first milestone: no new SLAA dealternation rules, SCC-local
semi-determinisation, rank-pressure profile scoring, acceptance compaction or
online polarity portfolio. The optional frontend's deadline/output/input-state
limits do not bound native construction or language checking. Keep PR #2 draft.

## Subsequent SLAA shape diagnosis and online portfolio

Read `tests/ltl-slaa-shape-diagnosis.md`. All 80 winner ablations and 300
shape/polarity experiments are retained. Six of the ten LTL3TELA wins over
positive SLAA COLA select negation, one selects Spot, and one depends on
composition. None of the extra shape variants improves the best native
result across both baseline polarities. Smaller intermediate counts do not
imply easier determinisation; protect acceptance-aware transition dominance.

The opt-in `--slaa-portfolio` tries both SLAA polarities, completes before
acceptance complement, validates the positive language, and retains the
smaller checked result. It also lets X-advice compete with these candidates
and compares the surviving elevator BA result with formula translation.
This fixes early size commitments on Pelanek 7 (9 -> 5) and Dwyer 50
(12 -> 11). Native SCC pruning makes Parametrised 15 ten states, versus
LTL3TELA eleven. Direct monitors and existing defaults are unchanged.

All 681 outputs on 227 formulas pass. Versus default: 15 smaller, 212 ties,
no larger. Common-222 totals: default 1036, positive SLAA 1035, portfolio 985,
LTL3TELA 991. Pairwise against LTL3TELA: six smaller, 216 ties, none larger.
The 22 frontend checks and all other make-check fixtures pass. Running the
finite-witness suite with the new portfolio enabled passes all 387 measured
outputs and 585 fallback/bypass checks. HOA artifacts are under
`build-local/slaa-shapes/` and `build-local/slaa-portfolio-comparison/`.

## Subsequent TACAS/OWL LDGBA route

The additional route is implemented and measured. Read `tests/ltl-ldgba-report.md`.
The TACAS 2017 paper (Esparza/Kretinsky/Raskin/Sickert) and OWL source were
checked. A standard LDGBA has rejecting weak prefix SCCs and closed deterministic
accepting SCCs, hence is elevator. Keep generalized Buchi acceptance and use
native shifted Emerson-Lei acceptance; do not degeneralise or pass through DPA.
Paper-level semantic annotations and complexity guarantees do not automatically
transfer through unannotated HOA.

- `--ldgba-tool=PATH` invokes OWL 21.0 `ltl2ldgba -t SEJK16|EKS20` with formula/
  acceptance simplification and `--skip-translation-portfolio`. Default tries
  both algorithms and compares final completed states/marks/edges, keeping
  established results on exact ties. Combine with `--slaa-portfolio` as desired.
  Direct recurrence, GF/FG and finite-witness monitors retain priority.
- Every input must be generalized Buchi, certified elevator and source-equivalent.
  Every native result is checked for determinism and input equivalence. Existing
  bounded exact SCC-local preorder/union pruning remains; simulation/stutter
  shortcuts stay disabled at this boundary. Failed optional attempts fall back.
- Acceptance allocation can use maximum observed rank widths after exploration.
  Always-absent ranks have false Fin(discontinued) and may be omitted. This is
  enabled only for the new route. Dwyer 45's two algorithm inputs change from
  capacity failures to checked 276/28-state results. Spot still limits marks to 32.
- The first integrated campaign timed out on Dwyer 55 because profile refinement
  repeatedly invoked OWL. Per-formula caching (including failed attempts) and
  `--ldgba-attempt-limit=8` fix it: controlled reproduction 4.4 seconds, eight
  calls, 18 cache hits. Budget/cache reset for each batch input. Frontend defaults
  are five seconds per call, 8 MiB output, 256 input states; zero budgets skip.
  Native construction, parsing and exact language checking remain unbounded.
- All 908 outputs across default, SLAA portfolio, LDGBA and combined modes pass.
  Common-222 totals: 1036, 985, 998, **984** respectively. Combined versus default:
  15 smaller/212 ties/no larger. Combined versus LTL3TELA: seven smaller/215 ties/
  no larger. The new additional win is Dwyer 46: default 6, SLAA 4, LDGBA 3.
- 1135 raw comparisons cover both generalized and ordinary Buchi frontends plus
  OWL's TACAS DPA route. Preserving generalized acceptance is smaller on 19 SEJK16
  and 29 EKS20 joint successes, never larger. Somenzi 21 gives four versus eight.
  Raw GBA is not uniformly better than OWL DPA; use it alongside direct monitors.
  Genuine raw timeouts/capacity outcomes remain explicit in the CSV.
- 60 targeted controls compare formula/acceptance simplification, OWL portfolio
  and full/observed rank allocation. On these six formulas disabling simplifiers
  gives no size gains. OWL portfolio improves some SEJK16 outcomes but loses the
  EKS20 three-state result on Dwyer 46. Do not pick only by intermediate size.
- `make check`: eight historical, 17 specialized, 47 generic, 22 SLAA and 24 LDGBA
  checks pass. Complete smoke, 387 combined-mode finite-witness outputs and 585
  budget/bypass checks pass without timeout or capacity failure. CSV timing is
  single-repeat with concurrent campaigns, not a runtime ranking.

Artifacts: `build-local/ldgba-comparison/`, `build-local/ldgba-integrated/`,
`build-local/ldgba-optimizations/`. Source/binary hashes are in CSV companion
JSON manifests. Optional tools are runtime dependencies; no source is vendored.
Keep PR #2 draft. Existing SLAA/finite-witness work is preserved; custom SLAA
rewrites, annotated semantic jump/ranking optimization and SCC-local
elevatorization remain future work.

## Colour-choice milestone from idea.md

Work continues on dedicated branch `colour-elevator`, based on the completed
`0ef66dc` branch. Read `tests/colour-choice-report.md` and
`research/colour-elevator.tex`. Spot remains the 32-set installation.

Priority A is implemented: BDD target-deterministic SCC detection, bounded
generalised-Rabin clause rewriting, SCC selectors and state-preserving mark
choice elimination. The theorem has a finite-requirement round-robin proof.
Global source/rewrite equivalence is mandatory; verification capacity retains
the original graph. Reuse the existing native backend without reproving it.
`--colour-choice` enables this on SLAA candidates. All limits fall back safely.

The new suite passes 3708 checks, including an exhaustive 3600-case family
with a separate recurrent-edge oracle, 100 seeded multi-state cases and eight
edge/budget/capacity fixtures. All six make-check suites pass; SLAA frontend
checks now number 25. The retained-TELA scan has 530 rows: 227 positive
literature, 300 shape/polarity and three illustrative cases. Two historical
frontends are unavailable; all other 528 preprocessing outputs verify.
Twelve literature intermediates become elevator and eleven complete native
determinisation; Parametrised 36 still hits native capacity. Hardness 8 exceeds
capacity during equivalence, safely retaining its input. The 300 shape variants
retain genuine target nondeterminism and have no eligibility gain.

All 454 integrated baseline/enabled outputs pass; both totals remain 1336 on
227 and 984 on common 222. Do not present raw eligibility as a final size gain:
the changed examples already have direct one-state monitors. Spot already merges
Fin-less equal-guard edges; mixed Fin/Inf generalisation is not a novelty claim.
The supplement includes a proved pure-persistence configuration graph result
and explicit caveats about acceptance lifting/quotienting, and a parametric
global-monitor argument with pruning restrictions. Custom SLAA rewriting and
general shared-monitor backend code are not implemented at this checkpoint.

### Subsequent priorities B/C/D

Read `tests/colour-elevator-report.md`. Bounded positive Fin-only SCC
weakification is now implemented in `src/cobuchi_weak.*`. `--colour-elevator`
enables both passes. A standard last-bad-event guess makes rejecting prefix
SCCs and accepting weak copies; exits retain downstream semantics. Limits:
512 total states (CLI `--cobuchi-state-limit`), 64 clauses, 16384 edges and
Spot's colour capacity. Source/rewrite equivalence is mandatory.

Corrected raw measurements have 531 rows: literature native successes
170 -> 185, with three additional co-Buchi repairs (Parametrised 43/44/45,
adding 4/12/32 states; checked native results 6/23/90). Forty remain hard,
all repaired inputs complete natively, two old frontends unavailable.
The shape grid remains 151 successes/149 hard. A diagnostic counter had
shadowed the weakification flag; the corrected driver and targeted fixture
cover actual execution. All 681 baseline/A/A+B integrated outputs pass;
all final state counts tie, common-222 total 984.

SCC-local acceptance packing is enabled by the new colour modes only. It
substitutes absent/common colours, densely renames the remaining local sets
and preserves each rank's discontinuation mark, after graph exploration.
This is also present in Kofola DAC (inspected devel 14b657bc), not new theory.
The raw ablation now compares identical rewritten graphs with global/local
blocks: Parametrised 36 changes from capacity failure to one checked state
and 15 colours with the original Spot32 build. Final generic fixtures now
number 94, with local packing off/on. The original modes retain global blocks.

The SLAA certificate driver proves/checks pure retention plus strict discharge
and enumerates canonical configuration graphs with 4096-state/65536-work
budgets. All 543 probes finish: 103/227 literature and 42/300 shape graphs
certify pure persistence, with no non-singleton SCC in certified enumerations.
Sixteen controls show two nested-W formulas lose the syntactic certificate
under native expansion, even without merging/simplification; they still have
singleton configuration SCCs. Conversely merging makes GF a pure one-state
while disabling it restores recurrent spawn. Do not disable merging wholesale.

The late-product campaign has 28 independently checked outputs, including a
minimised-monitor control. At depth six, full-history D=64 gives early backend
input 192 versus late 3, final 18 both; minimising D to seven reduces early
input to 21. Timings/RSS are diagnostic, not a speedup ranking.

`src/late_monitor.*` implements a separate checked acceptance-parametric
reference API. It substitutes bounded global-monitor Inf valuations, checks
each elevator profile, uses the existing fixed-acceptance backend, then composes
the deterministic profile results with each global monitor once. Independent
early-product verification is mandatory. It has a PRODUCT of profile state
counts, not the desired single-rank-graph bound. Default eight profiles;
unsupported/over-budget profiles return no candidate. It is not enabled in
the LTL frontend. Twenty-six tests cover all 16 two-variable mixed acceptance
functions, rejecting-run versus language-complement semantics, multiple
monitors, profile eligibility and budgets.

All ten check suites pass: 3709 colour-choice, 214 co-Buchi, seven SLAA graph/
syntax, three late-product, 26 parametric and the historical suites (27 SLAA,
24 LDGBA). Full smoke plus 387 complete-mode finite-witness outputs and 585
budget/bypass checks pass. Proofs and measured scope are in
`research/colour-elevator.tex` and `research/colour-experiments.tex`.
Remaining research: custom recurrent-spawn elimination, one acceptance-uniform
rank graph/pruning, and an actual exported shared acceptance DAG. Existing
preorder pruning is preserved, not reproved or made more aggressive.
Keep the user’s untracked `idea.md` and nested `COLA/` checkout untouched.

## Sources

- https://github.com/liyong31/ltl2dela-scc-decomp/blob/main/factored.tex
- https://github.com/liyong31/COLA/pull/1
- https://spot.lre.epita.fr/ipynb/ltlf2dfa.html
- https://spot.lre.epita.fr/doxygen/ltlf2dfa_8hh_source.html

The same formulas interpreted on finite traces require strong next. Spot's
MTBDD terminal carries a continuation and a separate finite-acceptance bit;
using only the continuation's infinite-word truth would be incorrect.
