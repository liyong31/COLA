# Colour-choice elimination: priority A

Implemented on the dedicated `colour-elevator` branch, based on the completed SLAA/LDGBA branch. Spot remains the existing 32-set build. The existing preorder determiniser and finite-witness construction are reused. This milestone targets the first priority in `idea.md`.

## Proved transformation and implementation

A target-deterministic SCC has at most one internal destination for each state and letter, even if several acceptance-mark choices overlap. For each bounded generalized Rabin clause, emit a bad predicate when every available choice is bad, and a good predicate when a bad-free choice emits the required good colour. After the last unavoidable bad step, a round-robin schedule can satisfy all infinitely available good requirements. The formal proof, SCC-selector argument and counterexamples are in [the manuscript supplement](../research/colour-elevator.tex).

BDD guards certify internal target uniqueness. The pass preserves all states and labelled successor possibilities; exits remain available. Fresh internal SCC selectors prevent Fin-only clauses from accepting runs that eventually remain elsewhere. The original acceptance remains guarded for unchanged SCCs. Clause products are budgeted before expansion, and colours, formula words and symbolic regions are bounded. A whole-automaton equivalence gate is mandatory. If that check itself exceeds acceptance capacity, the unchanged graph is retained.

Use `--slaa-tool=PATH --slaa-portfolio --colour-choice`. Limits are `--colour-choice-clause-limit` (64), `--colour-choice-region-limit` (4096) and `--colour-choice-colour-limit` (Spot capacity). The library also has a 4096-word acceptance formula budget. Zero budgets retain unsupported SCCs. Observed rank allocation is enabled only when colour rewriting actually changes an intermediate. Defaults and direct-monitor priority remain unchanged.

## Correctness checks

The new suite passes **3708 checks**: all 16 acceptance truth functions on two colours times all 15 nonempty mark-choice families for each of two letters (3600 automata); 100 seeded multi-state examples; and eight exit/backend/budget/target-overlap/verification-capacity checks. The exhaustive family is checked against a separate deterministic oracle built by enumerating possible recurrent original edge sets. It rewrites 2616 SCCs; remaining examples are already deterministic or inherently weak. It covers mutually exclusive good choices, mixed Fin/Inf, constants and shared-colour contradictions.

All six `make check` suites pass, including 25 SLAA frontend admission checks with enabled, disabled and exhausted-budget colour rewriting. The exit fixture independently matches an LTL formula and passes the existing native determiniser.

## Retained TELA comparison

The scan covers 227 literature positive intermediates, all 300 previous SLAA shape/polarity variants, and three illustrative automata. Two original literature frontend outputs are unavailable; the other 528 preprocessing runs finish and pass source and rewrite equivalence. Both native controls use identical SCC pruning and observed-rank options. An unchanged input reuses its baseline native measurement, explicitly recorded in the manifest.

| Family | Cases | Before native outcomes | After native outcomes |
| --- | ---: | --- | --- |
| literature | 227 | unavailable: 2, non-elevator: 55, ok: 170 | unavailable: 2, acceptance-capacity: 1, non-elevator: 43, ok: 181 |
| shape | 300 | non-elevator: 149, ok: 151 | non-elevator: 149, ok: 151 |
| targeted | 3 | non-elevator: 3 | ok: 3 |

Changed literature intermediates:

| Source | Input / rewritten states | Rewritten colours | Native result |
| --- | ---: | ---: | ---: |
| Parametrised.ltl:26 | 1 / 1 | 4 | 1 |
| Parametrised.ltl:35 | 3 / 3 | 13 | 1 |
| Parametrised.ltl:33 | 1 / 1 | 6 | 1 |
| Parametrised.ltl:34 | 3 / 3 | 10 | 1 |
| Pelanek07.ltl:19;SomenziB00.ltl:4 | 1 / 1 | 3 | 1 |
| Parametrised-Hardness.ltl:10 | 1 / 1 | 7 | 1 |
| Parametrised.ltl:32 | 1 / 1 | 5 | 1 |
| Parametrised.ltl:27 | 1 / 1 | 5 | 1 |
| Parametrised.ltl:36 | 3 / 3 | 16 | acceptance-capacity |
| EtessamiH00.ltl:7 | 1 / 1 | 3 | 1 |
| Parametrised.ltl:25 | 1 / 1 | 3 | 1 |
| Parametrised.ltl:31;Pelanek07.ltl:2 | 1 / 1 | 4 | 1 |

Twelve previously non-elevator positive literature intermediates become elevator; eleven complete native determinisation. Parametrised 36 remains an explicit native acceptance-capacity outcome. The Parametrised-Hardness 8 rewrite fits the construction budget but exceeds capacity during independent equivalence; it is safely retained unchanged. No new state was introduced by preprocessing. None of the 300 targeted shape variants gains eligibility: their remaining hard SCCs have genuine successor nondeterminism or hit a recorded budget, which motivates the next frontend/weak-component phase.

## Integrated LTL sizes

All 454 newly run baseline/enabled outputs are deterministic, complete and equivalent to independent retained positive-language references. A raw eligibility gain is not automatically an end-to-end size gain: many changed examples already have one-state direct GF/FG monitors.

| Mode | Total states, all 227 | Common 222 |
| --- | ---: | ---: |
| cola_combined | 1336 | 984 |
| cola_combined_colour | 1336 | 984 |

Enabled versus baseline: 0 smaller, 227 tied, 0 larger.

## Prior art and remaining priorities

Spot 2.14.1 already unions marks on edges with identical source, guard and destination for Fin-less acceptance. Its [`merge_edges()` source](https://gitlab.lre.epita.fr/spot/spot/-/blob/spot-2-14-1/spot/twa/twagraph.cc) explicitly excludes Fin acceptance and notes its different rules. The mixed-Fin/Inf transformation extends this restricted engineering case; that observation does not establish research novelty. LTL3TELA’s [transition dominance](https://github.com/jurajmajor/ltl3tela/blob/02092adca492678407bd74b5d3bbe103d8c2b400/automaton.cpp) and general [TELA determinisation](https://arxiv.org/abs/2106.15892) are separate points of comparison. No optimality or new unrestricted LTL bound is claimed.

The supplement proves the singleton-SCC graph statement for canonical pure-persistent configuration expansion, while explicitly separating that statement from acceptance lifting and external simplification. It records a sufficient pre-merging temporal syntax. It also states the global-monitor sharing argument and the pruning restriction for a future acceptance-parametric interface. Those statements do not constitute implemented custom SLAA dealternation or shared-monitor parametric determinisation. Generalised co-Büchi weakification is the next implementation priority; the existing backend does not directly support arbitrary such SCCs.

## Reproduction

```sh
make -C build-local -j4 check
python3 tests/benchmark-colour-choice.py
python3 tests/benchmark-slaa.py --tool build-local/external/ltl3tela-master/ltl3tela \
  --modes cola_combined cola_combined_colour --artifacts build-local/colour-integrated \
  --csv tests/colour-choice-integrated-results.csv
python3 tests/summarize-colour-choice.py
```

Source/binary hashes, process limits and artifacts are retained in the companion JSON files and `build-local/colour-choice/` / `build-local/colour-integrated/`. Timings are single-run diagnostics with concurrent campaigns, not runtime rankings.
