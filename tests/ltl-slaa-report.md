# SLAA/TELA elevator route: first implementation milestone

The existing finite-witness, recurrence, persistence and Boolean GF/FG constructions are preserved. An optional external SLAA front end supplies generic-acceptance TELA candidates; certified elevator candidates use the existing native ranked-run determiniser. Non-elevator or failed candidates return to the established residual route.

## Measured literature results

All 227 default and all 227 integrated SLAA-mode outputs passed determinism and reference equivalence. Default state counts match the retained baseline on every formula. SLAA mode is smaller on **1**, ties on **226**, and is larger on **0**.

| Configuration | Total complete states, all 227 |
| --- | ---: |
| COLA default | 1388 |
| COLA + SLAA route | 1387 |

On the unchanged 222-formula external-tool common-success cohort:

| Configuration | Total complete states |
| --- | ---: |
| Spot | 1058 |
| DELAG | 1207 |
| LTL3TELA | 991 |
| OWL SLM21 | 1115 |
| COLA default | 1036 |
| COLA + SLAA route | 1035 |

Offline selection between the new SLAA-mode output and the previously verified COLA-neg candidate gives **992** states on this cohort (previous positive/negative portfolio: 993; LTL3TELA: 991). This is not an online polarity implementation or a new set of negative measurements.

Changed formulas:

| Source | Default | SLAA route |
| --- | ---: | ---: |
| SomenziB00.ltl:23 | 5 | 4 |

## Raw boundary coverage

A separate driver bypasses direct LTL routing and fallback. It receives the whole-formula positive SLAA-derived TELA, validates it against its LTL source, certifies elevator structure, and checks the native deterministic result against both the TELA and retained reference.

| Raw outcome | Formulas |
| --- | ---: |
| frontend-error | 1 |
| frontend-timeout | 1 |
| non-elevator | 55 |
| ok | 170 |

Of 170 successful raw boundaries, **35** had nondeterministic TELA inputs and exercised the native elevator backend; 135 were already deterministic. Rejected inputs are not counted as successful translations. Raw outputs are not selected as a whole-formula portfolio alongside the integrated results.

Integrated route counters (component attempts can exceed formula counts):

- SLAA attempts: 195.
- SLAA frontend failures: 4.
- SLAA non-elevator candidates: 37.
- SLAA validation failures: 0.
- SLAA backend attempts: 33.
- SLAA candidates: 154.
- SLAA components: 138.

## Construction and admission

LTL3TELA is invoked without a shell, with fixed flags `-D0 -b0 -n0 -l0 -t0 -p2`: positive SLAA/dealternation, no external determinisation, no Spot/SPOTELA candidate portfolio, no complement alternative, no Boolean splitting, and no Fin-to-TGBA conversion. Upstream generic postprocessing remains enabled. Acceptance semantics and mark ownership are preserved by its dealternation; the textual acceptance expression need not remain identical.

Known direct fragments compare successful candidates with the existing deterministic and checked DBA candidates by complete states, acceptance sets, then edges. Other successful residual candidates can bypass NBA construction. Both TELA/source and deterministic-result/TELA equivalence are mandatory gates. Buchi-specific simulation and stutter acceleration are disabled at the new generic boundary; bounded exact-language preorder/union pruning remains available. No formula annotations are used to certify generic TELA pruning.

The frontend child has a 5-second default deadline, an 8 MiB output limit and no core dumps. Its process group is killed and reaped on timeout. The input TELA cap is 256 states. Zero time/state budgets skip the candidate. These limits do not bound child memory, parser allocations, native determinisation or exact language checks. The benchmark separately applies a 30-second outer command limit.

## Failure found and fixed

The first full run exposed an assertion on SomenziB00 line 23, with acceptance `Fin(3)&Fin(2)&Fin(1)&Fin(0)`. Spot can initially leave Fin-SCC acceptance undecided. A rejecting deterministic SCC with varying marks was classified as neither weak nor accepting, and hit the successor assertion. Resolving unknown SCC acceptance before classification fixes the error. A small three-state Fin regression now exercises this case with exact pruning both off and on. An unexpected unclassified successor now throws, permitting the optional route to fall back rather than aborting the process. A pre-existing unconditional complete-automaton debug print was also removed from the HOA output path.

## Reproduction and validation

Build locally, then run:

```sh
make -C build-local -j4 check
python3 tests/benchmark-slaa.py --tool build-local/external/ltl3tela-master/ltl3tela
python3 tests/summarize-slaa.py
```

The external tool is the pinned LTL3TELA 2.1.1 build from the original comparison (commit `02092adca492678407bd74b5d3bbe103d8c2b400`, with the retained Clang template-instantiation patch). No source from it is vendored or rewritten. CSV and source/binary hashes are in `ltl-slaa-results.csv` and `ltl-slaa-results.json`; HOA and stderr artifacts are under `build-local/slaa-comparison/`. The raw driver elapsed column covers the driver and its checks, excluding frontend translation; integrated elapsed covers the whole translator command. These single-run timings include checking and possible concurrent regression activity and are not runtime rankings.

`make check` covers eight historical elevator fixtures, 17 specialized fragment fixtures, 22 generic-acceptance fixtures and 15 frontend admission/fallback checks. The full smoke suite and seeded finite-witness/scaling rerun are retained separately; see `finite-witness-slaa-regressions.csv`.

This milestone does not implement new SLAA dealternation rules, local SCC semi-determinisation, profile scoring by rank pressure, local acceptance-colour compaction, or an online polarity portfolio. Non-elevator candidates continue through the existing translator, including its bounded profile refinement and deterministic fallback. The new route remains opt-in while those improvements are evaluated.
