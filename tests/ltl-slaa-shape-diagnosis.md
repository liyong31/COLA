# Why LTL3TELA wins, and what to change before determinisation

This follow-up studies the ten formulas where LTL3TELA beats the first integrated positive-SLAA COLA mode. It retains that earlier campaign as a baseline. There are 80 full-tool winner ablations and 300 SLAA-shape/polarity experiments: ten formulas, fifteen variants, two polarities. Every admitted positive-language result is independently checked against the retained Spot reference.

## The causes differ across examples

| Source | Previous positive SLAA mode | LTL3TELA | Full-tool winner | No complement | No composition | No U/G merging | New COLA portfolio |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| DwyerAC98.ltl:45 | 17 | 6 | neg | 17 | 6 | 6 | 6 |
| DwyerAC98.ltl:46 | 6 | 4 | neg | 6 | 4 | 4 | 4 |
| DwyerAC98.ltl:50 | 12 | 11 | spot | 11 | 11 | 11 | 11 |
| DwyerAC98.ltl:51 | 6 | 4 | neg | 7 | 4 | 4 | 4 |
| Liberouter04.ltl:36 | 50 | 34 | neg | 65 | 34 | 34 | 34 |
| Liberouter04.ltl:44 | 9 | 7 | neg | 9 | 7 | 7 | 7 |
| Parametrised.ltl:15 | 13 | 11 | neg | 13 | 11 | 11 | 10 |
| Pelanek07.ltl:7 | 9 | 5 | basic | 5 | 5 | 5 | 5 |
| SomenziB00.ltl:20 | 10 | 6 | basic | 6 | 6 | 6 | 6 |
| SomenziB00.ltl:21 | 5 | 4 | Ga;basic / Gb;basic / Ga;basic / GFc;basic / Gb;basic / GF!c;basic | 4 | 5 | 4 | 4 |

Six full-tool winners select `neg`; disabling complement loses their sizes. Dwyer 50 selects `spot`, not the SLAA engine. Pelanek 7 and Somenzi 20 select `basic`; they retain their size without complement. Somenzi 21 benefits from composition: disabling it changes four states to five. Its negative whole-formula SLAA nevertheless gives COLA an alternative four-state construction. Winner names describe the observed selected portfolio candidate, not a proof that it is the only way to obtain that size. The clean no-merging column retains the rest of the full portfolio. The historical `no_merging` variant also sets `-b0` and disables transition reduction; it is retained separately in the CSV. On Dwyer 50, that combined ablation gives 12 states because it removes the winning Spot candidate, while the clean no-merging variant retains 11.

Dwyer 50 exposed a COLA routing choice: the existing elevator BA route returns a valid 12-state result before considering the 11-state deterministic formula translation. Additional High postprocessing of the 12-state result still gives 12; translating the source formula afresh gives 11. The new mode compares these alternatives.

Pelanek 7 exposed another early return: X-advice produces nine states before any SLAA attempt. Its positive SLAA has five states and gives a four-state TELA with one hard SCC. Its negative SLAA also has five states, but gives a five-state elevator TELA; the native backend and complement give five states for the original language. A slightly larger, structurally suitable intermediate is preferable here.

## Manipulating SLAA construction

The fifteen variants independently change U-merging for NA size (`-F1`), avoidance of looping alternating merges (`-F3`), disabled U/G merging, G-merging level, transition reduction, basic/no dominance, single X successor, disjunction merging, a single initial state, formula simplification, NA equivalence, and acceptance conversion (`-t1`, diagnostic only). Baseline uses `-D0 -b0 -n0 -l0 -t0`; each formula is explicitly tested in both polarities.

| Source | Polarity | SLAA states | TELA states | Hard SCCs | Checked native complete states | General Spot diagnostic states |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| DwyerAC98.ltl:45 | positive | 6 | 8 | 1 | rejected | 113 |
| DwyerAC98.ltl:45 | negative | 6 | 4 | 0 | 6 | — |
| DwyerAC98.ltl:46 | positive | 4 | 4 | 1 | rejected | 21 |
| DwyerAC98.ltl:46 | negative | 3 | 3 | 0 | 4 | — |
| DwyerAC98.ltl:50 | positive | 7 | 12 | 1 | rejected | 49 |
| DwyerAC98.ltl:50 | negative | 7 | 11 | 1 | rejected | 13 |
| DwyerAC98.ltl:51 | positive | 4 | 4 | 1 | rejected | 25 |
| DwyerAC98.ltl:51 | negative | 4 | 3 | 0 | 4 | — |
| Liberouter04.ltl:36 | positive | 12 | 34 | 1 | rejected | 82 |
| Liberouter04.ltl:36 | negative | 12 | 19 | 0 | 34 | — |
| Liberouter04.ltl:44 | positive | 5 | 6 | 1 | rejected | 14 |
| Liberouter04.ltl:44 | negative | 5 | 7 | 0 | 7 | — |
| Parametrised.ltl:15 | positive | 5 | 5 | 1 | rejected | 39 |
| Parametrised.ltl:15 | negative | 5 | 8 | 0 | 10 | — |
| Pelanek07.ltl:7 | positive | 5 | 4 | 1 | rejected | 18 |
| Pelanek07.ltl:7 | negative | 5 | 5 | 0 | 5 | — |
| SomenziB00.ltl:20 | positive | 7 | 14 | 1 | rejected | 6 |
| SomenziB00.ltl:20 | negative | 7 | 4 | 0 | 6 | — |
| SomenziB00.ltl:21 | positive | 5 | 6 | 0 | 8 | — |
| SomenziB00.ltl:21 | negative | 6 | 8 | 0 | 4 | — |

No tested shape variant improves the best native result across both baseline polarities for any of these ten formulas. This does not establish that SLAA rewriting is unhelpful outside this grid. Some individual positive paths do improve: on Somenzi 21, `-i1` or `-O1` changes the TELA from six to four states and the normalized native result from eight to five. Its unchanged negative baseline is still better at four.

Merging is context-dependent. On Somenzi 21, disabling U/G merging shrinks the negative TELA from eight to six states but worsens the final result from four to five. The full LTL3TELA portfolio compensates through composition and still reaches four without merging.

Acceptance-aware dominance matters for downstream structure: on Pelanek 7, disabling it changes the negative TELA from five elevator states to six states with a hard SCC. On Dwyer 45, disabling dominance keeps the positive SLAA/TELA state counts at six/eight, while the separate general Spot determinisation grows from 113 to 8241 states. State counts alone miss transition and acceptance structure.

The shape grid has 151 admitted native results and 149 non-elevator TELA inputs. General Spot determinisation of the latter is kept strictly separate as a diagnostic; all 149 diagnostic results also pass positive-language equivalence. No non-elevator input is admitted to COLA’s elevator backend. Fin-to-TGBA conversion is not enabled in the implemented portfolio.

## Implemented improvement

Use `--slaa-tool=PATH --slaa-portfolio` to try the positive and negative SLAA-derived generic TELA. Each candidate must pass elevator and source-language checks; a nondeterministic candidate uses COLA’s existing backend. A negative deterministic result is normalized, completed, and only then has its acceptance complemented. It is checked again against the positive source. Exact candidate ties retain positive polarity. Failure of either attempt retains the other.

The mode also lets the successful X-advice candidate compete with SLAA candidates, and compares a surviving elevator BA result with deterministic source-formula translation. These comparisons account for the Pelanek and Dwyer early-return cases above. Existing GF/FG, recurrence, persistence and finite-witness monitors keep priority. Default and positive-only SLAA behavior remain unchanged.

SCC pruning is retained at the native boundary. A controlled on/off experiment with the same negative TELA gives Parametrised 15 eleven versus ten states, and Liberouter 36 thirty-five versus thirty-four. All four outputs pass equivalence; the measurements are in `ltl-slaa-scc-probes.json`.

## Full-corpus validation

All 681 outputs across 227 formulas and three COLA modes pass determinism and independent reference equivalence. Against default COLA, the new portfolio has **15 wins, 212 ties and 0 losses**. Default counts reproduce the previous baseline.

| Configuration | Total complete states, all 227 | Total on common 222 |
| --- | ---: | ---: |
| COLA default | 1388 | 1036 |
| Positive SLAA mode | 1387 | 1035 |
| SLAA polarity portfolio | 1337 | 985 |
| Spot | — | 1058 |
| DELAG | — | 1207 |
| LTL3TELA | — | 991 |
| OWL SLM21 | — | 1115 |

Against LTL3TELA on those 222 matched formulas: 6 smaller, 216 tied, 0 larger. This comparison reuses the four external tools’ original verified outputs; all 80 targeted LTL3TELA ablations were newly rerun. It is a size comparison, not a runtime ranking.

Integrated portfolio counters:

- SLAA attempts: 404.
- SLAA frontend failures: 8.
- SLAA non-elevator candidates: 67.
- SLAA validation failures: 0.
- SLAA backend attempts: 94.
- SLAA candidates: 329.
- SLAA components: 177.
- SLAA negative attempts: 202.
- SLAA negative candidates: 174.
- SLAA negative components: 39.
- SLAA formula candidates: 1.
- SLAA formula components: 1.
- SLAA formula failures: 0.

## Reproduction and next construction work

```sh
python3 tests/diagnose-ltl-sizes.py --updated-cola tests/ltl-slaa-results.csv \
  --artifacts build-local/slaa-portfolio --csv tests/ltl-slaa-winner-ablations.csv
python3 tests/diagnose-slaa-shapes.py
python3 tests/benchmark-slaa.py --tool build-local/external/ltl3tela-master/ltl3tela \
  --modes cola_current cola_slaa cola_slaa_portfolio \
  --artifacts build-local/slaa-portfolio-comparison --csv tests/ltl-slaa-portfolio-results.csv
python3 tests/summarize-slaa-shapes.py
```

The raw driver’s `--integrated` option enables the same SCC pruning as the translator. The historical raw-driver mode remains available. Source/binary hashes, flags and limits are in the companion JSON manifests. Shape experiments use two workers and a five-second limit per process; general determinisation outcomes are independently labelled. The integrated frontend keeps its five-second limit per attempt, 8 MiB output cap and 256-state admission cap. Trying both polarities can spend two frontend deadlines per residual. These are not hard bounds on native construction or language checking.

The expanded 22 admission/fallback checks include both polarity failures, incomplete negative safety automata, zero budgets and direct-monitor priority. The full finite-witness suite was also run through a wrapper enabling the new portfolio: all 387 measured outputs and 585 budget/bypass checks pass. See `finite-witness-slaa-portfolio-regressions.csv`.

The next SLAA transformation objective should be the shape of the dealternated TELA: hard SCCs, concurrent ranked runs and acceptance footprint, with state count as another cost rather than the sole target. Keep a small Pareto set of certified alternatives; protect stable guards and mark ownership during any merge or transition subsumption. The measured acceptance-aware dominance and single-initial variants are useful starting points, but the grid does not justify enabling extra shape variants by default. New custom SLAA rewrites and SCC-local elevatorization remain future work.

The theoretical SLAA/acceptance basis is described in the [SLAA paper](https://arxiv.org/abs/1908.04645); the pinned [construction](https://github.com/jurajmajor/ltl3tela/blob/02092adca492678407bd74b5d3bbe103d8c2b400/alternating.cpp) and [dealternation/portfolio implementation](https://github.com/jurajmajor/ltl3tela/blob/02092adca492678407bd74b5d3bbe103d8c2b400/nondeterministic.cpp) supply the tested upstream variants.
