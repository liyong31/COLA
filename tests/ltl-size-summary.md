# OWL literature: measured size summary

227 unique formula strings; 1362 tool runs; 222 formulas in the common verified cohort.

References are deterministic; other valid rows are deterministic and language-equivalent to the reference. Where Spot fails, an explicitly labelled alternate reference is used for available pairs. All main size comparisons use the same common cohort. Automata are completed and unreachable states removed; no common minimisation is applied.

## Outcomes

| Tool | alternate-reference | ok | reference | timeout | translation-error |
| --- | --- | --- | --- | --- | --- |
| Spot | 0 | 0 | 225 | 2 | 0 |
| DELAG | 2 | 225 | 0 | 0 | 0 |
| LTL3TELA | 0 | 222 | 0 | 4 | 1 |
| OWL SLM21 | 0 | 227 | 0 | 0 | 0 |
| COLA | 0 | 225 | 0 | 2 | 0 |
| COLA reset | 0 | 225 | 0 | 2 | 0 |

## Complete reachable automata

Best counts include ties; strict best requires being smaller than every other configuration. State ratios are geometric means of per-formula tool/Spot ratios; lower is better.

| Tool | Best incl. ties | Strict best | Total states | Median states | Max states | State ratio / Spot | Total edges |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Spot | 207 | 0 | 1058 | 3 | 65 | 1.0000 | 4906 |
| DELAG | 194 | 0 | 1207 | 4 | 68 | 1.0517 | 8304 |
| LTL3TELA | 217 | 2 | 991 | 3 | 42 | 0.9784 | 4120 |
| OWL SLM21 | 183 | 0 | 1115 | 4 | 42 | 1.0606 | 5613 |
| COLA | 192 | 0 | 1337 | 4 | 84 | 1.1467 | 13145 |
| COLA reset | 191 | 0 | 1338 | 4 | 84 | 1.1482 | 13149 |

## Paired state comparisons

Each cell is row-tool wins / ties / losses against the column tool. These comparisons use every formula verified for that particular pair, including formulas excluded from the all-tool cohort.

| Row vs column | Spot | DELAG | LTL3TELA | OWL SLM21 | COLA | COLA reset |
| --- | --- | --- | --- | --- | --- | --- |
| Spot | — | 26 / 188 / 11 | 0 / 211 / 11 | 38 / 178 / 9 | 18 / 202 / 5 | 18 / 203 / 4 |
| DELAG | 11 / 188 / 26 | — | 4 / 190 / 28 | 15 / 197 / 15 | 26 / 171 / 28 | 26 / 172 / 27 |
| LTL3TELA | 11 / 211 / 0 | 28 / 190 / 4 | — | 39 / 179 / 4 | 26 / 195 / 1 | 27 / 194 / 1 |
| OWL SLM21 | 9 / 178 / 38 | 15 / 197 / 15 | 4 / 179 / 39 | — | 25 / 165 / 35 | 25 / 165 / 35 |
| COLA | 5 / 202 / 18 | 28 / 171 / 26 | 1 / 195 / 26 | 35 / 165 / 25 | — | 1 / 224 / 0 |
| COLA reset | 4 / 203 / 18 | 27 / 172 / 26 | 1 / 194 / 27 | 35 / 165 / 25 | 0 / 224 / 1 | — |

## Raw reachable state counts

The same common cohort before completion. Missing rejecting sinks can reduce these counts by one.

| Tool | Total raw states | Best incl. ties |
| --- | --- | --- |
| Spot | 926 | 207 |
| DELAG | 1075 | 194 |
| LTL3TELA | 863 | 215 |
| OWL SLM21 | 983 | 183 |
| COLA | 1205 | 192 |
| COLA reset | 1206 | 191 |

## Common-cohort state ratios by collection

Geometric mean tool/Spot state ratio. A formula appearing in multiple collections contributes once to each relevant collection.

| Collection | N | Spot | DELAG | LTL3TELA | OWL SLM21 | COLA | COLA reset |
| --- | --- | --- | --- | --- | --- | --- | --- |
| DwyerAC98.ltl | 55 | 1.0000 | 1.1096 | 0.9482 | 1.0127 | 0.9823 | 0.9823 |
| EtessamiH00.ltl | 12 | 1.0000 | 1.0505 | 0.9889 | 1.1661 | 0.9763 | 0.9763 |
| Liberouter04.ltl | 52 | 1.0000 | 0.9884 | 0.9829 | 0.9938 | 0.9950 | 0.9950 |
| Parametrised-Hardness.ltl | 17 | 1.0000 | 1.1176 | 1.0000 | 1.0706 | 2.4670 | 2.4670 |
| Parametrised.ltl | 45 | 1.0000 | 1.0234 | 0.9963 | 1.1443 | 1.3430 | 1.3430 |
| Pelanek07.ltl | 20 | 1.0000 | 1.0145 | 1.0000 | 1.0873 | 1.0661 | 1.0661 |
| SickertEJK16.ltl | 3 | 1.0000 | 1.2599 | 0.9086 | 1.2331 | 1.1447 | 1.2599 |
| SomenziB00.ltl | 26 | 1.0000 | 1.0622 | 0.9830 | 1.0806 | 1.0926 | 1.0926 |

## Cases with the largest state spread

Sorted by largest/smallest complete state count in the common cohort. All formulas and source lines are in the CSV.

| Source | Spot | DELAG | LTL3TELA | OWL SLM21 | COLA | COLA reset |
| --- | --- | --- | --- | --- | --- | --- |
| Parametrised-Hardness.ltl:9 | 1 | 1 | 1 | 1 | 84 | 84 |
| Parametrised.ltl:36 | 1 | 1 | 1 | 1 | 66 | 66 |
| Parametrised.ltl:35 | 1 | 1 | 1 | 1 | 28 | 28 |
| Parametrised-Hardness.ltl:8 | 1 | 1 | 1 | 1 | 12 | 12 |
| Parametrised-Hardness.ltl:12 | 1 | 1 | 1 | 1 | 12 | 12 |
| Parametrised.ltl:34 | 1 | 1 | 1 | 1 | 11 | 11 |
| DwyerAC98.ltl:15 | 7 | 68 | 7 | 8 | 7 | 7 |
| Parametrised-Hardness.ltl:7 | 1 | 1 | 1 | 1 | 8 | 8 |
| Parametrised-Hardness.ltl:11 | 1 | 1 | 1 | 1 | 8 | 8 |
| DwyerAC98.ltl:45 | 17 | 39 | 6 | 22 | 17 | 17 |
| Parametrised-Hardness.ltl:10 | 1 | 1 | 1 | 1 | 6 | 6 |
| Parametrised.ltl:42 | 16 | 16 | 16 | 31 | 65 | 65 |

## Reset routing

- Formula runs with completed finite-witness monitors: 7.
- Formula runs with budget aborts: 0.

Do not attribute unchanged fast-path or fallback outputs to the reset construction. Timings in the CSV are single-process diagnostic elapsed times, not repeated performance benchmarks.
