# OWL literature: measured size summary

Updated rows: `ltl-fragment-results.csv`; other tool outputs are reused from the original campaign.

227 unique formula strings; 1362 tool runs; 222 formulas in the common verified cohort.

References are deterministic; other valid rows are deterministic and language-equivalent to the reference. Where Spot fails, an explicitly labelled alternate reference is used for available pairs. All main size comparisons use the same common cohort. Automata are completed and unreachable states removed; no common minimisation is applied.

## Outcomes

| Tool | alternate-reference | ok | reference | timeout | translation-error |
| --- | --- | --- | --- | --- | --- |
| Spot | 0 | 0 | 225 | 2 | 0 |
| DELAG | 2 | 225 | 0 | 0 | 0 |
| LTL3TELA | 0 | 222 | 0 | 4 | 1 |
| OWL SLM21 | 0 | 227 | 0 | 0 | 0 |
| COLA | 0 | 227 | 0 | 0 | 0 |
| COLA reset | 0 | 227 | 0 | 0 | 0 |

## Complete reachable automata

Best counts include ties; strict best requires being smaller than every other configuration. State ratios are geometric means of per-formula tool/Spot ratios; lower is better.

| Tool | Best incl. ties | Strict best | Total states | Median states | Max states | State ratio / Spot | Total edges |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Spot | 207 | 0 | 1058 | 3 | 65 | 1.0000 | 4906 |
| DELAG | 194 | 0 | 1207 | 4 | 68 | 1.0517 | 8304 |
| LTL3TELA | 217 | 2 | 991 | 3 | 42 | 0.9784 | 4120 |
| OWL SLM21 | 183 | 0 | 1115 | 4 | 42 | 1.0606 | 5613 |
| COLA | 207 | 0 | 1036 | 3 | 50 | 0.9968 | 4625 |
| COLA reset | 203 | 0 | 1108 | 3 | 65 | 1.0132 | 4771 |

## Paired state comparisons

Each cell is row-tool wins / ties / losses against the column tool. These comparisons use every formula verified for that particular pair, including formulas excluded from the all-tool cohort.

| Row vs column | Spot | DELAG | LTL3TELA | OWL SLM21 | COLA | COLA reset |
| --- | --- | --- | --- | --- | --- | --- |
| Spot | — | 26 / 188 / 11 | 0 / 211 / 11 | 38 / 178 / 9 | 3 / 217 / 5 | 6 / 215 / 4 |
| DELAG | 11 / 188 / 26 | — | 4 / 190 / 28 | 15 / 197 / 15 | 12 / 184 / 31 | 15 / 182 / 30 |
| LTL3TELA | 11 / 211 / 0 | 28 / 190 / 4 | — | 39 / 179 / 4 | 11 / 210 / 1 | 15 / 206 / 1 |
| OWL SLM21 | 9 / 178 / 38 | 15 / 197 / 15 | 4 / 179 / 39 | — | 10 / 177 / 40 | 13 / 177 / 37 |
| COLA | 5 / 217 / 3 | 31 / 184 / 12 | 1 / 210 / 11 | 40 / 177 / 10 | — | 4 / 223 / 0 |
| COLA reset | 4 / 215 / 6 | 30 / 182 / 15 | 1 / 206 / 15 | 37 / 177 / 13 | 0 / 223 / 4 | — |

## Raw reachable state counts

The same common cohort before completion. Missing rejecting sinks can reduce these counts by one.

| Tool | Total raw states | Best incl. ties |
| --- | --- | --- |
| Spot | 926 | 207 |
| DELAG | 1075 | 194 |
| LTL3TELA | 863 | 215 |
| OWL SLM21 | 983 | 183 |
| COLA | 904 | 207 |
| COLA reset | 976 | 203 |

## Common-cohort state ratios by collection

Geometric mean tool/Spot state ratio. A formula appearing in multiple collections contributes once to each relevant collection.

| Collection | N | Spot | DELAG | LTL3TELA | OWL SLM21 | COLA | COLA reset |
| --- | --- | --- | --- | --- | --- | --- | --- |
| DwyerAC98.ltl | 55 | 1.0000 | 1.1096 | 0.9482 | 1.0127 | 0.9823 | 0.9823 |
| EtessamiH00.ltl | 12 | 1.0000 | 1.0505 | 0.9889 | 1.1661 | 0.9763 | 0.9763 |
| Liberouter04.ltl | 52 | 1.0000 | 0.9884 | 0.9829 | 0.9938 | 0.9950 | 0.9950 |
| Parametrised-Hardness.ltl | 17 | 1.0000 | 1.1176 | 1.0000 | 1.0706 | 1.0000 | 1.0000 |
| Parametrised.ltl | 45 | 1.0000 | 1.0234 | 0.9963 | 1.1443 | 1.0000 | 1.0773 |
| Pelanek07.ltl | 20 | 1.0000 | 1.0145 | 1.0000 | 1.0873 | 1.0298 | 1.0298 |
| SickertEJK16.ltl | 3 | 1.0000 | 1.2599 | 0.9086 | 1.2331 | 0.9086 | 1.0000 |
| SomenziB00.ltl | 26 | 1.0000 | 1.0622 | 0.9830 | 1.0806 | 1.0198 | 1.0198 |

## Cases with the largest state spread

Sorted by largest/smallest complete state count in the common cohort. All formulas and source lines are in the CSV.

| Source | Spot | DELAG | LTL3TELA | OWL SLM21 | COLA | COLA reset |
| --- | --- | --- | --- | --- | --- | --- |
| DwyerAC98.ltl:15 | 7 | 68 | 7 | 8 | 7 | 7 |
| DwyerAC98.ltl:45 | 17 | 39 | 6 | 22 | 17 | 17 |
| Parametrised.ltl:42 | 16 | 16 | 16 | 31 | 16 | 65 |
| DwyerAC98.ltl:55 | 13 | 52 | 13 | 28 | 13 | 13 |
| Parametrised.ltl:33 | 1 | 1 | 1 | 4 | 1 | 1 |
| DwyerAC98.ltl:40 | 4 | 14 | 4 | 6 | 4 | 4 |
| Parametrised.ltl:41 | 8 | 8 | 8 | 15 | 8 | 25 |
| Parametrised.ltl:32 | 1 | 1 | 1 | 3 | 1 | 1 |
| SomenziB00.ltl:12 | 1 | 3 | 1 | 3 | 1 | 1 |
| DwyerAC98.ltl:50 | 11 | 32 | 11 | 21 | 12 | 12 |
| DwyerAC98.ltl:44 | 20 | 9 | 8 | 8 | 8 | 8 |
| SomenziB00.ltl:13 | 2 | 5 | 2 | 5 | 2 | 2 |

## Reset routing

- Formula runs with completed finite-witness monitors: 7.
- Formula runs with budget aborts: 0.

Do not attribute unchanged fast-path or fallback outputs to the reset construction. Timings in the CSV are single-process diagnostic elapsed times, not repeated performance benchmarks.
