# COLA polarity experiment

Translate `!phi` with the existing default COLA, complete the deterministic graph, then complement its acceptance condition to obtain `phi`. Completion and acceptance complement are separate commands; no minimization is applied. All sizes below are reachable complete states. Positive COLA and external-tool rows are reused from the previous verified campaigns.

227 negated translations: 224 verified successes. Failures, if any, remain in `ltl-polarity-results.csv` and are excluded from paired metrics.

Against positive COLA on 224 verified pairs: **11 smaller, 206 tied, 7 larger**.

- COLA: 1050 total states over these 224 pairs.
- COLA-neg: 4030 total states over these 224 pairs.
- Best of both: 1007 total states over these 224 pairs.

Across all 227 formulas, retaining positive COLA when the negative attempt fails gives 1345 portfolio states versus 1388 positive states. This fallback prevents a negative timeout from losing an already available result.

| Unsuccessful negative attempt | Outcome | Positive COLA states |
| --- | --- | ---: |
| Parametrised-Hardness.ltl:2 | translation-timeout | 83 |
| Parametrised-Hardness.ltl:4 | translation-timeout | 148 |
| Parametrised-Hardness.ltl:6 | translation-timeout | 107 |

Each translation has a 30-second limit. These are resource failures of the negative route; no output from them is counted as equivalent. The current guard-preservation rule recognizes safety conjunctions; negation changes their Boolean structure, so it need not retain the same translation route.

Diagnostic Spot calls on these three negated formulas with `ltl2tgba -D -G -x ltl-split=0 -f "!(FORMULA)"` finish in roughly 36, 77 and 132 ms, with 83, 148 and 107 complete states, respectively. All three outputs passed positive-language equivalence after completion and acceptance complement. See `ltl-polarity-probes.json`. This demonstrates an avoidable route on these inputs; the probe outputs are not substituted into COLA-neg measurements. Extending constraint preservation to the dual Boolean structure is a concrete further routing improvement.

## Comparison with external tools

The same 222 formulas succeed for every listed configuration. Best counts include ties. The portfolio selects by complete states, acceptance sets, then edges, with positive polarity breaking exact ties. It is an offline selection from measured candidates, not a new translator option.

| Configuration | Total states | Smallest incl. ties | Total edges |
| --- | ---: | ---: | ---: |
| Spot | 1058 | 207 | 4906 |
| DELAG | 1207 | 194 | 8304 |
| LTL3TELA | 991 | 217 | 4120 |
| OWL SLM21 | 1115 | 183 | 5613 |
| COLA | 1036 | 207 | 4625 |
| COLA reset | 1108 | 203 | 4771 |
| COLA-neg | 4016 | 213 | 57129 |
| COLA best of both | 993 | 218 | 4169 |

Remaining differences between the portfolio and LTL3TELA:

| Source | COLA best of both | LTL3TELA |
| --- | ---: | ---: |
| DwyerAC98.ltl:50 | 12 | 11 |
| EtessamiH00.ltl:12 | 6 | 7 |
| Liberouter04.ltl:40 | 5 | 6 |
| Liberouter04.ltl:41 | 7 | 8 |
| Liberouter04.ltl:42 | 7 | 8 |
| Liberouter04.ltl:43 | 9 | 10 |
| Pelanek07.ltl:7 | 9 | 5 |
| SomenziB00.ltl:21 | 5 | 4 |
| SomenziB00.ltl:23 | 5 | 4 |

## Formulas whose state counts change

| Source | COLA | COLA-neg |
| --- | ---: | ---: |
| DwyerAC98.ltl:15 | 7 | 24 |
| DwyerAC98.ltl:45 | 17 | 6 |
| DwyerAC98.ltl:46 | 6 | 4 |
| DwyerAC98.ltl:50 | 12 | 691 |
| DwyerAC98.ltl:51 | 6 | 4 |
| DwyerAC98.ltl:55 | 13 | 1788 |
| EtessamiH00.ltl:12 | 6 | 486 |
| Liberouter04.ltl:13 | 16 | 65 |
| Liberouter04.ltl:36 | 50 | 34 |
| Liberouter04.ltl:40 | 6 | 5 |
| Liberouter04.ltl:41 | 8 | 7 |
| Liberouter04.ltl:42 | 8 | 7 |
| Liberouter04.ltl:43 | 10 | 9 |
| Liberouter04.ltl:44 | 9 | 7 |
| Parametrised.ltl:15 | 13 | 11 |
| Pelanek07.ltl:7 | 9 | 31 |
| SickertEJK16.ltl:3 | 3 | 4 |
| SomenziB00.ltl:20 | 10 | 6 |

Geometric mean COLA-neg/COLA state ratio over verified pairs: 1.0636.

## Reproduction and interpretation

Run `python3 tests/compare-cola-polarities.py`, then `python3 tests/summarize-cola-polarities.py`. Retained HOA intermediates are under `build-local/polarity-comparison/`. Source revision, binary/input hashes and timeout are recorded in `ltl-polarity-results.json`. Translation, completion/complement, and validation times are separate CSV columns; these are single runs, not stable runtime rankings.

Equivalence is checked against the original positive-language Spot reference, or the previously independently checked DELAG reference where Spot timed out. Every negative graph is checked deterministic before complementation, and the completed graph must retain its states, edges, acceptance-set count, determinism and completeness after acceptance complement.

Ten additional semantic boundary checks passed against fresh Spot references: `0`, `1`, `a`, `!a`, `G a`, `F a`, `GF a`, `FG a`, `G(a -> X b)`, and `GF(a & X b) & FG c`. For example, translating the negation of `F a` produces an incomplete one-state graph; completion makes it two states before acceptance is complemented. Boundary HOA artifacts remain under `build-local/polarity-boundaries/`.

Polarity selection complements specialized fragment routing: negative translation can expose a cheaper construction, but can also cause severe growth. Keep the positive candidate and bound any future additional attempt. Merely negating globally does not reproduce LTL3TELA’s full compositional polarity selection. The existing finite-witness construction and translator defaults are unchanged.
