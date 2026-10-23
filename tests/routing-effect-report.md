# Effect of specialized-first routing

Both implementation PRs were merged on 23 October 2026 into `ltl2dela`:
[PR #2](https://github.com/liyong31/COLA/pull/2) and
[PR #3](https://github.com/liyong31/COLA/pull/3).
The final merge is `178da6c148323a0aa52d052ade8f97899c3750a0`.

Strict specialized priority substantially reduces external frontend work,
but gives up some state-count improvements of the previous portfolio.
This is a routing-policy comparison, not a ranking of primitive algorithms.

## Controlled build and correctness

Before: `cc2dc27634fd187758051275ad2a0175468991dd`. After: `2c83c3c7aad4b56df0b22aa6c33b796d60066655`.
The only changed production file is `src/ltl2dela.cpp`. The old version of
that file was rebuilt with the same compiler/options and linked against
identical other object files. Both variants use the same executable and
separate frozen runtime libraries selected through `DYLD_LIBRARY_PATH`.
The native SCC determiniser, acceptance implementation, Spot installation,
LTL3TELA and OWL executables are identical. Build commands and all measured
hashes are recorded in the result manifest.

All **1816 outputs** (227 formulas × four configurations × two policies)
pass independent language equivalence, determinism and completeness.
There are no translation/checking timeouts or language failures.

Primary sizes count complete reachable output states without extra
minimization. A second identical Spot low/generic normalization is also
recorded; it is kept separate from the primary metric.

## State counts and external calls

| Configuration | Before states | After states | Smaller / equal / larger | Frontend calls before → after |
| --- | ---: | ---: | --- | ---: |
| default | 1388 | 1388 | 0 / 227 / 0 | 0 → 0 |
| finite_witness | 1460 | 1460 | 0 / 227 / 0 | 0 → 0 |
| portfolio | 1336 | 1387 | 0 / 213 / 14 | 788 → 26 |
| finite_witness_portfolio | 1408 | 1459 | 0 / 213 / 14 | 788 → 26 |

`default` has no external frontends. `finite_witness` enables the optional
bounded reset construction. `portfolio` enables both SLAA polarities,
colour/weak preprocessing, both OWL LDGBA algorithms and polarities,
annotation pruning and same-input cross-SCC comparison.
`finite_witness_portfolio` enables both options. All other budgets and
translation settings are matched exactly.

The state-count benefit of a generic candidate is therefore not implied
by applicability of a specialized construction. The requested strict
priority remains implemented: this experiment does not re-enable generic
competition after specialization succeeds.

Additional normalization totals:

| Configuration | Before | After |
| --- | ---: | ---: |
| default | 1384 | 1384 |
| finite_witness | 1456 | 1456 |
| portfolio | 1336 | 1383 |
| finite_witness_portfolio | 1408 | 1455 |

Largest portfolio state increases:

| Formula source | Before | After | Increase |
| --- | ---: | ---: | ---: |
| Liberouter04.ltl:36 | 34 | 50 | 16 |
| DwyerAC98.ltl:45 | 6 | 17 | 11 |
| Pelanek07.ltl:7 | 5 | 9 | 4 |
| SomenziB00.ltl:20 | 6 | 10 | 4 |
| DwyerAC98.ltl:46 | 3 | 6 | 3 |
| Parametrised.ltl:15 | 10 | 13 | 3 |
| DwyerAC98.ltl:51 | 4 | 6 | 2 |
| Liberouter04.ltl:44 | 7 | 9 | 2 |
| Liberouter04.ltl:40 | 5 | 6 | 1 |
| Liberouter04.ltl:42 | 7 | 8 | 1 |

The two largest losses expose different previously winning routes:
Liberouter36 used an LDGBA result (34 states), whereas Dwyer45 used an
SLAA result (six states). Both now return from the recognized-fragment
route (50 and 17 states). That broad route invokes the existing Spot
deterministic Low/High translation; syntactic class membership alone is
not a certificate that a dedicated fragment construction was selected
inside Spot. Tightening this distinction is a useful follow-up, without
overriding successful direct monitors or checked DBA/DCA constructions.

## Serial timing controls

The full corpus used two workers; its single-run timings are descriptive
and are not used as a runtime ranking. After it finished, seven selected
formulas were timed serially, with three repetitions and randomly
interleaved before/after order. Every run starts fresh translator and
frontend processes. The timer excludes subsequent validation and metric
extraction. All repeated output state counts match the corpus campaign.

| Formula source | Default before / after (ms) | Portfolio before / after (ms) |
| --- | ---: | ---: |
| DwyerAC98.ltl:45 | 34.0 / 33.3 | 1485.5 / 32.3 |
| DwyerAC98.ltl:46 | 7.6 / 7.8 | 1261.0 / 8.2 |
| DwyerAC98.ltl:50 | 26.6 / 26.3 | 1922.4 / 1910.5 |
| DwyerAC98.ltl:55 | 555.1 / 555.7 | 7601.9 / 6425.9 |
| Parametrised.ltl:27 | 6.7 / 6.5 | 6.8 / 7.0 |
| Parametrised.ltl:45 | 8.9 / 9.0 | 1503.0 / 8.9 |
| Liberouter04.ltl:43 | 8.0 / 8.0 | 1621.8 / 8.4 |

These selected-case medians support a local runtime tradeoff; they do not
establish a full-corpus speedup or a universal performance ordering.

## Interpretation and next work

Keep specialized-first routing as requested. The next size optimizations
should target the specialized outputs themselves, especially the cases
listed above, and distinguish a merely syntactic applicability test from
a construction that exploits all relevant formula constraints. General
SLAA-to-elevator or limit-deterministic Emerson–Lei work remains confined
to residual formulas. These results do not prove that dealternation is
universally better, and do not establish the TACAS complexity bound.

## Reproduction

```sh
python3 tests/build-routing-ablation.py
python3 tests/benchmark-routing-effect.py
python3 tests/time-routing-effect.py
python3 tests/summarize-routing-effect.py
```

The build driver targets this macOS/Spot setup and requires retained
objects from the current checked local build. Keep all sources and
frozen binaries unchanged during measurements. Corpus runs have a
30-second subprocess deadline; native candidate construction and exact
checking inside COLA retain their existing bounds/limitations.
