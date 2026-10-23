# Colour-elevator priorities: implementation and experiments

Work follows `idea.md` on the dedicated `colour-elevator` branch, retaining the completed SLAA/LDGBA implementation and existing preorder backend. Spot has **not** been reinstalled: all these results use its existing 32-acceptance-set configuration. The first working milestone is `865274b` (local checkpoint `fefb4f6`; [priority A report](colour-choice-report.md)).

## Implemented in priority order

1. **Colour-choice elimination.** State-preserving recognition and rewriting of internally target-deterministic SCCs, including mixed Fin/Inf acceptance, bounded clause expansion, BDD guard partitioning, SCC-local selectors and independent equivalence. The proof and counterexamples are in [the manuscript supplement](../research/colour-elevator.tex).
2. **Colour-elevator preprocessing.** A separate bounded conversion turns unsupported positive Fin-only local SCCs into rejecting prefix components and accepting weak copies. It can add states. It uses the standard last-bad-event commitment idea, and does not assume the backend directly supports arbitrary co-Büchi SCCs.
3. **Actual SLAA certification.** A syntax check for the specified pre-merging expansion and a graph certificate for self-only retention plus strictly descending discharge. Bounded canonical configuration enumeration checks the singleton-SCC theorem on actual LTL3TELA outputs. This does not implement a new alternating acceptance lifting.
4. **Late global monitors.** Early/late product experiments validate the existing Boolean-composition route. A separate checked C++ acceptance-parametric reference API supports mixed acceptance by bounded monitor-profile instantiation, sharing monitor colours once in the late product. Its larger product bound is stated explicitly.
5. **Pruning.** Existing bounded exact SCC-local inclusion/union pruning is reused. No new aggressive pruning or deletion of older runs under unknown monitor facts is enabled.

## Raw TELA eligibility

There are 531 cases: 227 positive literature intermediates, 300 retained shape/polarity variants, three colour-choice examples and one co-Büchi example. Two historical frontend outputs are unavailable. All other 529 preprocessing results pass independent equivalence. The native controls use the same SCC pruning and observed-rank settings. The CSV additionally compares global and SCC-local colour allocation on each changed intermediate. Unchanged raw inputs reuse the baseline.

| Family | Before: native successes | After: native successes | Remaining non-elevator | Native capacity |
| --- | ---: | ---: | ---: | ---: |
| literature | 170 | 185 | 40 | 0 |
| shape | 151 | 151 | 149 | 0 |
| targeted | 0 | 4 | 0 | 0 |

The colour-choice pass makes twelve literature inputs eligible; twelve finish with SCC-local packing (eleven without). Weakification recovers three more (Parametrised 43/44/45), adding 4/12/32 intermediate states and producing checked 6/23/90-state DELAs. Thus positive literature native successes increase from 170 to **185**. SCC-local packing recovers Parametrised 36 as a checked one-state result where global colour blocks exceed capacity. Hardness 8 safely retains its input when the equivalence checker exceeds capacity. The 300 shape variants still contain genuine target nondeterminism with recurring good obligations; these two transformations do not resolve those SCCs.

A diagnostic-driver bug shadowed the weakification flag with an SCC counter in the first scan. The flag/counter are now separate; the co-Büchi example and production frontend fixtures cover the route. Only corrected measurements are reported here.

## SCC-local acceptance allocation

The new modes additionally restrict each stable rank’s acceptance to its own deterministic SCC: absent colours are finite, colours on every internal edge are infinite, and remaining indices are packed before marks are materialised. The rank graph and discontinuation semantics remain unchanged. Allocation becomes `sum_C r_C * (k_C + 1) + weak`, rather than copying every global input colour into every rank. Existing modes keep their original allocation. This principle is already used by [Kofola’s DAC implementation](https://github.com/VeriFIT/kofola/blob/14b657bc567442722285743fbf1976af43998334/src/determinization/determinize_alg_dac.cpp) and is not claimed as new determinisation. The same Parametrised 36 intermediate fails with global blocks and succeeds with local blocks, producing one state and 15 colours under the unchanged 32-set Spot build. All 94 generic acceptance fixtures exercise local allocation off/on, including mixed Fin/Inf, disappearing ranks and a forty-state deterministic SCC.

## Integrated comparison

All 681 newly run outputs are deterministic, complete and equivalent to retained independent positive-language references. Reference Spot/DELAG/LTL3TELA/OWL outputs are reused, not newly timed.

| Configuration | States, all 227 | States, common 222 | Colours, common 222 |
| --- | ---: | ---: | ---: |
| cola_combined | 1336 | 984 | 338 |
| cola_combined_colour | 1336 | 984 | 338 |
| cola_colour_elevator | 1336 | 984 | 338 |

All 227 final state counts tie the established combined portfolio. Its common-222 total remains **984**, versus retained LTL3TELA 991. The new eligibility gains do not yet yield end-to-end state savings: direct monitors or the other polarity already handle these examples well. Do not present preprocessing coverage as a final-size win.

Use `--slaa-tool=PATH --slaa-portfolio --colour-elevator` (optionally also `--ldgba-tool=PATH`). `--colour-choice` enables only the state-preserving pass. Weakification defaults: 512 total states, 64 clauses, 16384 edges, and the installed colour capacity; `--cobuchi-state-limit=N` adjusts its state budget. Library budgets and equivalence gates abandon unsupported candidates. Existing direct monitors and defaults remain unchanged.

## Pure-persistence result and simplification controls

A certified transition retains only its source, or discharges to strictly smaller states. The highest state taking a strict transition disappears, so the configuration characteristic vector strictly decreases lexicographically. This proves singleton SCCs for the canonical, unquotiented configuration graph. Marks and alternating acceptance lifting are separate concerns.

- literature: 103/227 graphs certify pure persistence; no certified enumerated configuration graph has a non-singleton SCC.
- shape: 42/300 graphs certify pure persistence; no certified enumerated configuration graph has a non-singleton SCC.

All 543 SLAA probes finish; 1 configuration enumerations record a state/work budget instead of a complete graph. The dataset includes 16 explicit preservation controls. Dwyer 11 and 13 meet the sufficient source syntax but LTL3TELA expands nested W into retaining/spawning G structures. Disabling simplification or U/G merging does not restore that certificate. Their enumerated graphs nevertheless have singleton SCCs: the certificate is sufficient, not necessary. `F(Ga & X(Fb))` preserves it in all four controls. Conversely default U/G merging turns `GF a` into a certified one-state SLAA; disabling merging yields recurring spawn and a non-singleton configuration SCC. Blanket disabling of merging would lose a useful optimisation.

## Late-composition controls

The test uses `F(a & XG b)` as the nondeterministic skeleton and one global deterministic finite-history monitor. All 28 outputs (seven depths, early/late, full-history/minimised monitor) pass independent LTL equivalence. Every late raw product satisfies `|Preorder(B)| × |D|`; monitor colours appear once.

| Depth 6 monitor | Monitor states | Early backend input | Late backend input | Final states, both | Early / late construction ms |
| --- | ---: | ---: | ---: | ---: | ---: |
| full-history | 64 | 192 | 3 | 18 | 28.714 / 1.201 |
| minimised | 7 | 21 | 3 | 18 | 1.588 / 0.661 |

Minimising the monitor is an essential control: the window predicate admits a seven-state streak monitor, while the deliberately generic history representation has 64 states. Much of the large raw timing gap disappears after that optimisation. Timings are single-run diagnostics, not speedup claims. Fresh-process peak RSS is retained in the CSV, measured using macOS `time -l`; source-oracle translation and equivalence are outside construction timing and measured processes.

## Acceptance-parametric reference API

`determinise_with_global_monitors()` in [late_monitor.hpp](../src/late_monitor.hpp) accepts a skeleton, complete deterministic global monitors and a mixed Fin/Inf formula. For each bounded valuation of monitor infinite-colour predicates, it substitutes those constants, certifies the resulting elevator instance and invokes the existing determiniser with fixed acceptance. The deterministic profile results are then synchronised with each monitor once; the final acceptance selects the matching monitor profile. An independent early product verifies the result.

The default profile budget is eight. This reference supports arbitrary positive Boolean mixed acceptance, including rejecting-run cases that cannot be implemented by complementing the deterministic language of the original skeleton. It has **26 checks**, including all 16 two-variable acceptance functions against an independent LTL oracle, multiple monitors, unsupported profiles and budgets.

**Limit:** its state bound contains a product of the profile determinisation sizes. It is not the desired single shared rank graph, is not enabled in the LTL frontend, and does not justify acceptance-uniform pruning. The paper states the larger bound and the exact remaining proof obligation. Boolean late composition is already supported; run-local restarted monitors remain ineligible for global sharing.

## Validation and remaining gaps

- All ten local suites pass: 3709 colour-choice, 214 co-Büchi, seven pure-persistence, three late-product, 26 parametric, and 94 generic acceptance fixtures with local packing on/off, and the historical elevator/fragment/27 SLAA/24 LDGBA fixtures.
- All 387 finite-witness measurements and 585 budget/bypass checks pass with the complete colour-elevator portfolio enabled; full smoke passes.
- Manuscript proofs and measured claims are separate from novelty claims. Spot already merges Fin-less equal-guard transitions; the co-Büchi commitment construction is standard. No unrestricted LTL complexity improvement, arbitrary-DELA optimality or uniform size improvement is claimed.
- Custom SLAA recurrent-spawn elimination, a single parametric rank graph with uniform pruning, and an exported shared acceptance-circuit representation remain research gaps. Existing tests use ordinary Spot acceptance formulas; an implementation DAG size is therefore not reported as though such a DAG were present.

## Reproduction

```sh
make -C build-local -j4 check
python3 tests/benchmark-colour-choice.py --weakify \
  --artifacts build-local/colour-weak --csv tests/colour-weak-results.csv
python3 tests/benchmark-slaa.py --tool build-local/external/ltl3tela-master/ltl3tela \
  --modes cola_combined cola_combined_colour cola_colour_elevator \
  --artifacts build-local/colour-weak-integrated --csv tests/colour-weak-integrated-results.csv
python3 tests/probe-pure-persistence.py
python3 tests/benchmark-late-monitors.py
python3 tests/summarize-colour-elevator.py
```

Companion JSON files identify measured source and binary hashes, limits and artifact directories. Priority-A data retain their original milestone provenance. The new modes remain opt-in.
