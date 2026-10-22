# LDGBA pruning: retained-input experiment

All new runs replay the same retained OWL HOA inputs. Frontend time is zero
by construction; unavailable retained inputs are not new frontend timeouts.
Each completed result passes source-LTL equivalence, native equivalence,
determinism, completeness and equivalence to the retained independent reference.
Five seconds per process, two workers; timings are diagnostic.

Cache means the existing 8-state SCC / 4-run prefix / 64-query policy with
memoised exact union proofs. Packed adds SCC-local colour restriction.
Wider adds 256-state SCC / full admitted prefix / 512-query limits.
The shared query budget also expands the reserved static semantic-order
budget; this control measures their combined effect, not union pruning alone.
All deletions still require exact language inclusion against older retained runs.

| Change | Variant | Paired successes | Smaller / tied / larger | States before / after |
| --- | --- | ---: | ---: | ---: |
| raw-results → cache | sejk16_gba | 225 | 6 / 219 / 0 | 3487 / 3273 |
| raw-results → cache | eks20_gba | 222 | 2 / 220 / 0 | 2019 / 1983 |
| raw-results → cache | sejk16_ba | 223 | 11 / 212 / 0 | 4437 / 3379 |
| raw-results → cache | eks20_ba | 222 | 7 / 215 / 0 | 3608 / 2689 |
| cache → packed | sejk16_gba | 225 | 0 / 225 / 0 | 3273 / 3273 |
| cache → packed | eks20_gba | 223 | 0 / 223 / 0 | 2055 / 2055 |
| cache → packed | sejk16_ba | 224 | 0 / 224 / 0 | 3493 / 3493 |
| cache → packed | eks20_ba | 224 | 0 / 224 / 0 | 3072 / 3072 |
| packed → packed-pruning | sejk16_gba | 225 | 6 / 219 / 0 | 3273 / 1753 |
| packed → packed-pruning | eks20_gba | 224 | 4 / 220 / 0 | 2164 / 1998 |
| packed → packed-pruning | sejk16_ba | 224 | 6 / 218 / 0 | 3493 / 1973 |
| packed → packed-pruning | eks20_ba | 224 | 6 / 218 / 0 | 3072 / 2710 |

## Final status and fixed-cohort comparison

| Variant | OK | Capacity | Backend timeout | Input unavailable |
| --- | ---: | ---: | ---: | ---: |
| sejk16_gba | 225 | 1 | 0 | 1 |
| eks20_gba | 224 | 3 | 0 | 0 |
| sejk16_ba | 224 | 0 | 2 | 1 |
| eks20_ba | 224 | 1 | 2 | 0 |
| owl_tacas_dpa | 225 | 0 | 0 | 2 |

Fixed original five-way common cohort: **219 formulas**.

| Variant | Original states | Optimised states |
| --- | ---: | ---: |
| sejk16_gba | 3006 | 1556 |
| eks20_gba | 1753 | 1551 |
| sejk16_ba | 3983 | 1689 |
| eks20_ba | 3157 | 1876 |
| owl_tacas_dpa | 1188 | 1188 |

Recovered original failures:

- DwyerAC98.ltl:50 eks20_gba: acceptance-capacity → 72 states.
- Parametrised.ltl:39 eks20_ba: acceptance-capacity → 114 states.
- Parametrised.ltl:39 sejk16_ba: acceptance-capacity → 114 states.
- DwyerAC98.ltl:55 eks20_ba: acceptance-capacity → 269 states.
- DwyerAC98.ltl:55 eks20_gba: acceptance-capacity → 109 states.

## Integrated portfolio

| Control | Mode | Smaller / tied / larger | Original total | New total |
| --- | --- | ---: | ---: | ---: |
| optimized | cola_ldgba | 0 / 227 / 0 | 1350 | 1350 |
| optimized | cola_combined | 0 / 227 / 0 | 1336 | 1336 |
| polarity | cola_ldgba | 10 / 217 / 0 | 1350 | 1337 |
| polarity | cola_combined | 0 / 227 / 0 | 1336 | 1336 |

The polarity control adds --ldgba-portfolio to --ldgba-pruning.
Positive and negative frontend calls share the eight-attempt budget.

- DwyerAC98.ltl:51 cola_ldgba: 5 → 4 states.
- Liberouter04.ltl:40 cola_ldgba: 6 → 5 states.
- Liberouter04.ltl:41 cola_ldgba: 8 → 7 states.
- Liberouter04.ltl:42 cola_ldgba: 8 → 7 states.
- Liberouter04.ltl:43 cola_ldgba: 10 → 9 states.
- Liberouter04.ltl:44 cola_ldgba: 9 → 7 states.
- Parametrised.ltl:15 cola_ldgba: 13 → 10 states.
- Pelanek07.ltl:7 cola_ldgba: 6 → 5 states.
- SomenziB00.ltl:20 cola_ldgba: 7 → 6 states.
- SomenziB00.ltl:23 cola_ldgba: 5 → 4 states.

The additional 227-formula default-mode check passes and reproduces
every historical default state count (1388 total).


## Complexity: what this implementation establishes

TACAS 2017 §4.1–4.2 requires initial determinism and a singly exponential
language basis, not merely limit determinism. Removing every covered younger
run bounds the ranking length by the basis size plus one. Together with the
double-exponential LDGBA size this bounds ordered configurations doubly
exponentially. Generalized Büchi marks can remain on persistent runs; they
need not be replaced by a Büchi counter for this counting argument.

Our bounded SCC-local exact checks are safe engineering approximations.
The installed HOA interface carries neither certified state-language formulas
nor their basis. Exhausted budgets keep runs, SCC ranks are independent,
and elevator admission does not certify initial determinism. Consequently
**the TACAS double-exponential LTL bound is not yet established for this route**.
Observed rank widths and a larger fixed query budget do not repair that proof.

The next architectural step is an annotated LDGBA boundary exposing each
state language and basis support, a certified deterministic prefix and closed
accepting region, followed by complete oldest-first basis coverage pruning
across that region. Its interaction with SCC rank resets, weak accepting
components and original Emerson–Lei acceptance needs a proof. OWL language()
annotations are suitable candidates; match_states() overapproximations and
unverified HOA state-name strings are not sufficient deletion certificates.

OWL additionally uses fixpoint availability, safety/liveness partitions,
blocking and safety-progress rotation. Those rules depend on annotations;
copying them onto an arbitrary elevator automaton would be unjustified.

## Reproduction

```sh
python3 tests/benchmark-ldgba.py --reuse-inputs build-local/ldgba-comparison \
  --local-colours --ldgba-pruning --artifacts build-local/ldgba-packed-pruning \
  --csv tests/ltl-ldgba-packed-pruning.csv
python3 tests/benchmark-slaa.py --tool PATH_TO_LTL3TELA --ldgba-pruning \
  --modes cola_ldgba cola_combined --artifacts build-local/ldgba-optimized-integrated \
  --csv tests/ltl-ldgba-optimized-integrated.csv
python3 tests/summarize-ldgba-pruning.py
```

For cache-only omit both raw flags; for packed-only omit --ldgba-pruning.
Repeat the integrated command with --ldgba-portfolio and distinct output
paths to reproduce the polarity control.
Use distinct artifact/CSV paths for each ablation. JSON manifests identify
the measured sources, binaries and replay inputs; the original raw campaign
keeps its historical provenance.

[TACAS 2017 full paper](https://arxiv.org/html/1701.06103v1),
[OWL ranking source](https://github.com/owl-toolkit/owl/blob/632c2da3ec982cdda340305afb9a3ddf45000491/src/main/java/owl/translations/ltl2dpa/AsymmetricDPAConstruction.java).
