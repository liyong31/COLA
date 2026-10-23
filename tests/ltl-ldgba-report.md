# LTL → LDGBA → native elevator DELA

The additional route is implemented and opt-in. It uses OWL only to construct the generalized Büchi intermediate, then applies COLA’s existing elevator Emerson–Lei determinisation. The finite-witness construction and direct monitors are preserved. All 908 integrated outputs on 227 distinct OWL collection formulas pass determinism, completeness and independent positive-language equivalence.

## Why this intermediate fits

For a standard LDGBA, partition the states into a nondeterministic prefix N and a closed deterministic region D, with every run staying in N rejecting. Each SCC in N is rejecting weak; each SCC in D is deterministic. The automaton is therefore elevator. This argument depends on the actual partition properties, so the implementation certifies the emitted HOA graph rather than trusting a tool name.

Keep the intermediate acceptance α = ⋀ᵢ Inf(cᵢ). COLA follows its ranked runs and builds disjuncts Fin(discontinuedᵣ) ∧ shiftᵣ(α), alongside the existing weak-component branch. It does not introduce a round-robin Büchi counter or translate through parity. Final generic acceptance simplification is still allowed.

The [TACAS 2017 paper by Esparza, Křetínský, Raskin and Sickert](https://arxiv.org/abs/1701.06103) studies LDBA-to-DPA; Appendix C explicitly uses a generalized deterministic Büchi product. Section 4 deletes ordered runs covered by older runs’ languages; Section 5 discusses polarity and simplification. Its asymptotic bound relies on construction-specific semantic information. Exporting HOA and using COLA’s bounded exact containment does not establish the same bound.

## OWL choices and optimizations

The installed OWL 21.0 macOS amd64 executable runs through Rosetta on this Apple M3. The two explicit frontends are:

```sh
owl ltl2ldgba -t SEJK16 --skip-translation-portfolio -f FORMULA
owl ltl2ldgba -t EKS20 --skip-translation-portfolio -f FORMULA
```

SEJK16 is the asymmetric CAV 2016 LTL frontend used by the TACAS pipeline; EKS20 is a later symmetric alternative. These are different construction families, not two names for the TACAS determiniser. See the official [OWL LDBA package documentation](https://owl.model.in.tum.de/owl-21.0-javadoc/owl/translations/ltl2ldba/package-summary.html).

The inspected [asymmetric LDBA implementation](https://github.com/owl-toolkit/owl/blob/632c2da3ec982cdda340305afb9a3ddf45000491/src/main/java/owl/translations/ltl2ldba/AsymmetricLDBAConstruction.java) avoids commitments for blocked/simple obligations, removes false obligations, retains implication-maximal jump targets, carries safety assumptions, and skips fulfilled breakpoints. Its [DPA implementation](https://github.com/owl-toolkit/owl/blob/632c2da3ec982cdda340305afb9a3ddf45000491/src/main/java/owl/translations/ltl2dpa/AsymmetricDPAConstruction.java) also prunes ranked languages and groups fixpoints by semantic class. Those DPA-stage optimizations do not automatically transfer through unannotated HOA. The inspected source checkout is pinned separately from the measured OWL 21.0 release.

The new route retains OWL formula/acceptance simplification and transition acceptance. It disables OWL’s easy-fragment translation portfolio because COLA already handles those fragments. It tries both algorithms and compares their final completed DELAs, rather than selecting the smallest intermediate. Existing exact SCC-local preorder/union pruning remains; Büchi-specific simulation and stutter shortcuts are disabled here.

## Full integrated comparison

The common external-tool cohort has 222 formulas. External measurements are retained verified references; all four COLA modes were newly run. State totals use completed deterministic automata.

| Configuration | All 227 | Common 222 |
| --- | ---: | ---: |
| COLA default | 1388 | 1036 |
| COLA SLAA polarity portfolio | 1337 | 985 |
| COLA LDGBA candidates | 1350 | 998 |
| COLA combined portfolio | 1336 | 984 |
| Spot | — | 1058 |
| DELAG | — | 1207 |
| LTL3TELA | — | 991 |
| OWL SLM21 | — | 1115 |

COLA LDGBA candidates versus COLA default on 227: **7 smaller, 220 tied, 0 larger**.

COLA combined portfolio versus COLA default on 227: **15 smaller, 212 tied, 0 larger**.

COLA combined portfolio versus COLA SLAA polarity portfolio on 227: **1 smaller, 226 tied, 0 larger**.

Combined versus LTL3TELA on 222: 7 smaller, 215 tied, 0 larger.

DwyerAC98 line 46 is the additional size win over the SLAA portfolio: default COLA 6, SLAA portfolio 4, new LDGBA/combined modes 3. The SEJK16 generalized intermediate has eight states and gives five final states; the EKS20 generalized intermediate has five states and gives three. EKS20 ordinary Büchi gives six final states. This is a concrete reason to retain both generalized constructions.

## Raw whole-formula experiment

This bypasses direct monitors and routing to isolate the intermediate. Each of 227 formulas is tested through both LDGBA algorithms, their ordinary-Büchi controls, and OWL’s `ltl2dpa -t SEJK16_EKRS17` control. The DPA control retains its default translation portfolio. Every successful native boundary passes source/input and input/output equivalence, followed by normalization and independent retained-reference equivalence. Resource failures remain explicit.

| Variant | Verified / 227 | Nondeterministic inputs among successes | Resource outcomes |
| --- | ---: | ---: | --- |
| eks20_ba | 222 | 140 | acceptance-capacity: 3, backend-timeout: 2 |
| eks20_gba | 222 | 140 | acceptance-capacity: 5 |
| owl_tacas_dpa | 225 | 0 | frontend-timeout: 2 |
| sejk16_ba | 223 | 142 | acceptance-capacity: 1, backend-timeout: 2, frontend-timeout: 1 |
| sejk16_gba | 225 | 144 | acceptance-capacity: 1, frontend-timeout: 1 |

All five raw variants succeed on the same 219 formulas:

| Variant | Total complete states on this common cohort |
| --- | ---: |
| eks20_ba | 3157 |
| eks20_gba | 1753 |
| owl_tacas_dpa | 1188 |
| sejk16_ba | 3983 |
| sejk16_gba | 3006 |

SEJK16 generalized versus ordinary Büchi on their 223 joint successes: 19 smaller, 204 tied, 0 larger.

EKS20 generalized versus ordinary Büchi on their 221 joint successes: 29 smaller, 192 tied, 0 larger.

For SomenziB00 line 21, retaining generalized acceptance gives four final states, versus eight after degeneralisation. Generalized acceptance helps, but these raw totals also show why the LDGBA route should complement specialized monitors rather than replace them.

## Targeted optimization controls

Six formulas (Dwyer 45/46/50/55, Parametrised 15, Somenzi 21), two algorithms and five variants give 60 additional boundaries. All successful outputs pass the same checks. Entries below are complete state counts, or the recorded resource outcome.

| Source | Algorithm | Normal LDGBA | No formula simplifier | No acceptance simplifier | OWL portfolio enabled | Full SCC rank allocation |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| SomenziB00.ltl:21 | SEJK16 | 4 | 4 | 4 | 4 | 4 |
| SomenziB00.ltl:21 | EKS20 | 4 | 4 | 4 | 4 | 4 |
| DwyerAC98.ltl:50 | SEJK16 | 17 | 17 | 17 | 17 | 17 |
| DwyerAC98.ltl:50 | EKS20 | acceptance-capacity | acceptance-capacity | acceptance-capacity | acceptance-capacity | acceptance-capacity |
| Parametrised.ltl:15 | SEJK16 | 16 | 16 | 16 | 14 | 16 |
| Parametrised.ltl:15 | EKS20 | 13 | 13 | 13 | 14 | 13 |
| DwyerAC98.ltl:55 | SEJK16 | 19 | 19 | 19 | 19 | 19 |
| DwyerAC98.ltl:55 | EKS20 | acceptance-capacity | acceptance-capacity | acceptance-capacity | acceptance-capacity | acceptance-capacity |
| DwyerAC98.ltl:46 | SEJK16 | 5 | 5 | 5 | 4 | 5 |
| DwyerAC98.ltl:46 | EKS20 | 3 | 3 | 3 | 4 | 3 |
| DwyerAC98.ltl:45 | SEJK16 | 276 | 276 | 276 | 276 | acceptance-capacity |
| DwyerAC98.ltl:45 | EKS20 | 28 | 28 | 28 | 28 | acceptance-capacity |

Disabling either simplifier does not change final sizes in this six-formula grid; this does not establish that simplification is unhelpful generally. OWL’s easy-fragment portfolio helps SEJK16 on Dwyer 46 (five to four) while losing EKS20’s smaller intermediate (three to four). Trying both generalized algorithms still gives the best result here. On Dwyer 45, observed-rank allocation removes an acceptance-capacity failure in both algorithms and gives 276 and 28 checked states respectively.

The new backend option allocates acceptance blocks for the maximum rank width actually observed in each accepting deterministic SCC, after graph exploration. An always-absent rank emits its discontinuation mark on every transition, making its Fin(discontinued) conjunct false. Its entire shifted disjunct and associated marks can be omitted. This option is enabled only at the new LDGBA boundary. A 42-state regression with a 40-state deterministic SCC and only one concurrent run verifies generalized Inf/Inf and mixed Fin/Inf cases against both the input automaton and independent LTL formulas; the output needs at most three acceptance sets. The installed Spot still has a 32-set capacity, so some genuine multi-rank cases remain unsupported.

## Routing, limits and validation

Use `--ldgba-tool=PATH` alone or combine it with `--slaa-tool=PATH --slaa-portfolio`. `--ldgba-construction=SEJK16|EKS20|both` selects the frontend family. Candidates must have generalized Büchi acceptance, a certified elevator graph and the correct language. Native results must be deterministic and language-equivalent. Selection uses completed states, then marks and edges; exact ties keep the established result. GF/FG, recurrence and optional finite witnesses keep priority; failed attempts retain existing fallback.

The first integrated campaign timed out on Dwyer 55 by repeatedly calling OWL throughout profile refinement. A cache now retains both successful and failed residual attempts. The default `--ldgba-attempt-limit=8` bounds external calls across the whole translation, not per profile node. In the controlled reproduction the formula finished in 4.4 seconds, with eight attempts and 18 cache hits; the final full campaign has no integrated timeout. Cache and budget reset per input formula.

Default frontend limits are five seconds per call, 8 MiB output and 256 input states. `--ldgba-timeout-ms` and `--ldgba-state-limit` adjust them; zero time, state or attempt budget skips the route. The attempt budget does not bound native determinisation, parsing or exact language checking. Runtime errors including acceptance capacity abandon an optional candidate. No external sources are vendored.

Integrated LDGBA counters:

- COLA LDGBA candidates, LDGBA attempts: 180.
- COLA LDGBA candidates, LDGBA frontend/construction failures: 4.
- COLA LDGBA candidates, LDGBA rejected candidates: 0.
- COLA LDGBA candidates, LDGBA backend attempts: 171.
- COLA LDGBA candidates, LDGBA validation failures: 0.
- COLA LDGBA candidates, LDGBA candidates: 176.
- COLA LDGBA candidates, LDGBA components: 11.
- COLA LDGBA candidates, LDGBA cache hits: 18.
- COLA LDGBA candidates, LDGBA budget skips: 20.
- COLA combined portfolio, LDGBA attempts: 180.
- COLA combined portfolio, LDGBA frontend/construction failures: 6.
- COLA combined portfolio, LDGBA rejected candidates: 0.
- COLA combined portfolio, LDGBA backend attempts: 169.
- COLA combined portfolio, LDGBA validation failures: 0.
- COLA combined portfolio, LDGBA candidates: 174.
- COLA combined portfolio, LDGBA components: 4.
- COLA combined portfolio, LDGBA cache hits: 18.
- COLA combined portfolio, LDGBA budget skips: 20.

Local `make check` passes five suites: eight historical elevator, 17 specialized-fragment, 47 generic acceptance, 22 SLAA and 24 LDGBA admission/fallback checks. Complete smoke passes. With both optional frontends enabled, all 387 measured finite-witness outputs and 585 budget/bypass checks pass. Single-run timings with concurrent campaigns are diagnostic only; this is a state-count experiment, not a runtime ranking.

## Reproduction

```sh
make -C build-local -j4 check
python3 tests/benchmark-ldgba.py
python3 tests/benchmark-ldgba.py --optimization-probes \
  --artifacts build-local/ldgba-optimizations --csv tests/ltl-ldgba-optimizations.csv
python3 tests/benchmark-slaa.py --tool build-local/external/ltl3tela-master/ltl3tela \
  --modes cola_current cola_slaa_portfolio cola_ldgba cola_combined \
  --artifacts build-local/ldgba-integrated --csv tests/ltl-ldgba-results.csv
python3 tests/summarize-ldgba.py
```

Raw HOA and diagnostics remain under `build-local/ldgba-comparison/`, `build-local/ldgba-optimizations/` and `build-local/ldgba-integrated/`. CSV companion JSON manifests record the actual binaries, native sources, frontend flags and limits. The raw driver has a five-second outer process limit; integrated runs have a 30-second outer limit. No paper-level complexity or minimality claim is made for this integration.
