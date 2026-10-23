# Specialized constructions before generic residual translation

The LTL frontend now returns successful specialized constructions before calling
external SLAA/TELA or LDGBA frontends. This implements the requested priority;
it does not change the finite-witness construction, SLAA acceptance lifting,
colour/weak preprocessors, or SCC-decomposed preorder determiniser.

The order is recurrence/finite-witness monitors and recognized fragments,
Master bundles and X-advice, available syntactic/Boolean decomposition,
checked DBA recognition, and remaining SCC-guided profile decomposition.
Each child repeats the specialized checks in its refined context. Prepared
formulas are checked again for fragments exposed by Delta2 normalization.
Generic frontends run only on the remaining residuals, before the existing
native elevator or formula fallback. Available GF(co-safety), FG(safety),
safety, guarantee, obligation, recurrence and persistence routes retain priority.
A failed or budget-exhausted recognition attempt permits fallback; this is not
an exhaustive decision procedure for all DBA/DCA-recognizable LTL languages.

Both polarity portfolio switches respect this order. They no longer override
successful X-advice or recognized recurrence/persistence constructions.
Construction ablations can explicitly disable the corresponding gates; frontend
admission fixtures do so to continue testing malformed outputs, failures,
non-elevator rejection, semantic checks and acceptance preservation.

## Regressions

Built on the same Apple M3 computer with Apple Clang 17/C++17 and installed
Spot 2.14.1 (32 acceptance sets). All twelve `make check` suites pass, including
22 specialized-priority checks, 27 SLAA admission checks and 31 LDGBA checks.
The priority tests use marker-writing frontends and verify they are never
executed after successful GF/FG, safety/co-safety, finite-witness, X-advice or
checked DBA constructions, with portfolios both disabled and enabled. Each
output is checked independently for language equivalence and determinism.

The complete smoke suite passes. The preserved finite-witness campaign passes
387 equivalent measured outputs plus 585 budget/bypass checks, with no timeout
or acceptance-capacity failure. Its wrapper enables both external frontends,
SLAA polarity and checked LDGBA pruning; see `finite-witness-priority.json`.

## OWL literature corpus

`benchmark-specialized-priority.py` measures all 227 distinct retained OWL
collection formulas in three modes. All enable the optional finite-witness
construction, so the appropriate historical baseline is `cola_reset` in
`ltl-fragment-results.csv`, rather than COLA with that option disabled.
Completed reachable state counts are measured directly, without additional
state minimization. Each result passes determinism, completeness and
independent equivalence against the retained Spot/DELAG reference.

| Mode | Successful formulas | Total complete states | External attempts |
| --- | ---: | ---: | ---: |
| Specialized-first baseline | 227 | 1460 | 0 |
| SLAA residual + colour/weak preprocessing | 227 | 1460 | 7 |
| Positive SEJK16 LDGBA residual + annotation/pruning | 227 | 1460 | 7 |

All 681 outputs pass; every per-formula state count ties the specialized-first
baseline. All 227 baseline counts also reproduce the retained historical
finite-witness-enabled baseline. This is a priority/coverage change with no
observed size gain on this corpus.

Only Dwyer 50 and Dwyer 55 reach either external frontend: one call for Dwyer50
and six refined residual calls for Dwyer55. Final outputs have 12 and 13 complete
states, respectively. All other 225 formulas avoid the external frontends.
These numbers do not show that a generic route is unnecessary for arbitrary
LTL: the corpus is dominated by fragments handled by the specialized routes.
They also do not establish a new elevator-aware dealternation theorem.

An initial ordering still allowed generic candidates before SCC-guided profile
decomposition. It produced 1462 LDGBA-mode states, including a two-state increase
on Dwyer55 after composition. Moving profile decomposition ahead of those calls
restored every baseline count and reduced attempts from nine to seven. The
initial controls are retained locally in
`build-local/specialized-priority-before-profile-order.{csv,json}`; only the
final, source-hashed campaign is published as `specialized-priority-results.*`.

The earlier unrestricted portfolio totals remain historical results under a
different routing policy. They must not be presented as current strict-priority
results, nor as measurements of a single primitive algorithm. The separate
[LTL3TELA pipeline audit](ltl3tela-pipeline-report.md) documents its nested
selections and Spot postprocessing.

## Reproduction

```sh
make -C build-local -j4
make -C build-local check -j4
LTLD="$PWD/build-local/ltl2dela" sh tests/ltl2dela-smoke.sh
python3 tests/benchmark-specialized-priority.py
python3 tests/finite-witness.py --ltld build-local/ltld-owl-cross \
  --repeats 1 --stress 10 --random-cases 50 \
  --csv tests/finite-witness-priority.csv
```

The wrapper source is embedded in `finite-witness-priority.json`. Benchmark
manifests record the base commit, exact commands/options and measured hashes;
source/binary hashes are checked before and after the 681-output campaign.
Thirty-second subprocess deadlines and two workers apply to that campaign;
concurrent single-run timings are diagnostics, not runtime rankings. Default
frontend state/time limits and the whole-formula LDGBA call budget remain.
