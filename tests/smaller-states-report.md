# Smaller outputs before strict routing priority

The default policy now compares validated alternatives for broad recognized
fragments, checked DBA candidates and X-advice. Dedicated recurrence, GF/FG
and optional finite-witness monitors remain first. A complete one-state output
skips comparison because no complete reachable automaton can have fewer states.
`--specialized-first` preserves the previous strict early-return policy.

Candidate ordering uses complete reachable states, then acceptance sets and
edges. Exact ties retain the incumbent. All candidates use the existing input
and output language checks. Budgets, per-formula LDGBA caching, independent
SCC determinisation, ranked runs and shifted original acceptance are unchanged.
External tools are still opt-in; without configured tools the output is unchanged.

## Matched OWL collection results

All 908 outputs across 227 formulas and four configurations pass independent
language equivalence, determinism and completeness, without timeout. Results
use complete reachable states before extra minimization, matching the previous
routing experiment. Frozen executable/library copies and source/tool hashes
are checked before and after the campaign.

| Configuration | Complete states | Frontend calls |
| --- | ---: | ---: |
| default | 1388 | 0 |
| strict_portfolio | 1387 | 26 |
| portfolio | 1336 | 1084 |
| finite_witness_portfolio | 1408 | 1084 |

The historical portfolio totals 1336 states; strict priority totals 1387;
the new size-oriented policy totals **1336**. All 227 per-formula sizes
match or improve on the historical portfolio. The previous strict-policy
regressions are recovered. This compares policies with multiple configured
constructions; it is not a claim about the best primitive algorithm.

Concrete regressions cover Dwyer45 (17 to six states) and the X-advice case
Pelanek7 (nine to five), including strict-mode and disabled-frontend fallbacks.
Liberouter36 recovers 50 to 34 in the full campaign. Dedicated GF/FG routes
continue to make no external calls under either policy.

The optional finite-witness configuration is reported separately: a specialized
construction is not a global state-minimality certificate. For this corpus,
leave that option off for the smaller aggregate; it remains useful on other
finite-witness families. No global minimality or universal size bound is claimed.

## Verification

All 13 `make check` suites pass, including ten new smaller-candidate/direct-monitor
checks and the 22 strict-priority checks now run with `--specialized-first`.
The complete smoke suite passes. The preserved finite-witness campaign passes
387 equivalent outputs and 585 budget/bypass checks, with no timeout or installed
acceptance-capacity failure. Source and binary provenance is retained in the
JSON manifests. Corpus timings use two workers and are diagnostic, not rankings.

## Reproduction

Build and check normally, then freeze the measured runtime artifacts:

```sh
make -C build-local -j4
make -C build-local check -j4
mkdir -p build-local/smaller-states
cp build-local/.libs/ltl2dela build-local/smaller-states/ltl2dela
cp build-local/src/.libs/libcola.0.dylib build-local/smaller-states/libcola.0.dylib
python3 tests/benchmark-smaller-states.py
```

For the size-oriented configured portfolio:

```sh
./build-local/ltl2dela \
  --slaa-tool="$PWD/build-local/external/ltl3tela-master/ltl3tela" \
  --slaa-portfolio --colour-elevator \
  --ldgba-tool="$PWD/build-local/external/owl-21.0/bin/owl" \
  --ldgba-pruning --ldgba-portfolio --ldgba-cross-scc \
  -f 'G(a -> F b)'
```

Add `--specialized-first` to prioritize fewer external attempts. The external
programs, deadline/state limits and native/checker limitations are unchanged.
