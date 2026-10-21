# Finite-witness local validation and benchmarks

21 October 2026; continuation of `finite-witness-reset` from `fbaee65`.
The existing finite-witness construction is preserved and remains opt-in.

## Machine and method

Built on this computer: Apple M3 MacBook Air, 8 cores, 16 GB RAM,
macOS 26.6.2 arm64; Apple Clang 17.0.0, `-g -O2 -std=c++17`;
the existing native Spot 2.14.1 installation in `/usr/local`, with its
32-acceptance-set limit. No cloud objects or executables were reused.

An existing GNU-only `bits/stdc++.h` include was replaced by standard C++
headers to compile with Apple Clang. An out-of-source build avoids the
case-insensitive collision between the `cola` executable and the user's
nested `COLA/` checkout. That nested checkout was left untouched.

```sh
autoreconf -i
mkdir -p build-local
cd build-local
../configure --with-spot=/usr/local lt_cv_sys_max_cmd_len=32768
make -j4
make check
cd ..
LTLD=./build-local/ltl2dela sh tests/ltl2dela-smoke.sh

# Bypass the libtool shell launcher for comparable process timings.
export DYLD_LIBRARY_PATH="$PWD/build-local/src/.libs"
python3 tests/finite-witness.py --ltld ./build-local/.libs/ltl2dela \
  --repeats 5 --stress 10 --csv tests/finite-witness-results.csv
python3 tests/finite-witness.py --ltld ./build-local/.libs/ltl2dela \
  --repeats 1 --random-cases 50 --csv tests/finite-witness-random-results.csv
python3 tests/finite-witness.py --ltld ./build-local/.libs/ltl2dela \
  --repeats 5 --stress 10 --state-limit 4096 \
  --csv tests/finite-witness-large-results.csv
```

The configure cache setting avoids a sandbox-restricted `sysctl` probe of
the maximum command length; 32768 is a conservative value. When switching
from an already configured source-tree build, first run `make distclean`
(override `bin_PROGRAMS=ltl2dela` if the nested `COLA/` directory exists).

Measurements are fresh-process medians, including dynamic loading, parsing,
translation and HOA serialization. Each mode runs sequentially; there are
no concurrent benchmark campaigns. Routing diagnostics, determinism checks
and equivalence checks are outside the timings. Spot uses
`ltl2tgba --deterministic --generic`. All tools use their normal output
post-processing; edges are symbolic HOA edges, not alphabet valuations.
About 5 ms of startup dominates small cases. Sub-millisecond differences
and single-repeat random timings should not be interpreted as speed gains.

## Regression results

- `make check`: passed, including eight raw elevator acceptance fixtures.
- Complete `tests/ltl2dela-smoke.sh`: passed, including X-advice and elevator
  reference-language checks.
- All 17 fixed cases: baseline, reset and independent Spot outputs passed
  determinism and language equivalence checks.
- Seed 20261020: 50 generated co-safety kernels and their 50 persistence
  duals passed, in addition to the 17 fixed cases. No timeouts or capacity
  failures in this campaign (351 measured outputs).
  Only eight of the 100 generated formula/dual outputs actually complete a
  reset monitor; many simplify or use earlier fast paths. This limits what
  the random sample establishes about the new construction specifically.
- Each fixed/random formula also passed independent equivalence and
  determinism checks with state budgets 0 and 1, work budgets 0 and 1,
  and with recurrence fast paths disabled: 585 additional outputs in the
  random campaign alone.
- Routing checks require actual reset/dual use and retention of the flat
  fast path. Tiny-budget checks require at least one abort and zero completed
  monitors. Existing profile exploration can retry an attempt, so requiring
  exactly one abort was incorrect and has been fixed.

CSV `ok` means that determinism and independent equivalence both passed.
`translated` is an intermediate checkpoint, never a completed equivalence
result. Unexpected command failures and required-case timeouts fail the
driver. Scaling translation timeouts and Spot acceptance-capacity errors
are recorded explicitly and do not count as successful outputs.
The default campaign has 79 successful outputs, seven capacity failures and
one timeout; the 4096-state campaign has 81 successes, five capacity failures
and one timeout. No completed reset output has more states than the baseline
on any case where both finish in these three campaigns.

## Selected default-budget measurements

Cells show **states / edges / median milliseconds**. Full formulas, colours
and routing counts are in [the default CSV](finite-witness-results.csv).

| Case | Existing COLA | Reset enabled | Independent Spot |
| --- | ---: | ---: | ---: |
| nested X | 4 / 10 / 5.420 | 4 / 10 / 5.072 | 4 / 12 / 4.947 |
| nested U | 8 / 62 / 8.453 | 4 / 18 / 5.238 | 4 / 24 / 5.164 |
| nested M | 62 / 1094 / 30.046 | 5 / 25 / 5.364 | 5 / 35 / 5.292 |
| correlated | 10 / 78 / 8.520 | 4 / 16 / 5.468 | 4 / 18 / 5.182 |
| mixed | 561 / 14021 / 876.180 | 13 / 82 / 5.835 | 13 / 94 / 6.029 |
| dual nested | 6 / 38 / 6.054 | 4 / 15 / 5.764 | 4 / 18 / 5.333 |
| stable guard | 2 / 19 / 7.386 | 2 / 19 / 7.380 | 25 / 227 / 7.780 |
| until width 3 | 80 / 1202 / 45.398 | 8 / 42 / 5.502 | 8 / 54 / 5.856 |
| until width 4 | 1254 / 36941 / 6575.390 | 16 / 112 / 6.676 | 16 / 162 / 9.254 |
| until width 5 | timeout (30 s) | 32 / 306 / 12.457 | 32 / 486 / 60.272 |

The mixed formula is `GF(a & X((b U c) & (d M (e | F f))))`.
The until family is `GF(t & (g0 U h0) & ... & (g{k-1} U h{k-1}))`.
The stable-guard case completes **zero** finite-witness monitors: its small
output is an existing structural result, not a gain from the reset path.
Likewise the flat and Boolean cases retain the established fast paths.

## Growth, budgets and limits

For `GF(a & X^k b)`, the completed reset outputs have `2^k` states and
`5 * 2^(k-1)` symbolic edges; independent Spot has the same states and
`3 * 2^k` edges. The default 256-state budget completes through `k=8`.
At `k=9,10`, it abandons the reset construction and the existing translator
then exceeds this Spot build's 32-acceptance-set capacity. The CSV records
zero completed monitors and five aborted attempts, not reset-produced output.
The baseline itself exceeds the same capacity from `k=6` onward.

Increasing the state budget to 4096 permits the 512-state and 1024-state
reset monitors; the transition-extraction work budget remains 16384. The
increased-budget measurements and routing counts are retained in
[the larger-budget CSV](finite-witness-large-results.csv).

| X depth, budget 4096 | Reset states / edges / ms | Spot states / edges / ms |
| --- | ---: | ---: |
| 9 | 512 / 1280 / 12.273 | 512 / 1536 / 11.264 |
| 10 | 1024 / 2560 / 25.877 | 1024 / 3072 / 26.114 |

Both rows have one completed reset monitor, zero duals and zero aborts.

The correlated-until reset family also doubles in states with each added
obligation, reaching 32 states at width five. It has much less growth than
the existing pipeline in these measurements, but the DFA construction is
not generally polynomial. State/work budgets do not bound the memory or
time inside a single Spot derivative call. Safe language fallback does not
guarantee that the subsequent translator can finish within its own resource
limits. `--stats` now prints routing counters on translation errors as well
as on successful output, so that distinction remains visible.

## Interpretation

Use the optional path for nested, correlated co-safety recurrence kernels
and their safety-persistence duals when compact deterministic monitors are
useful. The mixed and wider-until cases provide substantial gains over the
existing COLA path. Simple kernels have essentially equal costs, and reset
is slightly slower than direct Spot on several X-window examples. The
structural COLA pipeline can still be preferable: the stable-guard example
has two states versus Spot's 25, without using a reset monitor.

Direct Spot is a useful alternative for generic inputs and when a reset
attempt exhausts its budget; it completes every reference in these families.
Increase the reset state budget only when accepting its exponential growth
is appropriate. Keep the feature off by default: these measurements cover
selected families and a small seeded grammar, not arbitrary LTL or all Spot
versions. Small startup-dominated timing differences provide no reason to
change the default.
