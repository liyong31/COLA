# Why the translators differ, and the fragment-routing changes

21 October 2026. This follows the [original literature experiment](ltl-size-comparison.md).
The old measurements remain unchanged as a historical baseline. New COLA
measurements are in [ltl-fragment-results.csv](ltl-fragment-results.csv), and
[the updated comparison](ltl-fragment-summary.md) combines them with the four
unchanged reference tools' retained outputs.

## The two shared timeouts are caused by the translation route

Spot and both COLA modes timed out on `Parametrised-Hardness.ltl` lines 2
and 4; DELAG and OWL did not. The formulas combine global safety constraints
with temporal obligations. Those constraints rule out many otherwise possible
histories. Splitting them into separate automata loses that pruning during
construction; composing the results afterwards cannot recover the resources
already spent on unconstrained components.

Live macOS stack samples of all four original Spot/COLA processes show
`spot::tgba_powerset` and its bit-vector/state-set operations. Early physical
footprint snapshots range from 368 MB to 2.2 GB. These are short samples,
not measurements of whole-run peak memory. Full samples are retained under
`build-local/size-diagnosis/`; selected observations and ablations are in
[ltl-timeout-probes.json](ltl-timeout-probes.json).

| Hardness line | Low-level NBA states / edges | Default Spot, original limit | Spot with `ltl-split=0`, complete states | Updated COLA, complete states |
| --- | ---: | --- | ---: | ---: |
| 2 | 26 / 59 | timeout at 30 s | 83 | 83 |
| 4 | 45 / 97 | timeout at 30 s | 148 | 148 |

The NBAs took about 10 ms to produce in short probes. Standalone Spot with
`-D -G -x ltl-split=0` finished in approximately 20 and 77 ms; updated COLA
took approximately 40 and 77 ms. These are single-run diagnostic times
including startup; the significant observation is completion versus the
original 30-second timeouts, not the small timing differences.

Simply selecting Low optimization, or disabling `wdba-minimize`, did not
reliably resolve the short probes. Preserving the full constrained formula
did. Spot's source partitions formulas into obligation/suspendable/other
components before translating them, and its WDBA minimization can explore
an unbounded intermediate powerset under deterministic preference. See the
[Spot 2.14.1 translation source](https://gitlab.lre.epita.fr/spot/spot/-/blob/spot-2-14-1/spot/twaalgos/translate.cc)
and [documented options](https://spot.lre.epita.fr/man/spot-x.7.html).
This is an avoidable intermediate-construction blow-up, not evidence that
the input intrinsically needs a huge deterministic automaton.

## LTL3TELA's size advantage comes mainly from polarity and composition

All eleven cases where LTL3TELA beats default Spot were rerun with its
component options disabled in turn. There are 77 ablation outputs; all passed
determinism and equivalence against the retained Spot reference.

- Disabling the negated-formula/complement alternative worsens **eight** cases.
- Disabling compositional splitting worsens **two** cases, with one overlap
  with the polarity-dependent cases.
- Two remaining cases select the basic SLAA-based translation.
- Disabling U/G merging while also disabling the Spot/SPOTELA alternatives
  retains all eleven winning state counts. Merging is therefore not necessary
  for these particular wins.
- Using the SLAA engine without Spot/SPOTELA alternatives also retains all
  eleven winning state counts. The results cannot be attributed merely to
  wrapping the same default Spot command.

The default winner labels identify seven whole-formula `neg` results, two
whole-formula `basic` results and two compositional results. One compositional
result uses a `spotneg` component. LTL3TELA compares positive and complemented
negative candidates, and constructs products with suspension for eligible
components. See its pinned
[translation and product implementation](https://github.com/jurajmajor/ltl3tela/blob/02092adca492678407bd74b5d3bbe103d8c2b400/nondeterministic.cpp).

The exact option changes, formulas, sizes and winner labels are retained in
[ltl-size-ablations.csv](ltl-size-ablations.csv). Reproduce them with
`python3 tests/diagnose-ltl-sizes.py` after preparing the reference artifacts
from the original experiment.

## Implemented routing policy

The existing finite-witness construction and its opt-in flag are preserved.
The changes are in [ltl2dela.cpp](../src/ltl2dela.cpp):

1. **Recognize Boolean GF/FG combinations before ordinary simplification.**
   Basic simplification can turn `(FG a & GF b)` into `G(FG a & F b)`, hiding
   the one-state fragment. Boolean combinations of GF/FG over propositional
   predicates now use Spot's specialized compositional translation together,
   before heuristic profile commitments. The 84-state example becomes one state.
2. **Use specialized GF/FG endpoints.** Existing exact recurrence rewrites
   and flat-until monitors keep priority. The optional finite-witness path
   remains next when enabled. Remaining `GF(co-safety)` and `FG(safety)`
   kernels use Spot's dedicated DBA and DCA constructions, respectively.
3. **Try checked DBA constructions.** Syntactic recurrence is a sufficient
   recognition rule, not a complete test. A small BA also permits a bounded
   weak-DBA attempt and a bounded transition-Buchi determinization with exact
   language checking, including residuals outside that syntactic fragment.
   The default input cap is 64 BA states, the constructed graph/product limit
   is 512 states, and the TBA cycle limit is 4096 per SCC. Failure keeps the
   original language and resumes the general route. These are practical
   construction limits, not hard time/memory bounds on BA generation or
   equivalence checking.
4. **Select, rather than force, a DBA.** A DBA-recognizable language can have
   a smaller Emerson-Lei presentation. Known-fragment DBA candidates compete
   with the specialized generic result by complete states, acceptance sets,
   then edges. Smaller generic results are retained. Statistics distinguish
   candidates constructed from DBA components actually selected.
5. **Keep safety constraints attached.** A conjunction containing safety and
   other conjuncts stays together, including in the residual passed to Spot.
   This avoids the two observed powerset blow-ups. Other Boolean components
   can still use decomposition.
6. **Compare Low and High generic candidates.** Optimization level is not a
   monotone size guarantee. Low produces 8 versus High's 20 states on Dwyer
   line 44, and 50 versus 65 on Liberouter line 36. The smaller completed
   candidate is kept; this costs extra translation work where both are tried.
7. **Fix separator absence and capacity fallback.** `find_master_separator`
   returns the false formula when none exists, but the caller tested pointer
   validity. That caused repeated bogus splits on `0`. The caller now checks
   the sentinel correctly. A real profile product can also exceed the installed
   acceptance-set capacity; that whole attempt is discarded and the original
   formula is translated directly. No partial language branch is returned.

`--no-specialized` disables the new early fragment/guard routing;
`--no-dba` disables checked DBA attempts. `--dba-state-limit=N` and
`--dba-cycle-limit=N` expose their budgets; zero disables attempts. These
switches are ablations, not an exact emulation of the historical binary.
The ordinary generic translator now compares optimization levels separately.

## Updated results and validation

All **454** updated COLA outputs (227 formulas, both modes) passed determinism
and language equivalence against the original Spot/DELAG reference artifacts.
Both modes finish all inputs. Against the 225 previously successful default
COLA runs, 15 outputs have fewer states and 210 tie: **no state-count
regressions**. Reset mode improves 12 and ties 213 against its own prior
successful runs. The two former timeouts are additional successful outputs.

On the same 222-formula common cohort as before:

| Configuration | Complete state total | Smallest including ties |
| --- | ---: | ---: |
| Original COLA | 1337 | 192 |
| Updated COLA | 1036 | 207 |
| Updated COLA with finite witnesses | 1108 | 203 |
| Spot reference | 1058 | 207 |
| LTL3TELA reference | 991 | 217 |

The updated default is smaller overall than its old implementation and
slightly smaller in total than default Spot here. LTL3TELA still leads this
size comparison. The explicit DBA route is selected on 50 default-mode
formula runs; other GF/safety/weak routes can also produce DBAs. Boolean
GF/FG routing is used on 39 default-mode formula runs. State totals over
all 227 formulas should not be compared to old totals missing timeout cases.

Validation completed on this computer with Spot 2.14.1 and Apple Clang 17:

- `make check`: eight raw elevator acceptance fixtures and 17 new fragment
  language/routing regressions passed. The new tests cover one-state GF/FG,
  dedicated GF/FG endpoints, response DBAs, disabled/zero DBA budgets, the
  absent-separator bug and whole-formula acceptance-capacity fallback.
- Complete smoke suite, including X-advice and elevator checks: passed.
- Literature rerun: all 454 outputs passed; no timeouts.
- Five-repeat kernel/scaling campaign: all 87 measured outputs passed, with
  no timeout or acceptance-capacity failure.
- The same campaign at reset-state budget 4096: all 87 outputs passed.
- Seeded 50 kernels and 50 duals plus 17 fixed cases: all 351 measured outputs
  and all 585 forced-budget/fast-path-bypass checks passed.
- LTL3TELA ablations: all 77 outputs passed.

The new kernel CSVs use the `finite-witness-specialized-` prefix. They
supersede performance claims about the old default for the changed binary.
For example, the mixed kernel now has 13 states on both COLA paths; reset
still uses 82 versus 94 edges. At until width five, the specialized default
has 32 states/486 edges and median 65.6 ms, versus reset's 32/306/12.6 ms.
At X depth ten, the default reset budget abandons its attempt and falls back
to the specialized GF route, which completes instead of hitting the old
acceptance-set ceiling. With budget 4096 the actual reset monitor completes.

The optional reset route can still be larger than the specialized default
on some literature formulas. Keeping it opt-in remains appropriate. A
general polarity portfolio and more selective suspension/composition are
the next evidence-backed opportunities from the LTL3TELA ablations; this
change does not claim to implement LTL3TELA's SLAA construction or a complete
DBA-recognizability decision procedure.

## Reproduction and artifacts

```sh
make -C build-local -j4 check
LTLD=./build-local/ltl2dela sh tests/ltl2dela-smoke.sh
python3 tests/recheck-cola-fragments.py
python3 tests/diagnose-ltl-sizes.py
python3 tests/summarize-ltl-sizes.py tests/ltl-size-results.csv \
  --overlay tests/ltl-fragment-results.csv --output tests/ltl-fragment-summary.md
```

The corpus recheck uses the retained `build-local/owl-comparison/` reference
artifacts from the original experiment. They can be regenerated using that
experiment's runner with a fresh CSV destination and the pinned reference
tool versions. No old COLA binary is required to generate Spot/DELAG references.
The combined six-tool summary reuses those four unchanged tools' measurements;
only the COLA modes are rerun. Source/binary hashes and limits are retained in
[ltl-fragment-environment.json](ltl-fragment-environment.json). Raw new outputs
and stderr are under `build-local/fragment-comparison/`. DBA budgets do not
provide whole-process resource isolation; the external runner retains its
30-second timeout.
