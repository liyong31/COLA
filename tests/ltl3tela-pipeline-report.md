# LTL3TELA internal pipeline audit

Inspected the actual benchmark source: LTL3TELA 2.1.1, upstream commit
02092adca492678407bd74b5d3bbe103d8c2b400, with the retained Clang template patch.
The executable uses local Spot 2.14.1. Our original tool comparison invoked
`ltl3tela -D1`, which enables the default portfolio, not a single construction.

## Core translation

1. Unabbreviate and simplify the formula with Spot; translate to a self-loop
   alternating automaton (SLAA), with U/G merging and transition dominance.
2. Remove unreachable SLAA states and unnecessary acceptance marks.
3. Enumerate configurations by multiplying outgoing alternating transitions.
   Lift acceptance into a nondeterministic transition-based Emerson–Lei automaton;
   apply equivalence merging, remove unused marks, and filter SCCs.
4. Always call `try_postprocessing()`. With `-D1`, this invokes Spot's Generic,
   Deterministic, High postprocessor and compares its output with the original.
   Already deterministic configurations may retain Emerson–Lei acceptance.

The general nondeterministic case is not handled by a distinct LTL3TELA ELA
rank determiniser. Spot's postprocessor attempts weak deterministic minimisation
where applicable, simulation, and retention of already deterministic results.
Its generic deterministic fallback converts to generalized Büchi, then calls
`tgba_determinize()`, whose documented core is Redziejowski's transition-based
variant of Safra/Piterman determinisation. That routine degeneralises generalized
Büchi input and produces parity acceptance. Local SCC, simulation and stuttering
optimisations are enabled by default. TBA determinisation is an optional Spot
branch; LTL3TELA does not request that option here.

Thus even the isolated native route is accurately described as
**LTL3TELA SLAA/dealternation + Spot postprocessing/determinisation**.
It is not a standalone, acceptance-preserving ELA determinisation algorithm.
Also, `-D0` still calls the Spot postprocessor, although without its deterministic
preference. Its output is not an untouched pre-postprocessing configuration graph.

## Default selection layers

| Option | Default | Effect |
| --- | --- | --- |
| `-b` | `3` | Also translate directly with Spot and try SPOTELA simplification |
| `-n` | `1` | Translate the negation, dualise a deterministic result, compare sizes |
| `-l` | `1` | Compare whole-formula translation with recursive Boolean composition |
| `-D` | `0`; our benchmark sets `1` | Request deterministic postprocessing |
| `-t` | `1` | Optimise the SLAA-to-NA acceptance lifting |
| `-x` | `0` | `-x1` reports selected route labels on stderr |

The `-l` option is implemented and enabled by default even though it is absent
from the printed help. Disabling `-b` and `-n` alone does not disable composition.

`build_best_nwa()` builds native positive/negative candidates, optionally applies
SPOTELA, constructs fresh Spot positive/negative candidates, and compares them.
Fresh Spot translations use Generic acceptance, High optimisation and the
Deterministic preference when `-D1` is set. SPOTELA is a graph/acceptance rewrite,
not another complete LTL translation: it merges eligible singleton SCC structures
of generalized Büchi automata into smaller Emerson–Lei graphs, with language
inclusion checks where needed.

`main()` also calls `build_product_nwa()` for top-level conjunction/disjunction.
The recursive component translations have their own candidate selection; ordinary
or suspension products then compose them. The product is postprocessed and
compared with the whole-formula candidate. These are nested selections.

`compare_automata()` prefers a deterministic result first when `-D1` is set,
then fewer states, fewer acceptance sets, fewer edges, semideterminism, and finally
the first candidate. The source comment gives an older order; this audit follows
the executable code.

## Reproduced measurements

`tests/diagnose-ltl3tela-pipeline.py` runs all 227 collected formulas in two modes:

- Default: `-D1 -x1`.
- Isolated positive SLAA route: `-D1 -b0 -n0 -l0 -x1`.

Both retain the same default internal SLAA optimisations and acceptance lifting.
Thirty seconds per process, two workers. Every successful output passes
independent reference equivalence, determinism and completeness. State counts
are measured both with completion only (the original experiment's policy) and
with the common acceptance/Low postprocessing policy used in the fixed OWL
controls. The totals below agree under both policies. Timings are diagnostic.

On the same 222 successful default cases:

| Route | Total states |
| --- | ---: |
| Default LTL3TELA | 991 |
| Isolated positive SLAA + Spot postprocessing | 12084 |

Disabling the outer selection increases 45 outputs and ties 177; none shrinks.
The default route labels are 173 `basic`, 26 `spot`, 20 `neg`, one `spotneg`, and
two Boolean compositions. A `basic` label still includes Spot postprocessing;
it must not be counted as a standalone native determiniser. Ties can retain the
first candidate, so labels do not prove exclusive provenance of a state count.

Large differences include Hardness12: 1 versus4871 states, Parametrised39:
1 versus4404, Hardness9: 1 versus808, Parametrised38: 1 versus191, and
Parametrised27: 1 versus121. These explain why aggregate totals are sensitive to
hard examples and why a total alone does not describe per-formula performance.

The default has 222 successes, four timeouts (Liberouter45 and Hardness2/4/6),
and one reproducible signal-11 crash on Somenzi11. These statuses reproduce the
retained original LTL3TELA results. The isolated route has 225 successes,
one timeout (Liberouter45), and the same Somenzi11 crash. These failures are
upstream experiment outcomes, not language-correct outputs; no result is filled
in from another translator.

## Fixed-route comparison

Adding the isolated SLAA route to the prior positive-only comparison leaves
221 formulas successful in every fixed route. The same common normalisation is
used, and the COLA rows always use the pruned result without selecting an
unpruned alternative.

| Fixed positive route | Total states |
| --- | ---: |
| SEJK16 LDGBA -> COLA independent-SCC ELA determinisation | 1672 |
| EKS20 LDGBA -> COLA independent-SCC ELA determinisation | 1700 |
| SEJK16 -> OWL EKRS17, both portfolios disabled | 1913 |
| EKS20 -> OWL EKRS17, both portfolios disabled | 2889 |
| LTL3TELA SLAA -> Spot postprocessing, outer selection disabled | 7046 |

These use different frontends and acceptance formats, so they are fixed-route
comparisons, not a controlled comparison of determinisers on the same graph.
COLA SEJK16 is smaller than isolated SLAA on27 cases, larger on46 and ties148.
It wins the total because of the larger difficult examples, not because it wins
most pairwise disagreements. No universal best-algorithm or runtime claim follows.
The 221-formula cohort differs from the earlier four-route cohort of223.

For a strict backend comparison, the next boundary to export is the configuration
TELA immediately before `try_postprocessing()`. No existing CLI flag disables
that call. Our current raw `-D0 -b0 -n0 -l0 -t0` inputs have already undergone
Spot postprocessing; changing that boundary needs a separately labelled tool
patch and fresh equivalence/admission measurements.

## Source and reproduction

- [Pinned native pipeline](https://github.com/jurajmajor/ltl3tela/blob/02092adca492678407bd74b5d3bbe103d8c2b400/nondeterministic.cpp): configuration construction, `build_best_nwa`, `build_product_nwa`, `try_postprocessing`.
- [Pinned main](https://github.com/jurajmajor/ltl3tela/blob/02092adca492678407bd74b5d3bbe103d8c2b400/main.cpp): command options and whole-formula/product comparison.
- [Pinned utilities](https://github.com/jurajmajor/ltl3tela/blob/02092adca492678407bd74b5d3bbe103d8c2b400/utils.cpp): actual defaults and candidate ordering.
- [Pinned SPOTELA implementation](https://github.com/jurajmajor/ltl3tela/blob/02092adca492678407bd74b5d3bbe103d8c2b400/spotela.cpp).
- Local Spot 2.14.1: `build-local/external/spot-2.14.1/spot/twaalgos/postproc.cc` lines612–620 and `determinize.hh` lines29–47.

Run `python3 tests/diagnose-ltl3tela-pipeline.py`. Data and manifest:
`tests/ltl3tela-pipeline.csv` and `tests/ltl3tela-pipeline.json`.
The initial ten-second diagnostic was replaced by this complete thirty-second
run; its data remain only in build-local/ltl3tela-pipeline-initial-10s.csv.
