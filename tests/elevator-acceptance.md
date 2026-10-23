# Elevator acceptance offsets

For deterministic accepting SCC `i`, let `k = num_colours_`,
`B_i = sum_{h<i} |SCC_h| * (k+1)`, and `R_ij = B_i + j*(k+1)`.
Rank `j` owns source acceptance sets `R_ij ... R_ij+k-1` and
discontinuation set `R_ij+k`.  `compute_successors()` records local sets;
`finalize_acceptance()` adds `B_i` to the transition marks.  Consequently
the rank's acceptance must be `(source_acceptance << R_ij) & Fin(R_ij+k)`.
Omitting `B_i` from `Fin` couples different SCCs' rank histories.

Run `make check` for the raw C++ regression.  It directly calls
`determinize_televator()` and checks determinism and `spot::are_equivalent()`
against its input; it cannot use the LTL validation fallback.  The eight
fixtures have DA SCC sizes `(1,1)`, `(1,2)`, `(2,1)`, and `(1,2,3)`, each
with and without a weak accepting SCC.  They assert the intended SCC
classification.  Independent guards kill/restart runs independently in
each branch.  The original acceptance offset fails the first fixture;
the corrected offset passes all eight.

Run `sh tests/ltl2dela-smoke.sh` with Spot's tools on `PATH` for front-end
checks.  The known formula `GF((G a | (b W c)) & (d R e))` is checked with
`--no-master-profiles` against independent `ltl2tgba -D -G` output in four
modes: default, no annotations, no exact languages, and both disabled.

Validation on Spot 2.14.2 (128 acceptance sets), 2026-10-04:

- Build, `make check`, and the complete smoke suite passed.
- At parent `56caf612a4fec6a694abebd6a96f8e13d1f95827`, the known formula
  used two elevator components and triggered one validation fallback.
  With the offset fix, all four modes use two components and zero such
  fallbacks.  Hence the actual elevator results pass the existing exact
  checks against their source BAs.
- 150 formulas from `randltl --seed=41 --tree-size=8..20 -n 150 a b c`
  passed determinism and exact equivalence against `ltl2tgba -D -G`.
  Default settings used no elevator components in this sample.
- Repeating those formulas with `--no-master-profiles --no-x-advice
  --no-recurrence --no-delta2 --no-boolean-split --no-profiles` passed all
  150 comparisons, exercising 13 elevator components with zero validation
  fallbacks.

These regressions establish the offset defect and its repair, not general
correctness of the elevator construction or its pruning optimizations.
The front-end's exact validation and generic fallback remain unchanged.
