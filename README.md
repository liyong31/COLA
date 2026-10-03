# COLA: a determinization, complementation and containment checking library for Büchi automata

COLA has been built on top of [SPOT](https://spot.lrde.epita.fr/) and inspired by [Seminator](https://github.com/mklokocka/seminator).


### List of algorithms
TBA

### Requirements
* [Spot](https://spot.lrde.epita.fr/)

```
./configure --enable-max-accsets=128
```
One can set the maximal number of colors for an automaton when configuring Spot with --enable-max-accsets=INT
```
make && make install
```

### Compilation
Please run the following steps to compile COLA after cloning this repo:
```
autoreconf -i
```
```
./configure [--with-spot=where/spot/is/installed]
```
```
make
```

Then you will get an executable file named **cola** !

### Determinization
Input an NBA from "filename", and run ```./cola --determinize=cola filename --simulation --stutter --use-scc```, then you will get an equivalent deterministic automaton on standard output!

To output the result to a file, use ```./cola --determinize=cola filename -o out_filename --simulation --stutter --use-scc```

To output a deterministic Parity automaton, use ```./cola --determinize=cola filename --parity --acd --simulation --stutter --use-scc```

To output a deterministic Rabin automaton, use ```./cola --determinize=cola filename --rabin --simulation --stutter --use-scc```

To output a complement automaton, use ```./cola --determinize=cola filename --parity --acd --complement --simulation --stutter --use-scc```

## Experimental LTL to deterministic Emerson-Lei translation

The `ltl2dela` branch contains an experimental C++ front-end for translating
LTL directly to deterministic Emerson-Lei automata while avoiding general
Buchi determinization whenever possible.

The current pipeline is:

1. simplify the original formula, but deliberately preserve its recurrent
   `GF(...)` structure;
2. apply exact structural recurrence rules before any general automaton
   construction, including
   `GF X p = GF p`, `GF F p = GF p`, `GF(a U b) = GF b`,
   `GF(a M b) = GF(a & b)`, `GF G p = FG p`, distribution over
   disjunction, extraction of top-level `G`/`F` obligations from
   conjunctions, and a two-state deterministic monitor for flat
   `GF(lambda & (g U h))`;
3. recognize explicit post-commitment bundles of the form
   `S & GF(theta_1) & ...` together with `FG gamma` / `GF !gamma`
   profile facts, and compile all conjuncts under the same asymptotic context;
4. if a recurrent kernel still contains a nested `G gamma`, synthesize a
   bounded pre-Buchi Y-profile split
   `FG gamma | GF !gamma` before building an NBA;
5. use the chosen profile context to simplify recurrent temporal guards.
   For example, under `FG g`, late suffixes satisfy
   `g U h = F h`, `a M g = F a`, `g W h = true`, and
   `a R g = true`; under `GF !g`, weak-until/release reduce to their
   strong counterparts;
6. only after these structural steps, use Spot's `to_delta2()`
   normalization when its growth stays within the configured bound;
7. let Spot directly compile remaining syntactically easy fragments;
8. for a genuinely residual formula, ask Spot for a small Buchi automaton,
   annotate hard states with `match_states()`, and inspect its SCCs;
9. if the BA is elevator, use CoLA's elevator determinizer; otherwise perform
   SCC-scored profile refinement, and finally fall back to direct
   deterministic formula translation if the bounded refinement budget is
   exhausted.

Because every profile split is a tautological partition of the language, the
profile heuristic affects only automaton size, not correctness.  The fallback
makes the translator total.

### Build

The standard CoLA build now also builds `ltl2dela`:

```
autoreconf -i
./configure --with-spot=/path/to/spot
make
```

### Examples

```
./ltl2dela -f 'GF(a | G b)'
./ltl2dela --stats --verbose -f 'GF(c & (a U b))'
./ltl2dela --profile-depth=6 --profile-budget=40 -f 'G(a -> F b) & FG c'
```

The tool writes HOA with deterministic generic acceptance.  Useful tuning options include `--profile-depth`, `--profile-budget`,
`--profile-lookahead`, and `--guard-max-length`.  Delta2 normalization and
formula annotations are enabled by default and can be disabled with
`--no-delta2`, `--no-recurrence`, `--no-master-profiles`, and
`--no-annotations`.

Smoke tests are in:

```
sh tests/ltl2dela-smoke.sh
```

### Current implementation boundary

This C++ implementation uses Spot as the LTL-to-Buchi backend and CoLA as the
SCC/elevator backend.  Spot's 2024 Delta2 normalization is wired in directly.
The full Esparza-Kretinsky-Sickert Master-Theorem derivative construction is
not yet reimplemented internally; that remains the main next step.

For LTL-derived Buchi automata, `spot::match_states(aut, f)` is used to
recover a residual formula for each state.  Spot guarantees these formulas as
sound over-approximations of the corresponding state languages.  Therefore
CoLA uses them in two ways that preserve correctness:

* states inside nondeterministic accepting SCCs contribute their residual
  temporal obligations to the candidate G-profile separators;
* for every deterministic accepting SCC, CoLA precomputes one fixed semantic
  state order.  Sound direct/delayed-simulation dominance gives hard ordering
  constraints (a simulator must occur before a state it simulates); mutual
  dominance is quotiented first.  The resulting DAG is topologically ordered,
  with matched-formula implication coverage used only to choose among
  incomparable classes.  At runtime, inherited runs keep their historical
  ranks and only genuinely fresh runs are appended according to this fixed
  SCC order.

The annotations are **not** used by themselves to remove runs or states,
because `match_states()` may over-approximate a nondeterministic state's
language.  Existing simulation checks remain responsible for pruning.

The central invariant is that CoLA's Buchi determinizer is invoked only after
`is_elevator_automaton()` succeeds; hard nondeterministic accepting SCCs
trigger profile refinement or direct formula-level deterministic fallback.


### Hybrid semantic ordering for deterministic accepting SCCs

The `ltl2dela` branch now uses a hybrid exact/approximate ordering policy
inside deterministic accepting SCCs.

For a state pair `p,q`, CoLA first tries the inexpensive sound relations
already available from direct or delayed simulation.  If those do not decide
that `p` dominates `q`, then, for sufficiently small SCCs and while a
global query budget remains, CoLA performs the exact check

```
L(q) subseteq L(p)
```

using Spot's `contains()` routine on copies of the source automaton with
`p` and `q` selected as initial states.  Exact results are cached.  When
the SCC is too large or the exact-query budget has been exhausted, the
construction automatically falls back to the existing approximation based on
simulation plus `match_states()` formula implication coverage.

The default bounds are intentionally conservative:

```
--exact-scc-limit=8
--exact-budget=64
```

Exact checks may be disabled completely with:

```
--no-exact-languages
```

The fixed per-SCC order therefore follows the hierarchy

```
cheap sound simulation
    -> bounded exact state-language containment for unresolved pairs
    -> formula-annotation implication coverage between incomparable classes
    -> stable textual/state-id tie break
```

Exact and simulation-based dominance facts are hard ordering constraints.
Formula annotations remain heuristic only.  Existing runs preserve their
historical ranks; the fixed semantic order is applied only to genuinely fresh
runs entering a deterministic accepting SCC.


### Bounded exact union-cover pruning

After the fixed semantic order has been assigned in a deterministic accepting
SCC, CoLA can now remove a later run `q_k` when it proves exactly that

```
L(q_k) subseteq L(q_0) union ... union L(q_{k-1}).
```

The smallest run is never removed.  The exact union is built from copies of
the source automaton with the retained earlier states selected as initial
states, combined with Spot's `product_or()`, and checked with
`spot::contains()`.

This optimization is deliberately bounded.  By default it is attempted only
when the number of retained earlier runs is at most 4 and while the global
exact-containment budget remains:

```
--exact-union-limit=4
--exact-budget=64
```

If either bound is exceeded, the later run is kept.  Thus expensive cases
automatically fall back to the cheaper simulation/annotation path.  Formula
annotations alone are never used to justify deletion.


When the retained earlier prefix is larger than `--exact-union-limit`, CoLA
does not give up immediately.  It uses residual-formula annotations and the
precomputed annotation-coverage scores to select a promising bounded subset
of earlier runs, prioritizing candidates whose annotation is syntactically
implied by the target annotation.  It then checks exact containment against
the union of that subset.  This is a sound approximation: annotations affect
only which exact query is attempted; a run is removed only after
`spot::contains()` proves the inclusion.


### Adaptive exact-query budgeting

Exact language checks are now budgeted adaptively rather than uniformly.

At most one third of `--exact-budget` is spent while computing the static
semantic order.  During that phase, exact unresolved-pair checks are attempted
preferentially when the matched residual formulas suggest that the candidate
simulator is more general; the formula test only selects which exact queries
to spend.

The remaining budget is used during determinization.  For every deterministic
accepting SCC CoLA tracks:

* how often the SCC appears with ranked runs in generated macrostates; and
* the maximum number of concurrent ranked runs observed there.

The SCC's runtime exact allowance grows approximately with

```
1 + 2 * max_rank_width + macrostate_visits / 8
```

subject to the remaining global budget.  Consequently cold/narrow SCCs stay on
the simulation/annotation path, while hot/wide SCCs receive more exact
union-cover checks.

With verbose diagnostics enabled, CoLA reports for each active deterministic
accepting SCC its visit count, maximum observed width, and exact-query usage.


### Explicit Master-profile front-end

The branch now performs a first explicit Master-Theorem-style pass before
Delta2 normalization and before any Buchi construction.

For conjunctions containing recurrence obligations and asymptotic profile
facts, the translator keeps a shared profile context of facts of the form

```
FG gamma
GF !gamma
```

and compiles the conjuncts independently under that same context.

In addition, if a still-unresolved `G gamma` occurs inside a `GF`
obligation, the translator can split immediately, before constructing any
Buchi automaton:

```
phi = (phi & FG gamma) | (phi & GF !gamma)
```

The two branches carry the corresponding profile fact explicitly.  This is
the concrete implementation of the delayed asymptotic commitment idea.

The profile context is used conservatively.  For example, under `FG gamma`,
an occurrence of `G gamma` inside the body of a `GF` obligation may be
replaced by true, because the replacement is valid from some finite point
onward and outer `GF` ignores that finite prefix.  Under `GF !gamma`,
`G gamma` is false on every suffix.  The same reasoning allows
`F gamma -> true` under `FG gamma` and `F !gamma -> true` under
`GF !gamma`.

These contextual rewrites are applied only inside recurrence bodies; the
translator does not globally replace `G gamma` by true under `FG gamma`,
which would be incorrect before the stabilization point.

The Master front-end may be disabled for A/B experiments with:

```
--no-master-profiles
```

The smoke tests compare Master-enabled and Master-disabled translations for
canonical and nested examples, including:

```
GF(a | G b)
GF((a U c) | G b)
GF((a & G b) | (c & G d))
FG b & GF(a | G b)
X GF(a | G b)
F(c & GF(a | G b))
```

For the canonical example `GF(a | G b)`, the intended pre-Buchi behavior is
now exactly the two asymptotic modes discussed in the design: a branch where
`b` stabilizes forever, and a branch where `!b` occurs infinitely often.


### Updated translation order

The structural recurrence compiler and explicit Master-profile front-end now
run before Delta2 normalization.  This preserves the `GF(mu)` syntax long
enough for exact rewrites and asymptotic profile simplification.  Delta2 is
used only after those passes, as an SCC-shaping normalization for the remaining
residual formula.

### Exact Master Y-advice for recurrence

For a recurrence obligation `GF psi`, the translator now collects all
nu-subformulas rooted at `G`, `W`, or `R`. The pre-Buchi profile layer
classifies each such subformula by the asymptotic dichotomy

```
FG chi
GF !chi
```

and, once the classification is complete, applies the exact EKS advice
transformation `psi[Y]_mu`:

```
G p        -> true  if G p is in Y, false otherwise
p W q      -> true  if p W q is in Y, otherwise p[Y]_mu U q[Y]_mu
p R q      -> true  if p R q is in Y, otherwise p[Y]_mu M q[Y]_mu
```

All other operators are transformed by recursive descent.

Thus the recurrence branch is explicitly reduced to mu-LTL before automata
construction, matching the `GF(psi[Y]_mu)` component of the Master Theorem.
The implementation keeps the previous cheaper profile rewrites as a secondary
optimization, but the exact Y-advice takes precedence whenever the nu-profile
is complete.

The remaining missing Master-Theorem component is the X/advice side

```
af(phi,u)[X]_nu
```

which requires a delayed formula derivative/progression layer. Spot exposes
the ordinary LTL-to-TGBA translation but no documented public after-function,
so this part will be implemented symbolically in CoLA rather than approximated.

### Exact X-advice and symbolic progression

Before the generic Büchi route, bounded residuals now use the X-advice
construction of Esparza–Křetínský–Sickert (LICS 2018, Definition 5.5 and
Section 6; <https://arxiv.org/abs/1805.00748>). This complements the existing
Y-advice recurrence rules. It does not yet replace profile certification by
the full mutually advised X/Y product of the Master Theorem.

For an NNF residual `f`, collect its distinct `F`, `U`, and `M` subformulas.
Enumerate all subsets `X` and check the exact profile

```
P_X = AND_{mu in X} GF mu  &  AND_{mu not in X} FG !mu.
```

Selected `F` formulas become true; selected `U` and `M` become `W` and `R`
with recursively advised operands. Unselected least-fixed-point formulas
become false. Other operators are mapped structurally. In particular, this
transformation is **not** an unconditional equivalence of `f`.

Each profile gets a deterministic co-Büchi monitor with states `(r, s)`.
Initially these are `(f, f[X]_nu)`. The first component always progresses
by one letter. The second progresses its safety obligation, except when it
is false: then it restarts from `r[X]_nu` and progresses that formula on the
same letter. Transitions out of false second components carry the rejecting
mark; acceptance requires finitely many such transitions. This recognizes
`exists i: w[i:] |= af(f, w[:i])[X]_nu`, including `i=0`.

Why the restart is exact: a satisfied advised residual stays satisfied after
progression and re-advice (EKS Lemma 6.1). A false safety obligation has a
finite bad prefix, so the monitor eventually restarts; once a successful
candidate exists, all later restart candidates succeed. Conversely, finitely
many failures leave a surviving safety candidate. On the exact profile
`P_X`, existence of such a candidate is equivalent to satisfaction of `f`:
after the last occurrence of every unselected mu formula, advice preserves
truth; selected mu formulas recur on every suffix and justify the converse.
Intersecting each monitor with its independently translated `P_X`, and taking
the union over **all** X, therefore preserves the original language.

The one-letter after construction combines disjoint BDD letter partitions,
without enumerating valuations. Equal residual regions are merged by BDD
union. Residuals are canonical positive Boolean skeletons over opaque
formula atoms. Only propositional equivalence is used here: temporal
simplification could change subformula identities and invalidate X membership.
BDD variables for the skeleton are private and are never output as APs.
No formula annotation is used for pruning or for proving a profile.

The defaults allow three mu subformulas, 256 states per monitor, and 4096
entries per symbolic cache/partition. `--x-advice-max-mu=N`,
`--x-advice-state-limit=N`, and `--x-advice-work-limit=N` control these limits;
`--no-x-advice` disables the layer. Exceeding a limit abandons the **whole**
profile construction and translates the original residual by the existing
route; a partial union is never returned. Easy fragments retain their earlier
direct translation priority. Profile guards currently use Spot's generic
deterministic translation, so this is an exact construction, not a claim of
an across-the-board performance improvement.

The smoke suite checks focused X-advice cases against both the disabled-layer
translation and independent `ltl2tgba -D -G` output, asserts the layer was
actually exercised, and covers resource-limit fallback.

Validation also exposed a pre-existing elevator translation mismatch for
`GF((G a | (b W c)) & (d R e))` with `--no-master-profiles`. Disabling
annotations or exact-language pruning did not remove it. The LTL front-end
now checks elevator output for exact equivalence with its source Büchi
automaton and uses the generic formula translation if the check fails.
`--stats` reports these `elevator validation fallbacks`. This check has a
runtime cost; it contains the existing error rather than claiming to repair
the underlying elevator algorithm. The smoke suite includes an independent
Spot-reference regression for this case.
