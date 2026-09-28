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

1. simplify the formula and use Spot's `to_delta2()` implementation of the
   Esparza-Rubio-Sickert 2024 Delta2 normalization when the normalized result
   stays within the configured growth bound;
2. let Spot directly compile syntactically easy safety, guarantee, obligation,
   recurrence, and persistence fragments to deterministic generic automata;
3. for a residual formula, ask Spot for a small Buchi automaton;
4. annotate hard Buchi states with `spot::match_states(aut, formula)`;
5. inspect its SCCs with CoLA and, if it is an elevator automaton (all SCCs
   deterministic or inherently weak), use CoLA's elevator determinizer;
6. otherwise generate asymptotic separator candidates first from the matched
   formulas of states in nondeterministic accepting SCCs, then from bodies of
   syntactic `G` subformulas and recurrent `U/M/R/W` guards;
7. refine the residual formula with the exhaustive profile split

       phi = (phi & FG gamma) | (phi & GF !gamma)

   and rank candidates by the number and size of nondeterministic accepting
   SCCs in the two resulting Buchi automata;
8. recursively translate the two profile branches and combine their
   deterministic results with generic Emerson-Lei acceptance;
9. if bounded profile refinement does not remove the hard SCCs, fall back to
   Spot's direct deterministic generic translation of that residual formula.

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
`--no-delta2` and `--no-annotations`.

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
