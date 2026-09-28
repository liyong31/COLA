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

1. let Spot directly compile syntactically easy safety, guarantee, obligation,
   recurrence, and persistence fragments to deterministic generic automata;
2. for a residual formula, ask Spot for a small Buchi automaton;
3. inspect its SCCs with CoLA and, if it is an elevator automaton (all SCCs
   deterministic or inherently weak), use CoLA's elevator determinizer;
4. otherwise generate asymptotic separator candidates from bodies of `G`
   subformulas and recurrent `U/M/R/W` guards;
5. refine the residual formula with the exhaustive profile split

       phi = (phi & FG gamma) | (phi & GF !gamma)

   and rank candidates by the number and size of nondeterministic accepting
   SCCs in the two resulting Buchi automata;
6. recursively translate the two profile branches and combine their
   deterministic results with generic Emerson-Lei acceptance;
7. if bounded profile refinement does not remove the hard SCCs, fall back to
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

The tool writes HOA with deterministic generic acceptance.  Useful tuning
options include `--profile-depth`, `--profile-budget`,
`--profile-lookahead`, and `--guard-max-length`.

Smoke tests are in:

```
sh tests/ltl2dela-smoke.sh
```

### Current implementation boundary

This first C++ implementation deliberately uses Spot as the LTL-to-Buchi
backend and CoLA as the SCC/elevator backend.  It does **not yet** implement
the full Esparza-Kretinsky-Sickert Master-Theorem derivative construction
internally, nor the 2024 contextual Delta2 normalization.  The API is split
into `src/ltl2dela.{hpp,cpp}` so those two pieces can be added without
changing the command-line front-end.

The central invariant already implemented is that CoLA's Buchi determinizer
is invoked only after `is_elevator_automaton()` succeeds; hard
nondeterministic accepting SCCs trigger profile refinement or direct
formula-level deterministic fallback instead.
