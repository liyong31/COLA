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
Input an NBA from "filename", and run ```./cola filename --simulation --stutter --use-scc```, then you will get an equivalent deterministic automaton on standard output!

To output the result to a file, use ```./cola filename -o out_filename --simulation --stutter --use-scc```

To output a deterministic Parity automaton, use ```./cola filename --parity --acd --simulation --stutter --use-scc```

To output a deterministic Rabin automaton, use ```./cola filename --rabin --simulation --stutter --use-scc```

To output a complement automaton, use ```./cola filename --parity --acd --complement --simulation --stutter --use-scc```