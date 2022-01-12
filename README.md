# COLA: a determinization and complementation library for Büchi automata
COLA currently a determinization algorithm for nondeterministic Büchi automata.
COLA has been built on top of [SPOT](https://spot.lrde.epita.fr/) and inspired by [Seminator](https://github.com/mklokocka/seminator).


### List of algorithms
Complementing UNBA (Under construction): the [slice-based algorithm](https://arxiv.org/abs/2005.09125v2)
Determinizing nondeterministic BAs: under construction

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
./configure
```
```
make
```

Then you will get an executable file named **cola** !

### Determinization
Input an LDBA named "filename", and run ```./cola --determinize=cola filename```, then you will get an equivalent deterministic automaton on standard output!

To output the result to a file, use ```./cola --determinize=cola filename -o out_filename```

To output a deterministic Parity automaton, use ```./cola --determinize=cola filename --parity --acd```