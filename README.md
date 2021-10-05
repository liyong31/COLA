# COmpLementing nondeterministic büchi Automata
Complement algorithms implementation for UNBA (Unambiguous Nondeterministic Büchi Automata) and SDBA (Semi-Deterministic Büchi Automata).

### First version 2021.6.28
The [slice-based algorithm](https://arxiv.org/abs/2005.09125v2) for UNBA complementation is implemented as a function in [Seminator](https://github.com/mklokocka/seminator). 

### 2021.7.2
* Fixed bugs in NCB algorithm implementation. 
* NSBC algorithm is implemented.
* random_nd.ltl has passed.

### Installation
Please run the following steps to compile COLA after git clone from this repo:
```
autoreconf -i
```
```
./configure --disable-python
```
```
make
```

Then you will get an executable file named **cola** !

### Determinization
Input an LDBA named "filename", and run ```./cola --determinize=parity filename```, then you will get an equivalence deterministic parity automaton !
