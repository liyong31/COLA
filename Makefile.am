## Copyright (C) 2019-2020  The Seminator Authors
## Copyright (C) 2022  The COLA Authors
##
## This file is a part of COLA, a tool for determinization
## of Buchi automata.
##
## COLA is free software: you can redistribute it and/or modify
## it under the terms of the GNU General Public License as published by
## the Free Software Foundation, either version 3 of the License, or
## (at your option) any later version.
##
## COLA is distributed in the hope that it will be useful,
## but WITHOUT ANY WARRANTY; without even the implied warranty of
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
## GNU General Public License for more details.
##
## You should have received a copy of the GNU General Public License
## along with this program.  If not, see <http://www.gnu.org/licenses/>.

## The COLA Authors
##
## Removed some unnecessary files (e.g. the python binding for Seminator)

bin_PROGRAMS = cola ltl2dela
lib_LTLIBRARIES = src/libcola.la

AM_CPPFLAGS = -I$(srcdir)/src -I$(SPOTPREFIX)/include
ACLOCAL_AMFLAGS = -I m4

cola_LDADD = -L$(SPOTPREFIX)/lib src/libcola.la -lspot -lbddx
src_libcola_la_LIBADD = -L$(SPOTPREFIX)/lib -lspot -lbddx

src_libcola_la_SOURCES =			\
  src/cola.hpp			\
  src/cola.cpp			\
  src/complement_tnba.cpp			\
  src/composer.cpp				\
  src/composer.hpp				\
  src/decomposer.hpp			\
  src/decomposer.cpp			\
  src/determinize_teba.cpp			\
  src/determinize_tldba.cpp			\
  src/determinize_tnba.cpp			\
  src/determinize_twba.cpp			\
  src/optimizer.hpp				\
  src/optimizer.cpp				\
  src/ltl2dela.hpp				\
  src/ltl2dela.cpp				\
  src/simulation.cpp			\
  src/simulation.hpp			\
  src/types.hpp

cola_SOURCES = src/main.cpp

ltl2dela_SOURCES = src/ltl2dela_main.cpp
ltl2dela_LDADD = -L$(SPOTPREFIX)/lib src/libcola.la -lspot -lbddx

check_PROGRAMS = tests/elevator-acceptance
tests_elevator_acceptance_SOURCES = tests/elevator-acceptance.cpp
tests_elevator_acceptance_LDADD = $(ltl2dela_LDADD)
TESTS = tests/elevator-acceptance
EXTRA_DIST = tests/ltl2dela-smoke.sh tests/finite-witness.py \
  tests/finite-witness-benchmarks.md tests/finite-witness-results.csv \
  tests/finite-witness-random-results.csv tests/finite-witness-large-results.csv

EXTRA_DIST += tests/compare-ltl-sizes.py tests/summarize-ltl-sizes.py \
  tests/ltl-size-comparison.md tests/ltl-size-summary.md \
  tests/ltl-size-results.csv tests/ltl-size-environment.json \
  tests/ltl3tela-clang.patch tests/ltl-size-corpus/README.md \
  tests/ltl-size-corpus/DwyerAC98.ltl tests/ltl-size-corpus/EtessamiH00.ltl \
  tests/ltl-size-corpus/Liberouter04.ltl tests/ltl-size-corpus/Parametrised.ltl \
  tests/ltl-size-corpus/Parametrised-Hardness.ltl tests/ltl-size-corpus/Pelanek07.ltl \
  tests/ltl-size-corpus/SickertEJK16.ltl tests/ltl-size-corpus/SomenziB00.ltl
