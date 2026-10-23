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
  src/slaa_frontend.cpp                 \
  src/slaa_frontend.hpp                 \
  src/owl_annotations.cpp               \
  src/owl_annotations.hpp               \
  src/colour_choice.cpp                 \
  src/colour_choice.hpp                 \
  src/cobuchi_weak.cpp                  \
  src/cobuchi_weak.hpp                  \
  src/late_monitor.cpp                  \
  src/late_monitor.hpp                  \
  src/simulation.cpp			\
  src/simulation.hpp			\
  src/types.hpp

cola_SOURCES = src/main.cpp

ltl2dela_SOURCES = src/ltl2dela_main.cpp
ltl2dela_LDADD = -L$(SPOTPREFIX)/lib src/libcola.la -lspot -lbddx

check_PROGRAMS = tests/elevator-acceptance tests/specialized-fragments tests/generic-elevator tests/tela-elevator-driver
tests_elevator_acceptance_SOURCES = tests/elevator-acceptance.cpp
tests_elevator_acceptance_LDADD = $(ltl2dela_LDADD)
tests_specialized_fragments_SOURCES = tests/specialized-fragments.cpp
tests_specialized_fragments_LDADD = $(ltl2dela_LDADD)
tests_generic_elevator_SOURCES = tests/generic-elevator.cpp
tests_generic_elevator_LDADD = $(ltl2dela_LDADD)
tests_tela_elevator_driver_SOURCES = tests/tela-elevator-driver.cpp
tests_tela_elevator_driver_LDADD = $(ltl2dela_LDADD)
TESTS = tests/elevator-acceptance tests/specialized-fragments tests/generic-elevator
TESTS += tests/slaa-route.py
TESTS += tests/ldgba-route.py tests/specialized-priority.py
check_PROGRAMS += tests/owl-annotations
tests_owl_annotations_SOURCES = tests/owl-annotations.cpp
tests_owl_annotations_LDADD = $(ltl2dela_LDADD)
TESTS += tests/owl-annotations
check_PROGRAMS += tests/colour-choice
tests_colour_choice_SOURCES = tests/colour-choice.cpp
tests_colour_choice_LDADD = $(ltl2dela_LDADD)
TESTS += tests/colour-choice
check_PROGRAMS += tests/cobuchi-weak
tests_cobuchi_weak_SOURCES = tests/cobuchi-weak.cpp
tests_cobuchi_weak_LDADD = $(ltl2dela_LDADD)
TESTS += tests/cobuchi-weak
check_PROGRAMS += tests/pure-persistence-driver
tests_pure_persistence_driver_SOURCES = tests/pure-persistence-driver.cpp
tests_pure_persistence_driver_LDADD = $(ltl2dela_LDADD)
TESTS += tests/pure-persistence-driver
check_PROGRAMS += tests/late-monitor
tests_late_monitor_SOURCES = tests/late-monitor.cpp
tests_late_monitor_LDADD = $(ltl2dela_LDADD)
TESTS += tests/late-monitor
check_PROGRAMS += tests/parametric-monitor
tests_parametric_monitor_SOURCES = tests/parametric-monitor.cpp
tests_parametric_monitor_LDADD = $(ltl2dela_LDADD)
TESTS += tests/parametric-monitor
TESTS_ENVIRONMENT = LTLD='$(abs_builddir)/ltl2dela'; export LTLD;
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

EXTRA_DIST += tests/diagnose-ltl-sizes.py tests/recheck-cola-fragments.py \
  tests/ltl-routing-diagnosis.md tests/ltl-size-ablations.csv \
  tests/ltl-timeout-probes.json tests/ltl-fragment-results.csv \
  tests/ltl-fragment-summary.md tests/ltl-fragment-environment.json \
  tests/finite-witness-specialized-results.csv \
  tests/finite-witness-specialized-large-results.csv \
  tests/finite-witness-specialized-random-results.csv

EXTRA_DIST += tests/compare-cola-polarities.py tests/summarize-cola-polarities.py \
  tests/ltl-polarity-results.csv tests/ltl-polarity-results.json \
  tests/ltl-polarity-summary.md tests/ltl-polarity-probes.json

EXTRA_DIST += tests/slaa-route.py
EXTRA_DIST += tests/ldgba-route.py tests/specialized-priority.py
EXTRA_DIST += tests/benchmark-slaa.py tests/summarize-slaa.py \
  tests/ltl-slaa-results.csv tests/ltl-slaa-results.json tests/ltl-slaa-report.md \
  tests/finite-witness-slaa-regressions.csv

EXTRA_DIST += tests/diagnose-slaa-shapes.py tests/summarize-slaa-shapes.py \
  tests/ltl-slaa-shapes.csv tests/ltl-slaa-shapes.json \
  tests/ltl-slaa-winner-ablations.csv tests/ltl-slaa-scc-probes.json \
  tests/ltl-slaa-shape-diagnosis.md tests/ltl-slaa-portfolio-results.csv \
  tests/ltl-slaa-portfolio-results.json \
  tests/finite-witness-slaa-portfolio-regressions.csv

EXTRA_DIST += tests/benchmark-ldgba.py tests/summarize-ldgba.py \
  tests/ltl-ldgba-raw-results.csv tests/ltl-ldgba-raw-results.json \
  tests/ltl-ldgba-results.csv tests/ltl-ldgba-results.json \
  tests/ltl-ldgba-optimizations.csv tests/ltl-ldgba-optimizations.json \
  tests/ltl-ldgba-report.md tests/finite-witness-ldgba-regressions.csv

EXTRA_DIST += research/colour-elevator.tex tests/benchmark-colour-choice.py \
  tests/summarize-colour-choice.py tests/colour-choice-results.csv \
  tests/colour-choice-results.json tests/colour-choice-integrated-results.csv \
  tests/colour-choice-integrated-results.json tests/colour-choice-report.md \
  tests/colour-choice-cases/response.hoa tests/colour-choice-cases/persistence.hoa \
  tests/colour-choice-cases/recurrence.hoa

EXTRA_DIST += tests/colour-choice-cases/hard-cobuchi.hoa \
  tests/probe-pure-persistence.py tests/benchmark-late-monitors.py \
  tests/summarize-colour-elevator.py tests/colour-elevator-report.md \
  tests/colour-weak-results.csv tests/colour-weak-results.json \
  tests/colour-weak-integrated-results.csv tests/colour-weak-integrated-results.json \
  tests/pure-persistence-results.csv tests/pure-persistence-results.json \
  tests/late-monitor-results.csv tests/late-monitor-results.json \
  tests/finite-witness-colour-regressions.csv tests/colour-acceptance-sizes.csv \
  research/colour-experiments.tex

EXTRA_DIST += tests/summarize-ldgba-pruning.py tests/ltl-ldgba-pruning-report.md \
  tests/ltl-ldgba-cache.csv tests/ltl-ldgba-cache.json \
  tests/ltl-ldgba-packed.csv tests/ltl-ldgba-packed.json \
  tests/ltl-ldgba-packed-pruning.csv tests/ltl-ldgba-packed-pruning.json \
  tests/ltl-ldgba-optimized-integrated.csv tests/ltl-ldgba-optimized-integrated.json \
  tests/ltl-ldgba-polarity-integrated.csv tests/ltl-ldgba-polarity-integrated.json \
  tests/finite-witness-ldgba-pruning-regressions.csv \
  tests/finite-witness-ldgba-pruning-regressions.json
EXTRA_DIST += research/ldgba-experiments.tex
EXTRA_DIST += tests/ltl-ldgba-pruning-default.csv tests/ltl-ldgba-pruning-default.json
EXTRA_DIST += tests/benchmark-owl-annotations.py tests/summarize-owl-annotations.py \
  tests/owl-annotations-results.csv tests/owl-annotations-results.json \
  tests/owl-annotations-negative-results.csv tests/owl-annotations-negative-results.json \
  tests/owl-annotations-integrated.csv tests/owl-annotations-integrated.json \
  tests/owl-annotations-report.md research/owl-annotations.tex \
  tests/finite-witness-owl-annotations.csv tests/finite-witness-owl-annotations.json

EXTRA_DIST += tests/diagnose-owl-ldgba-gap.py tests/summarize-owl-gap.py \
  tests/owl-gap-controls.csv tests/owl-gap-controls.json tests/owl-gap-report.md \
  tests/owl-cross-scc-results.csv tests/owl-cross-scc-results.json \
  tests/owl-cross-scc-negative-results.csv tests/owl-cross-scc-negative-results.json \
  tests/owl-cross-scc-integrated.csv tests/owl-cross-scc-integrated.json
EXTRA_DIST += research/owl-gap.tex tests/finite-witness-owl-cross.csv \
  tests/finite-witness-owl-cross.json

EXTRA_DIST += tests/diagnose-ltl3tela-pipeline.py tests/ltl3tela-pipeline-report.md \
  tests/ltl3tela-pipeline.csv tests/ltl3tela-pipeline.json \
  tests/benchmark-specialized-priority.py tests/specialized-priority-report.md \
  tests/specialized-priority-results.csv tests/specialized-priority-results.json \
  tests/finite-witness-priority.csv tests/finite-witness-priority.json
