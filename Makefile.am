## Copyright (C) 2019-2020  The Seminator Authors
##
## This file is a part of Seminator, a tool for semi-determinization
## of omega automata.
##
## Seminator is free software: you can redistribute it and/or modify
## it under the terms of the GNU General Public License as published by
## the Free Software Foundation, either version 3 of the License, or
## (at your option) any later version.
##
## Seminator is distributed in the hope that it will be useful,
## but WITHOUT ANY WARRANTY; without even the implied warranty of
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
## GNU General Public License for more details.
##
## You should have received a copy of the GNU General Public License
## along with this program.  If not, see <http://www.gnu.org/licenses/>.

## The COLA Authors
##
## Removed some unnecessary files (e.g. the python binding for Seminator)

bin_PROGRAMS = cola
lib_LTLIBRARIES = src/libcola.la

AM_CPPFLAGS = -I$(srcdir)/src
cola_LDADD = -L$(SPOTPREFIX)/lib src/libcola.la -lspot -lbddx
src_libcola_la_LIBADD = -L$(SPOTPREFIX)/lib -lspot -lbddx

src_libcola_la_SOURCES =			\
  src/breakpoint_twa.cpp			\
  src/breakpoint_twa.hpp			\
  src/bscc.cpp					\
  src/bscc.hpp					\
  src/cola.hpp			\
  src/cola.cpp			\
  src/complement.cpp			\
  src/cutdet.cpp				\
  src/cutdet.hpp				\
  src/determinize.cpp			\
  src/optimizer.hpp				\
  src/optimizer.cpp				\
  src/powerset.cpp				\
  src/powerset.hpp				\
  src/semideterminize.cpp			\
  src/seminator.cpp				\
  src/seminator.hpp				\
  src/types.hpp

cola_SOURCES = src/main.cpp
