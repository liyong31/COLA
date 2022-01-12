// Copyright (c) 2017-2020  The Seminator Authors
// Copyright (C) 2022  The COLA Authors
//
// This file is a part of Seminator, a tool for semi-determinization
// of omega automata.
//
// Seminator is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Seminator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <string>
#include <iterator>
#include <vector>
#include <tuple>
#include <map>
#include <set>
#include <iostream>
#include <bddx.h>

#include <spot/twa/twa.hh>
#include <spot/twaalgos/powerset.hh>
#include <spot/misc/bitvect.hh>
#include <spot/misc/optionmap.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/sccinfo.hh>


typedef unsigned state_t;

typedef std::vector<std::string> *state_names;


static const state_set empty_set;

// for complementation and determinization
enum ncsb
{
  ncsb_n = 0,  // non deterministic
  ncsb_c = 2,  // needs check
  ncsb_cb = 3, // needs check AND in breakpoint
  ncsb_s = 4,  // safe
  ncsb_m = 1,  // missing
};

// fengwz
enum ncb
{
  ncb_i = 1, // init phase
  ncb_n = 6, // 110
  ncb_c = 2, // 10
  ncb_b = 3, // 11
  ncb_m = 0,
};

// N S B C do not intersect each other
enum nsbc
{
  nsbc_n = 1,  // non deterministic
  nsbc_s = 4,  // safe
  nsbc_b = 3,  // needs check AND in breakpoint
  nsbc_c = 2,  // needs check
  nsbc_m = -1, // missing
  nsbc_i = 0,
};

const int detrb_m = -2;  // missing
const int detrb_n = -1;  // non deterministic
const int detrb_bot = 0; // bottom
const int detrb_d = 1;   // label

typedef std::vector<ncsb> mstate;
typedef std::vector<std::pair<unsigned, ncsb>> small_mstate;

typedef std::vector<ncb> macrostate;
typedef std::vector<std::pair<unsigned, ncb>> small_macrostate;

typedef std::vector<nsbc> mcstate;
typedef std::vector<std::pair<unsigned, nsbc>> small_mcstate;

typedef std::vector<int> dstate;
typedef std::vector<std::pair<int, int>> small_dstate;

struct small_mstate_hash
{
  size_t
  operator()(small_mstate s) const noexcept
  {
    size_t hash = 0;
    for (const auto &p : s)
    {
      hash = spot::wang32_hash(hash ^ ((p.first << 2) | p.second));
    }
    return hash;
  }
};

// fengwz
struct small_macrostate_hash
{
  size_t
  operator()(small_macrostate s) const noexcept
  {
    size_t hash = 0;
    for (const auto &p : s)
    {
      hash = spot::wang32_hash(hash ^ ((p.first << 2) | p.second));
    }
    return hash;
  }
};

// new semi complement
struct small_mcstate_hash
{
  size_t
  operator()(small_mcstate s) const noexcept
  {
    size_t hash = 0;
    for (const auto &p : s)
    {
      hash = spot::wang32_hash(hash ^ ((p.first << 2) | p.second));
    }
    return hash;
  }
};

// determinization
struct small_dstate_hash
{
  size_t
  operator()(small_dstate s) const noexcept
  {
    size_t hash = 0;
    for (const auto &p : s)
    {
      hash = spot::wang32_hash(hash ^ ((p.first << 2) | p.second));
    }
    return hash;
  }
};
