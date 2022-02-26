// Copyright (C) 2022-present  The COLA Authors
//
// This file is a part of Seminator, a tool for semi-determinization
// of omega automata.
//
// COLA is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// COLA is distributed in the hope that it will be useful,
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

#include <spot/misc/bddlt.hh>

typedef unsigned state_t;
typedef std::set<state_t> state_set;

// state ranking
typedef std::pair<unsigned, int> state_rank;
// an outgoing edge from a state: 
//  bool value indicates whether it is accepting, unsigned value stores the destination
typedef std::pair<bool, unsigned> edge_label;

// a state and its labelling (list of integers/braces)
typedef std::pair<unsigned, std::vector<int>> safra_node;
// an outgoing transition for a given state
typedef std::pair<unsigned, bdd> outgoing_trans;

struct node_compare
{
  bool
  operator()(const safra_node &lhs,
             const safra_node &rhs) const
  {
    // return nesting_cmp(lhs, rhs);
    return lhs.second < rhs.second;
  }
};

struct outgoing_trans_hash
{
  size_t
  operator()(const outgoing_trans &s) const noexcept
  {
    return (s.first << 3) ^ s.second.id();
  }
};

// not sure whether we should keep this
struct
{
  size_t
  operator()(state_rank &p1, state_rank &p2) const noexcept
  {
    if (p1.second == p2.second)
    {
      return p1.first < p2.first;
    }
    return p1.second < p2.second;
  }
} rank_compare;
