// Copyright (C) 2017-2019 Laboratoire de Recherche et Développement
// de l'Epita.
// Copyright (C) 2020  The Seminator Authors
// Copyright (C) 2021  The COLA Authors
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

#include "determinize.hpp"
#include "cola.hpp"
//#include "struct.hpp"

#include <deque>
#include <map>
#include <set>
#include <vector>

#include <spot/misc/hashfunc.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/isunamb.hh>

#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/parity.hh>

#include <spot/twaalgos/postproc.hh>

#include <spot/parseaut/public.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/misc/version.hh>
#include <spot/twa/acc.hh>

namespace cola
{

  // Returns true if lhs has a smaller nesting pattern than rhs
  // If lhs and rhs are the same, return false.
  // compare backwards
  bool nesting_cmp(const std::vector<int> &lhs,
                   const std::vector<int> &rhs)
  {
    unsigned m = std::min(lhs.size(), rhs.size());
    auto lit = lhs.rbegin();
    auto rit = rhs.rbegin();
    for (unsigned i = 0; i != m; ++i)
    {
      if (*lit != *rit)
        return *lit < *rit;
      lit++;
      rit++;
    }
    return lhs.size() > rhs.size();
  }

  // Backward search for obtaining the nesting pattern
  // The obtained nesting pattern is in reverse order
  bool
  compare_braces(std::vector<int> &braces, int a, int b)
  {
    std::vector<int> a_pattern;
    std::vector<int> b_pattern;
    a_pattern.reserve(a + 1);
    b_pattern.reserve(b + 1);
    unsigned size_a = 0;
    unsigned size_b = 0;
    while (a != b)
    {
      if (a > b)
      {
        a_pattern.emplace_back(a);
        // go to the parent
        a = braces[a];
        size_a++;
      }
      else
      {
        b_pattern.emplace_back(b);
        // go to the parent
        b = braces[b];
        size_b++;
      }
    }
    return nesting_cmp(a_pattern, b_pattern);
  }

  void determinize_dac_succ::compute_succ()
  {
    succ_ranks_.clear();
    // list of deterministic states, already ordered by its labelling
    std::map<unsigned, int> succ_nodes;
    int max_rnk = -1;
    // PRECONDITION: ranks are already ordered
    for (unsigned j = 0; j < curr_ranks_.size(); j++)
    {
      unsigned curr_state = curr_ranks_[j].first;
      int curr_rnk = curr_ranks_[j].second;
      max_rnk = std::max(max_rnk, curr_rnk);

      assert(curr_rnk == j);

      // states and ranking
      for (const auto &t : det_trans_[curr_state])
      {
        unsigned succ_scc = si_.scc_of(t.second);
        // ignore the states that go to other SCCs
        if (curr_scc_ != succ_scc)
          continue;
        next_level_.erase(t.second);
        // Stay in the same accepting deterministic SCC or just enter this SCC
        // All DAC-states already have assigned with MAX_RANK
        auto it = succ_nodes.emplace(t.second, curr_rnk);
        if (!it.second) // already there
        {
          int prev_rnk = it.first->second;
          it.first->second = std::min(curr_rnk, prev_rnk);
        }
      }
    }

    ++max_rnk;
    // put them into succ
    for (unsigned p : next_level_)
    {
      // insertion failed is possible
      succ_nodes.emplace(p, max_rnk);
      ++max_rnk;
    }

    //succ.detscc_labels_[i].clear();
    for (auto &node : succ_nodes)
    {
      succ_ranks_.emplace_back(node.first, node.second);
    }
  }

  int determinize_dac_succ::get_color()
  {
    int min_acc = -1;
    int min_dcc = -1;

    std::map<unsigned, int> succ_nodes;
    for (auto &p : succ_ranks_)
    {
      succ_nodes[p.first] = p.second;
    }

    for (unsigned j = 0; j < curr_ranks_.size(); j++)
    {
      bool has_succ = false;
      bool has_acc = false;
      unsigned curr_state = curr_ranks_[j].first;
      int curr_rnk = curr_ranks_[j].second;
      assert(curr_rnk == j);
      for (const auto &t : det_trans_[curr_state])
      {
        // ignore the states that are not existing
        if (succ_nodes.find(t.second) == succ_nodes.end())
        {
          continue;
        }
        // 1. first they should be in the same SCC
        // 2. second the label should be equal
        if (si_.scc_of(curr_state) == si_.scc_of(t.second) && succ_nodes[t.second] == curr_rnk)
        {
          has_succ = true;
          has_acc = has_acc || t.first;
        }
      }
      if (!has_succ)
      {
        // i. no successor, record the smaller label
        if (min_dcc == -1)
        {
          min_dcc = 2 * j + 1;
        }
      }
      else if (has_acc && min_acc == -1)
      {
        // ii. see an accepting transition
        min_acc = 2 * (j + 1);
      }
      // number
    }
    // reorganize the indices
    std::sort(succ_ranks_.begin(), succ_ranks_.end(), rank_compare);
    for (int k = 0; k < succ_ranks_.size(); k++)
    {
      succ_ranks_[k].second = k;
    }
    // compute the color
    return std::min(min_acc, min_dcc);
  }

  void determinize_nac_succ::compute_succ()
  {
    // store the minimal new brace
    int min_new_brace = succ_braces_.size();

    std::map<unsigned, int> succ_nodes;
    
    // nodes are pair of states and labelling, ordered according to
    // labels and then state number
    for (const auto &node : curr_ranks_)
    {
      for (const auto &t : nondet_trans_[node.first])
      {
        unsigned dst = t.second;
        unsigned succ_scc = si_.scc_of(dst);
        int newb = node.second;
        // Only care about the states in the current SCC
        if (curr_scc_ != succ_scc)
          continue;

        // std::cout << " " << node.first << " -> " << t.dst << " : " << letter << " " << t.acc << std::endl;
        // Delete a newincoming state who is already a successor from the same SCC
        next_level_.erase(dst);
        if (t.first)
        {
          // Step A1: Accepting edges generate new braces
          newb = succ_braces_.size();
          // put current brace node.second as the parent of newb
          succ_braces_.emplace_back(node.second);
          // std::cout << " " << newb << " parent: " << node.second << std::endl;
        }
        auto i = succ_nodes.emplace(dst, newb);
        if (!i.second) // dst already exists
        {
          // Step A2: Only keep the smallest nesting pattern.
          if (compare_braces(succ_braces_, newb, i.first->second))
          {
            // newb is smaller
            i.first->second = newb;
          }
          else
          {
            // the newb is not smaller than current one
            if (newb != node.second) // new brace was created but is not needed
              succ_braces_.pop_back();
          }
        }
      }
    }

    // std::cout << "After computation of nondet inside " << i << " size = " << next_nondetstates.size() << "\n";
    // New incoming states
    // Top level is 0, if we enter the SCC, we need more braces
    // Order each entry states since each run can have accepting runs
    for (unsigned dst : next_level_)
    {
      // put them all in top brace 0
      int newb = succ_braces_.size();
      // Step A1
      auto i = succ_nodes.emplace(dst, newb);
      // If the state has not been added
      if (i.second || i.first->second == -1)
      {
        succ_braces_.push_back(RANK_TOP_BRACE);
        i.first->second = newb;
      }
    }
    if (reassign_ranks_)
    {
      // we need to reorganize the states from accepting transitions
      // so we may have a canonical form for the successor
      state_set higher_states;
      std::map<int, int> parent;
      for (auto &node : succ_nodes)
      {
        if (node.second >= min_new_brace)
        {
          // this state must come from accepting state
          higher_states.insert(node.first);
          // store the parent
          parent.emplace(node.second, succ_braces_[node.second]);
        }
      }
      // now we need to rearrange the braces in higher_states
      // states outside higher_states will have braces less than min_new_brace
      int new_brace = min_new_brace;
      for (unsigned dst : higher_states)
      {
        int old_brace = succ_nodes[dst];
        succ_nodes[dst] = new_brace;
        // it is guaranteed that the parent is less than min_new_brace
        succ_braces_[new_brace] = parent[old_brace];
        ++ new_brace; 
      }
    }
    // now store the results to succ
    succ_ranks_.clear();
    for (auto &node : succ_nodes)
    {
      succ_ranks_.emplace_back(node.first, node.second);
    }
  }

  int determinize_nac_succ::get_color()
  {
    std::vector<state_rank> &nodes = succ_ranks_;
    std::vector<int> braces = succ_braces_; // copy the vector

    int min_dcc = INT_MAX;
    int min_acc = INT_MAX;

    int topbrace = braces.size();
    constexpr char is_empty = 1;
    constexpr char is_green = 2;
    std::vector<char> empty_green;
    // initially both empty and green for a brace
    empty_green.assign(braces.size(), is_empty | is_green);

    for (const auto &n : nodes)
      if (n.second >= 0) // not top level, top level will not have red or good events?
      {
        int brace = n.second;
        // Step A4: The brace has a state on its own, so it is not a green event
        empty_green[brace] &= ~is_green;
        while (brace >= 0 && (empty_green[brace] & is_empty))
        {
          // Once there is brace associated with a state, it is certainly not empty
          empty_green[brace] &= ~is_empty;
          // backward search until top brace
          brace = braces[brace];
        }
      }

    // Step A4 Remove brackets within green pairs
    // for each bracket, find its highest green ancestor
    // 0 cannot be in a green pair, its highest green ancestor is itself
    // Also find red and green signals to emit
    // And compute the number of braces to remove for renumbering
    std::vector<int> highest_green_ancestor;
    highest_green_ancestor.assign(braces.size(), 0);

    std::vector<unsigned> decr_by;
    decr_by.assign(braces.size(), 0);
    unsigned decr = 0;

    for (int b = 0; b < braces.size(); ++b)
    {
      // At first, set it to iself
      highest_green_ancestor[b] = b;
      const int &ancestor = braces[b];
      // Note that ancestor < b
      if (ancestor >= 0 && (highest_green_ancestor[ancestor] != ancestor || (empty_green[ancestor] & is_green)))
      {
        // if we do not go further up to the tree or ancester is green
        highest_green_ancestor[b] = highest_green_ancestor[ancestor];
        empty_green[b] |= is_empty; // mark brace for removal
      }

      if (empty_green[b] & is_empty)
      {
        // Step A5 renumber braces
        ++decr;

        // Any brace above topbrace was added while constructing
        // this successor, so it should not emit any red.
        if (b < topbrace)
          // Step A3 emit red
          min_dcc = std::min(min_dcc, b);
      }
      else if (empty_green[b] & is_green)
      {
        assert(b < topbrace);
        // Step A4 emit green
        min_acc = std::min(min_acc, b);
      }

      decr_by[b] = decr;
    }
    // std::cout << "min_dcc = " << min_dcc << ", min_acc = " << min_acc << std::endl;
    //nondet_labellings.emplace_back(min_dcc, min_acc);
    // drease the values

    // Update nodes with new braces numbers
    std::vector<int> newbs = std::vector<int>(braces.size() - decr, -1);
    for (auto &n : nodes)
    {
      // if the brace is not -1
      if (n.second >= 0)
      {
        // highest ancester that is green
        unsigned i = highest_green_ancestor[n.second];
        int j = braces[i] >= 0 // except 0, every ancester should be this way
                    ? braces[i] - decr_by[braces[i]]
                    : -1;
        n.second = i - decr_by[i];
        // succ.ordered_states_[n.first] = n.second;
        newbs[n.second] = j;
      }
    }
    succ_braces_ = newbs;

    return -1;
  }

  bool
  tba_mstate::operator<(const tba_mstate &other) const
  {
    if (weak_set_ == other.weak_set_)
    {
      if (break_set_ == other.break_set_)
      {
        for (unsigned i = 0; i < dac_ranks_.size(); i ++)
        {
          if (dac_ranks_[i] == other.dac_ranks_[i])
          {
            continue;
          }else 
          {
            return dac_ranks_[i] < other.dac_ranks_[i];
          }
        }
        // equal size
        for (unsigned i = 0; i < nac_braces_.size(); i++)
        {
          if (nac_braces_[i] == other.nac_braces_[i])
          {
            continue;
          }
          else
          {
            return nac_braces_[i] < other.nac_braces_[i];
          }
          if (nac_ranks_[i] == other.nac_ranks_[i])
          {
            continue;
          }else 
          {
            return nac_ranks_[i] < other.nac_ranks_[i];
          }
        }
        return false;
      }
      else
      {
        return break_set_ < other.break_set_;
      }
    }else 
    {
      return weak_set_ < other.weak_set_;
    }
  }
  bool
  tba_mstate::operator==(const tba_mstate &other) const
  {
    if (weak_set_ != other.weak_set_)
    {
      return false;
    }
    if (break_set_ != other.break_set_)
    {
      return false;
    }
    for (unsigned i = 0; i < dac_ranks_.size(); i ++)
    {
      if (dac_ranks_[i] != other.dac_ranks_[i])
      {
        return false;
      }
    }
    for (unsigned i = 0; i < nac_ranks_.size(); i ++)
    {
      if (nac_ranks_[i] != other.nac_ranks_[i])
      {
        return false;
      }
      if (nac_braces_[i] != other.nac_braces_[i])
      {
        return false;
      }
    }
    return true;
  }
  
  state_set tba_mstate::get_reach_set() const
  {
    std::set<unsigned> result;
    result.insert(weak_set_.begin(), weak_set_.end());
    for (auto & vec : dac_ranks_)
    {
      for (auto& p : vec)
      {
        result.insert(p.first);
      }
    }
    for (auto & vec : nac_ranks_)
    {
      for (auto& p : vec)
      {
        result.insert(p.first);
      }
    }
    return result;
  }
  bool tba_mstate::is_empty() const
  {
    if (! weak_set_.empty())
    {
      return false;
    }
    for (unsigned i = 0; i < dac_ranks_.size(); i ++)
    {
      if (! dac_ranks_[i].empty())
      {
        return false;
      }
    }
    for (unsigned i = 0; i < nac_ranks_.size(); i ++)
    {
      if (! nac_ranks_[i].empty())
      {
        return false;
      }
    }
    return true;
  }

  state_set
  tba_mstate::get_weak_set() const
  {
    return weak_set_;
  }

  // Return the nodes sorted in ascending order
  std::vector<safra_node>
  tba_mstate::get_safra_nodes(unsigned index) const
  {
    assert (index >= 0 && index < nac_ranks_.size());
    std::vector<safra_node> res;
    for (unsigned i = 0; i < nac_ranks_[index].size(); i++)
    {
        // last brace
        int brace = nac_ranks_[index][i].second;
        std::vector<int> tmp;
        while (brace >= 0)
        {
          // insert in reverse order
          tmp.insert(tmp.begin(), brace);
          // obtain the i-th braces
          brace = nac_braces_[index][brace];
        }
        res.emplace_back(i, std::move(tmp));
    }
    // compare the node according to its labelling
    std::sort(res.begin(), res.end(), node_compare());
    return res;
  }

  size_t
  tba_mstate::hash() const
  {
    size_t res = 0;
    for (unsigned i : weak_set_)
    {
      res = (res << 3) ^ i;
    }
    for (unsigned i : break_set_)
    {
      res ^= (res << 3) ^ i;
    }
    for (unsigned i = 0; i < dac_ranks_.size(); i ++)
    {
      for (auto& p : dac_ranks_[i])
      {
        res ^= (res << 3) ^ (p.first);
        res ^= (res << 3) ^ (p.second);
      }
    }
    for (unsigned i = 0; i < nac_braces_.size(); i ++)
    {
      for (auto& p : nac_ranks_[i])
      {
        res ^= (res << 3) ^ (p.first);
        res ^= (res << 3) ^ (p.second);
      }
      for (int k : nac_braces_[i])
      {
        res ^= (res << 3) ^ ((unsigned) k);
      }
    }

    return res;
  }

  

}