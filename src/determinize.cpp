// Copyright (C) 2017-2019 Laboratoire de Recherche et Développement
// de l'Epita.
// Copyright (C) 2022 - present  The COLA Authors
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

  int compute_parity_color(int min_dcc, int min_acc)
  {
    int parity;

    if (min_dcc == -1 && min_acc != -1)
    {
      // only good events
      parity = 2 * (min_acc + 1);
    }
    else if (min_dcc != -1 && min_acc == -1)
    {
      // only bad events
      parity = 2 * min_dcc + 1;
    }
    else if (min_dcc != -1 && min_acc != -1)
    {
      // have both good and bad events
      parity = std::min(2 * min_dcc + 1, 2 * min_acc + 2);
    }
    else
    {
      parity = -1;
    }
    // std::cout << "Color: " << parity << std::endl;
    return parity;
  }

  // Returns true if lhs has a smaller nesting pattern than rhs
  // If lhs and rhs are the same, return false.
  // compare backwards, copied from spot
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
  // copied from spot
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

    state_set visited;
    int max_rnk = -1;

    // PRE-CONDITION: ranks are already  in ascending order
    for (unsigned j = 0; j < curr_ranks_.size(); j++)
    {
      unsigned curr_state = curr_ranks_[j].first;
      int curr_rnk = curr_ranks_[j].second;
      assert(curr_rnk == j);

      // record the maximal rank
      max_rnk = std::max(max_rnk, curr_rnk);

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
        if (visited.find(t.second) == visited.end())
        {
          visited.insert(t.second);
          // obtain the state with minimal rank
          succ_ranks_.emplace_back(t.second, curr_rnk);
        }
        
        // has only one successor in the same SCC
        break;
      }
    }

    // newly incoming states
    for (unsigned p : next_level_)
    {
      if (curr_scc_ != si_.scc_of(p))
        continue;
      // p must not be present previously
      succ_ranks_.emplace_back(p, ++ max_rnk);
    }

    // POST-CONDITION: the ranks in succ_ranks_ is still in ascending order
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
          min_dcc = j;
        }
      }
      else if (has_acc && min_acc == -1)
      {
        // ii. see an accepting transition
        min_acc = j;
      }
    }
    // reorganize the indices, it is already in ascending order
    //std::sort(succ_ranks_.begin(), succ_ranks_.end(), rank_compare);
    for (int k = 0; k < succ_ranks_.size(); k++)
    {
      succ_ranks_[k].second = k;
    }
    // compute the color
    return compute_parity_color(min_acc, min_dcc);
  }

  void determinize_nac_succ::compute_succ()
  {
    // store the minimal new brace
    const int min_new_brace = succ_braces_.size();

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

        // Delete a newincoming state who is already a successor from the same SCC
        next_level_.erase(dst);
        if (t.first)
        {
          // Step A1: Accepting edges generate new braces
          newb = succ_braces_.size();
          // put current brace node.second as the parent of newb
          succ_braces_.emplace_back(node.second);
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

    // New incoming states
    // Top level is 0, if we enter the SCC, we need more braces
    // Order each entry states since each run can have accepting runs
    for (unsigned dst : next_level_)
    {
      if (curr_scc_ != si_.scc_of(dst))
        continue;
      // put them all in top brace 0
      int newb = succ_braces_.size();
      // Step A1
      auto i = succ_nodes.emplace(dst, newb);
      // If the state has not been added, should be always true
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
      state_set states_from_acc_trans;
      std::map<int, int> parent_brace;
      
      for (auto &node : succ_nodes)
      {
        if (node.second >= min_new_brace)
        {
          // this state must come from accepting transition, use a set for canonical order
          states_from_acc_trans.insert(node.first);
          // store the parent
          parent_brace.emplace(node.second, succ_braces_[node.second]);
        }
      }
      // now we need to rearrange the braces in states_from_acc_trans
      // states outside states_from_acc_trans will have braces less than min_new_brace
      int new_brace = min_new_brace;
      for (unsigned dst : states_from_acc_trans)
      {
        int old_brace = succ_nodes[dst];
        succ_nodes[dst] = new_brace;
        // it is guaranteed that the parent is less than min_new_brace
        succ_braces_[new_brace] = parent_brace[old_brace];
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

  // copied from spot
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

    min_dcc = min_dcc != INT_MAX ? min_dcc : -1;
    min_acc = min_acc != INT_MAX ? min_acc : -1;
    return compute_parity_color(min_dcc, min_acc);
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

  spot::acc_cond::acc_code
  make_parity_condition(int base, bool odd, int num_colors)
  {
    assert((num_colors & 1) == odd);
    spot::acc_cond::acc_code res = spot::acc_cond::acc_code::f();

    //    acc-name: parity min even 5
    //    Acceptance: 5 Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))
    // built from right to left
    int start = num_colors - 1;
    int inc = -1;
    int end = -1;
    for (int i = start; i != end; i += inc)
    {
      if ((i & 1) == odd)
        res |= spot::acc_cond::acc_code::inf({(unsigned)(i + base)});
      else
        res &= spot::acc_cond::acc_code::fin({(unsigned)(i + base)});
    }

    return res;
  }

  // ------------- implementation of determinization below -----------------------
  // From a Rank state, looks for a duplicate in the map before
    // creating a new state if needed.
    unsigned
  determinize_tba::new_state(tba_mstate &s)
    {
      tba_mstate dup(s);
      auto p = rank2n_.emplace(dup, 0);
      if (p.second) // This is a new state
      {
        p.first->second = res_->new_state();
        if (show_names_)
          names_->push_back(get_name(p.first->first));
        todo_.emplace_back(dup, p.first->second);
      }
      return p.first->second;
    }

  
    std::string
  determinize_tba::get_name(const tba_mstate &ms)
    {
      // nondeterministic states (including weak states)
      bool first_state = true;
      std::string res = "P=" + get_set_string(ms.weak_set_);
      res += ", O=" + get_set_string(ms.break_set_);
      // now output according SCCs
      for (unsigned i = 0; i < dacs_.size(); i ++)
      {
        unsigned scc_id = dacs_[i];
        std::vector<state_rank> states = ms.dac_ranks_[i];
        res += ",[";
        first_state = true;
        for (unsigned p = 0; p < states.size(); p++)
        {
          if (!first_state)
            res += "<";
          first_state = false;
          res += std::to_string(states[p].first) + ":" + std::to_string(states[p].second);
        }
        res += "] = scc " + std::to_string(scc_id);
      }

      // now output nondeterministic sccs
      for (unsigned i = 0; i < nacs_.size(); i++)
      {
        unsigned scc_id = nacs_[i];
        std::vector<safra_node> states = ms.get_safra_nodes(i);
        res += ",{";
        first_state = true;
        for (unsigned p = 0; p < states.size(); p++)
        {
          if (!first_state)
            res += " ,";
          first_state = false;
          res += std::to_string(states[p].first) + " - [";
          bool first_brace = true;
          for (unsigned b = 0; b < states[p].second.size(); b++)
          {
            if (!first_brace)
              res += " ,";
            first_brace = false;
            res += std::to_string(states[p].second[b]);
          }
          res += "]";
        }
        res += "} = scc " + std::to_string(scc_id);
      }
      return res;
    }

    bool determinize_tba::exists(tba_mstate &s)
    {
      return rank2n_.end() != rank2n_.find(s);
    }

    bool determinize_tba::has_acc_iwcs()
    {
      for (unsigned i = 0; i < scc_types_.size(); i++)
      {
        // if there is an accepting weak SCC
        if ((scc_types_[i] & SCC_WEAK_TYPE) > 0 && (scc_types_[i] & SCC_ACC) > 0)
        {
          return true;
        }
      }
      return false;
    }

    int determinize_tba::get_nac_index(unsigned scc)
    {
      for (int idx = 0; idx < nacs_.size(); idx ++)
      {
        if (nacs_[idx] == scc)
        {
          return idx;
        }
      }
      throw std::runtime_error("determinize_tba::get_nac_index(unsigned scc): index not found");
    }

    int determinize_tba::get_dac_index(unsigned scc)
    {
      for (int idx = 0; idx < dacs_.size(); idx ++)
      {
        if (dacs_[idx] == scc)
        {
          return idx;
        }
      }
      throw std::runtime_error("determinize_tba::get_dac_index(unsigned scc): index not found");
    }

      spot::twa_graph_ptr
  determinize_tba::postprocess(spot::twa_graph_ptr aut)
  {
    spot::scc_info da(aut, spot::scc_info_options::ALL);
    // set of states -> the forest of reachability in the states.
    mstate_equiv_map set2scc;
    // record the representative of every SCC
    for (auto p = rank2n_.begin(); p != rank2n_.end(); p++)
    {
      const state_set set = p->first.get_reach_set();
      // first the set of reached states
      auto val = set2scc.find(set);
      if (val == set2scc.end())
      {
        // the set of macrostates in DPA
        state_set v;
        v.insert(p->second);
        set2scc[set] = v;
      }
      else
      {
        val->second.insert(p->second);
        set2scc[set] = val->second;
      }
    }
    mstate_merger merger(aut, set2scc, da, om_);
    spot::twa_graph_ptr res = merger.run();
    if (om_.get(VERBOSE_LEVEL) >= 1)
      std::cout << "The number of states reduced by mstate_merger: "
                << (aut->num_states() - res->num_states()) << " {out of "
                << aut->num_states() << "}" << std::endl;
    return res;
  }

  void determinize_tba::remove(std::vector<state_rank>& nodes, state_set& to_remove)
  {
      auto it1 = nodes.begin();
      while (it1 != nodes.end())
      {
        auto old_it1 = it1++;
        if (to_remove.find(old_it1->first) != to_remove.end())
        {
          it1 = nodes.erase(old_it1);
        }
      }
  }

  void determinize_tba::merge_redundant_states(tba_mstate &ms, std::vector<state_rank>& nodes, bool nondet)
  {
    auto it1 = nodes.begin();
    while (it1 != nodes.end())
      {
        auto old_it1 = it1++;
        for (auto it2 = nodes.begin(); it2 != nodes.end(); ++it2)
          {
            if (old_it1 == it2)
              continue;
            unsigned i = old_it1->first;
            unsigned j = it2->first;
            if (!(simulator_.simulate(j, i) || delayed_simulator_.simulate(j, i)))
            {
              continue;
            }
            int brace_i = old_it1->second;
            int brace_j = it2->second;
            bool remove = false;
            if (nondet)
            {
              // need to compare there nesting pattern
              unsigned scc_i = si_.scc_of(i);
              int scc_index = get_nac_index(scc_i);
              std::vector<int>& braces = ms.nac_braces_[scc_index];
              //print_pattern_vec(braces, braces.size());
              if (compare_braces(braces, brace_j, brace_i))
              {
                remove = true;
              }
            }else if (brace_j < brace_i)
            {
              remove = true;
            }
            if (remove)
              {
                it1 = nodes.erase(old_it1);
                break;
              }
          }
      }
  }

  void determinize_tba::make_simulation_state(tba_mstate &ms)
  {
    const state_set reached_states = ms.get_reach_set();
      std::vector<state_set> det_remove(dacs_.size(), std::set<unsigned>());
      std::vector<state_set> nondet_remove(nacs_.size(), std::set<unsigned>());
      for (unsigned i : reached_states)
      {
        for (unsigned j : reached_states)
        {
          if (i == j)
            continue;
          unsigned scc_i = si_.scc_of(i);
          // j simulates i and j cannot reach i
          if ((simulator_.simulate(j, i) || delayed_simulator_.simulate(j, i)) && simulator_.can_reach(j, i) == 0)
          {
            if (is_weakscc(scc_types_, scc_i))
            {
              ms.weak_set_.erase(i);
              ms.break_set_.erase(i);
            }else if (is_acepting_detscc(scc_types_, scc_i))
            {
              int index = get_dac_index(scc_i);
              det_remove[index].insert(i);
            }else if (is_accepting_nondetscc(scc_types_, scc_i))
            {
              int index = get_nac_index(scc_i);
              nondet_remove[index].insert(i);
            }
          }
        }
      }
      for (unsigned i = 0; i < det_remove.size(); i ++)
      {
        remove(ms.dac_ranks_[i], det_remove[i]);
        // now remove more
        merge_redundant_states(ms, ms.dac_ranks_[i], false);
      }
      for (unsigned i = 0; i < nondet_remove.size(); i ++)
      {
        remove(ms.nac_ranks_[i], nondet_remove[i]);
        merge_redundant_states(ms, ms.nac_ranks_[i], true);
      }
  }

  void
  determinize_tba::compute_succ(const tba_mstate &ms, bdd letter, tba_mstate &nxt, std::vector<int> &color)
  {
    // std::cout << "current state: " << get_name(ms) << std::endl;
    tba_mstate succ(si_, dacs_.size(), nacs_.size());
    // used for unambiguous automaton
    std::vector<bool> incoming(nb_states_, false);
    std::vector<bool> ignores(nb_states_, false);

    // this function is used for unambiguous NBAs
    auto can_ignore = [&incoming, &ignores](bool use_ambiguous, unsigned dst) -> bool
    {
      if (use_ambiguous)
      {
        if (incoming[dst])
        {
          // this is the second incoming transitions
          ignores[dst] = true;
        }
        else
        {
          incoming[dst] = true;
        }
        return ignores[dst];
      }
      else
      {
        return false;
      }
    };

    std::set<unsigned> acc_weak_coming_states;
    // states at current level
    std::set<unsigned> current_states = ms.get_reach_set();
    // states at next level
    std::vector<std::set<unsigned>> next_nondetstates;
    for (unsigned i = 0; i < nacs_.size(); i++)
    {
      next_nondetstates.emplace_back(state_set());
    }
    std::vector<std::set<unsigned>> next_detstates;
    for (unsigned i = 0; i < dacs_.size(); i++)
    {
      next_detstates.emplace_back(state_set());
    }

    int max_rnk = INT_MAX;

    std::unordered_map<unsigned, std::vector<edge_label>> dac_trans;
    std::unordered_map<unsigned, std::vector<edge_label>> nac_trans;

    //1. first handle inherently weak states
    for (unsigned s : current_states)
    {
      // nondeterministic states or states in nonaccepting SCCs
      bool in_break_set = (ms.break_set_.find(s) != ms.break_set_.end());
      bool in_acc_det = is_acepting_detscc(scc_types_, si_.scc_of(s));
      if (in_acc_det)
      {
        dac_trans.emplace(s, std::vector<edge_label>());
      }
      bool in_acc_nondet = is_accepting_nondetscc(scc_types_, si_.scc_of(s));
      if (in_acc_nondet)
      {
        nac_trans.emplace(s, std::vector<edge_label>());
      }

      for (const auto &t : aut_->out(s))
      {
        if (!bdd_implies(letter, t.cond))
          continue;
        // it is legal to ignore the states have two incoming transitions
        // in unambiguous Buchi automaton
        if (can_ignore(use_unambiguous_, t.dst))
          continue;
        
        unsigned scc_id = si_.scc_of(t.dst);
        // we move the states in accepting det SCC to ordered states
        if (is_acepting_detscc(scc_types_, scc_id))
        {
          int det_scc_index = get_dac_index(scc_id); 
          // incoming states
          next_detstates[det_scc_index].insert(t.dst);
          if (in_acc_det)
          {
            dac_trans[s].emplace_back(t.acc.has(0), t.dst);
          }
        }
        else if (is_weakscc(scc_types_, scc_id))
        {
          // weak states or nondeterministic or nonaccepting det scc
          succ.weak_set_.insert(t.dst);
          // be accepting and weak
          bool in_acc_set = (scc_types_[scc_id] & SCC_ACC) > 0;
          // in breakpoint and it is accepting
          if (in_break_set && in_acc_set)
          {
            succ.break_set_.insert(t.dst);
          }
          // in accepting weak SCCs
          if (in_acc_set)
          {
            acc_weak_coming_states.insert(t.dst);
          }
        }
        else if (is_accepting_nondetscc(scc_types_, scc_id))
        {
          int nondet_scc_index = get_nac_index(scc_id);
          // reached states for each NAC
          next_nondetstates[nondet_scc_index].insert(t.dst);
          if (in_acc_nondet)
          {
            nac_trans[s].emplace_back(t.acc.has(0), t.dst);
          }
        }
        else
        {
          throw std::runtime_error("determinize_tba::compute_succ(): wrong type of SCC");
        }
      }
    }

    //2. Compute the labelling successors for deterministic SCCs
    std::vector<determinize_dac_succ> dac_succs;
    for (unsigned i = 0; i < dacs_.size(); i ++)
    {
      determinize_dac_succ dac_succ(si_, dacs_[i], ms.dac_ranks_[i], next_detstates, succ.dac_ranks_[i], dac_trans);
      dac_succ.compute_succ();
      dac_succs.emplace_back(dac_succ);
    }

    // std::cout << "After deterministic part = " << get_name(succ) << std::endl;
    //3. Compute the successors for nondeterministic SCCs
    std::vector<determinize_nac_succ> nac_succs;
    for (unsigned i = 0; i < nacs_.size(); i ++)
    {
      determinize_nac_succ nac_succ(si_, nacs_[i], ms.nac_ranks_[i], ms.nac_braces_[i], next_nondetstates, succ.nac_ranks_[i], succ.nac_braces_[i], nac_trans, true);
      nac_succ.compute_succ();
      nac_succs.emplace_back(nac_succ);
    }

    // remove redudant states
    if (use_simulation_)
    {
      make_simulation_state(succ);
    }

    bool break_empty = succ.break_set_.empty();
    // now determine the break set
    if (break_empty)
    {
      // if the breakpoint is empty, then fill it with newly-incoming accepting weak SCC states
      std::set<unsigned> result;
      std::set<unsigned> reach_sucss = succ.weak_set_; // copy
      std::set_intersection(reach_sucss.begin(), reach_sucss.end(), acc_weak_coming_states.begin(), acc_weak_coming_states.end(), std::inserter(result, result.begin()));
      succ.break_set_ = result;
    }

    std::vector<int> colors;
    //3. Determine the color on the transition for each accepting deterministic SCC
    // the minimal even color is 2 and the minimal odd color is 1
    for (unsigned i = 0; i < dacs_.size(); i++)
    {
      int parity = dac_succs[i].get_color();
      colors.push_back(parity);
    }

    for (unsigned i = 0; i < nacs_.size(); i++)
    {
      int parity = nac_succs[i].get_color();
      colors.push_back(parity);
    }

    // give color for the weak SCCs
    if (break_empty)
    {
      colors.push_back(1);
    }
    else
    {
      // must be the one that infinitely often
      colors.push_back(2);
    }

    //4. Reorgnize the indices of each accepting deterministic SCC
    //5. Reorganize the indices for each accepting nondeterministic SCC
    // already done in deciding colors
    nxt = succ;
    color = colors;
  }


  // copied and adapted from deterministic.cc in Spot
  void
  determinize_tba::compute_stutter_succ(const tba_mstate &curr, bdd letter, tba_mstate &succ, std::vector<int> &colors)
  {
    tba_mstate ms(curr);

    std::vector<tba_mstate> stutter_path;
    if (use_stutter_ && aut_->prop_stutter_invariant())
    {
      // The path is usually quite small (3-4 states), so it's
      // not worth setting up a hash table to detect a cycle.
      stutter_path.clear();
      std::vector<tba_mstate>::iterator cycle_seed;
      std::vector<int> mincolor(dacs_.size() + nacs_.size() + 1, -1);

      // stutter forward until we cycle
      for (;;)
      {
        // any duplicate value, if any, is usually close to
        // the end, so search backward.
        auto it = std::find(stutter_path.rbegin(),
                            stutter_path.rend(), ms);
        if (it != stutter_path.rend())
        {
          cycle_seed = (it + 1).base();
          break;
        }
        stutter_path.emplace_back(std::move(ms));
        // next state
        tba_mstate tmp_succ(si_, dacs_.size(), nacs_.size());
        std::vector<int> tmp_color(dacs_.size() + nacs_.size() + 1, -1);
        compute_succ(stutter_path.back(), letter, tmp_succ, tmp_color);
        ms = tmp_succ;
        for (unsigned i = 0; i < mincolor.size(); i++)
        {
          if (tmp_color[i] != -1 && mincolor[i] != -1)
          {
            mincolor[i] = std::min(tmp_color[i], mincolor[i]);
          }
          else if (tmp_color[i] != -1 && mincolor[i] == -1)
          {
            mincolor[i] = tmp_color[i];
          }
        }
      }
      // check whether this ms has been seen before
      bool in_seen = exists(*cycle_seed);
      for (auto it = cycle_seed + 1; it < stutter_path.end(); ++it)
      {
        if (in_seen)
        {
          // if *cycle_seed is already in seen, replace
          // it with a smaller state also in seen.
          if (exists(*it) && (*it < *cycle_seed))
            cycle_seed = it;
        }
        else
        {
          // if *cycle_seed is not in seen, replace it
          // either with a state in seen or with a smaller
          // state
          if (exists(*it))
          {
            cycle_seed = it;
            in_seen = true;
          }
          else if (*it < *cycle_seed)
          {
            cycle_seed = it;
          }
        }
      }
      succ = std::move(*cycle_seed);
      colors = mincolor;
    }
    else
    {
      compute_succ(ms, letter, succ, colors);
    }
  }

  void
  determinize_tba::finalize_acceptance()
  {
    std::vector<bool> odds(max_colors_.size(), false);
    for (unsigned i = 0; i < max_colors_.size(); i++)
    {
      if (max_colors_[i] < 0)
        continue;
      // now we make all maximal colors an odd color (the color that cannot be visited infinitely often)
      max_colors_[i] = (max_colors_[i] & 1) ? max_colors_[i] : (max_colors_[i] + 1);
      // make minimal color an even color (no zero by construction, will shift to zero later)
      odds[i] = (min_colors_[i] & 1) > 0;
    }
    // now max_colors_ has the maximal color for each accepting deterministic SCC
    // compute the color base of each SCC
    std::vector<unsigned> color_bases(max_colors_.size(), 0);
    // the size of max_colors must be larger than 0
    int accumulated_colors = 0;
    if (max_colors_.size() > 0)
    {
      accumulated_colors = (max_colors_[0] < 0) ? 0 : max_colors_[0] - min_colors_[0] + 1;
      color_bases[0] = 0;
    }
    for (unsigned i = 1; i < max_colors_.size(); i++)
    {
      if (max_colors_[i] < 0)
        continue;
      color_bases[i] = accumulated_colors;
      accumulated_colors += (max_colors_[i] - min_colors_[i] + 1);
    }
    unsigned weak_base = (unsigned)accumulated_colors;
    bool has_weak = false;
    bool has_weak_acc = has_acc_iwcs();
    for (auto &t : res_->edges())
    {
      auto p = trans2colors_.find(std::make_pair(t.src, t.cond));
      if (p == trans2colors_.end())
      {
        throw std::runtime_error("No outgoing transition found in finalize_acceptance()");
      }
      // the list of colors, including the last one for weak SCCs
      for (unsigned i = 0; i < p->second.size() - 1; i++)
      {
        // if the maximal color is not -1
        if (max_colors_[i] < 0)
          continue;
        // should be set to the maximal odd color
        if (p->second[i] < 0)
        {
          t.acc.set((unsigned)(color_bases[i] + max_colors_[i] - min_colors_[i]));
          // maximal color
        }
        else
        {
          t.acc.set(((unsigned)(color_bases[i] + p->second[i] - min_colors_[i])));
        }
      }
      // has the value of fin
      // empty is 1 and nonempty would be 1
      if (has_weak_acc && (p->second.back() & 1))
      {
        has_weak = true;
        t.acc.set(weak_base);
      }
    }
    // now set up the acceptance
    spot::acc_cond::acc_code acceptance = spot::acc_cond::acc_code::f();
    for (unsigned i = 0; i < max_colors_.size(); i++)
    {
      if (max_colors_[i] < 0)
        continue;
      // max_colors are all odd colors, the biggest one
      acceptance |= make_parity_condition(color_bases[i], odds[i], max_colors_[i] - min_colors_[i] + 1);
    }
    if (has_weak_acc && has_weak)
    {
      acceptance |= spot::acc_cond::acc_code::fin({weak_base});
    }
    unsigned num_sets = has_weak_acc && has_weak ? weak_base + 1 : weak_base;
    // the final one
    res_->set_acceptance(num_sets, acceptance);
  }


  spot::twa_graph_ptr
  determinize_tba::run()
  {
    // todo_ is a queue for handling states
    while (!todo_.empty())
    {
      auto top = todo_.front();
      todo_.pop_front();
      // pop current state, (N, Rnk)
      tba_mstate ms = top.first;

      // Compute support of all available states.
      bdd msupport = bddtrue;
      bdd compact = bddfalse;
      const std::set<unsigned>& reach_set = ms.get_reach_set();
      // compute the occurred variables in the outgoing transitions of ms, stored in msupport
      for (unsigned s : reach_set)
        {
          msupport &= support_[s];
          compact |= compat_[s];
        }

      while (compact != bddfalse)
      {
        bdd letter = bdd_satoneset(compact, msupport, bddfalse);
        compact -= letter;

        // std::cout << "Current state = " << get_name(ms) << " letter = "<< letter << std::endl;
        tba_mstate succ(si_, dacs_.size(), nacs_.size());
        // the number of SCCs we care is the accepting det SCCs and the weak SCCs
        std::vector<int> colors(dacs_.size() + nacs_.size() + 1, -1);
        //compute_labelling_successors(std::move(ms), top.second, letter, succ, color);
        compute_stutter_succ(ms, letter, succ, colors);

        if (succ.is_empty())
          continue;

        unsigned origin = top.second;
        // add transitions
        // Create the automaton states
        unsigned dst = new_state(succ);
        // first add this transition
        res_->new_edge(origin, dst, letter);
        // handle with colors
        for (unsigned i = 0; i < colors.size(); i++)
        {
          // std::cout << "color: " << colors[i] << std::endl;
          if (colors[i] < 0)
            continue;
          int color = colors[i];
          if (i < max_colors_.size())
          {
            max_colors_[i] = std::max(max_colors_[i], color);
            min_colors_[i] = std::min(min_colors_[i], color);
          }
          // record this color
        }
        auto r = trans2colors_.emplace(std::make_pair(origin, letter), colors);
      }
    }
    finalize_acceptance();

    if (aut_->prop_complete().is_true())
      res_->prop_complete(true);
    res_->prop_universal(true);
    res_->prop_state_acc(false);
    if (om_.get(VERBOSE_LEVEL) >= 1)
    {
      output_file(res_, "dpa.hoa");
      std::cout << "Before simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
      if (om_.get(VERBOSE_LEVEL) >= 2) check_equivalence(aut_, res_);
    }
    if (om_.get(USE_SCC_INFO) > 0)
      res_ = postprocess(res_);
    if (om_.get(VERBOSE_LEVEL) >= 1)
    {
      std::cout << "After simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
      output_file(res_, "dpa1.hoa");
      if (om_.get(VERBOSE_LEVEL) >= 2) check_equivalence(aut_, res_);
    }
    simplify_acceptance_here(res_);

    return res_;
  }

}