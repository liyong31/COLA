// Copyright (C) 2017-2019 Laboratoire de Recherche et Développement
// de l'Epita.
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

//#include "optimizer.hpp"
#include "cola.hpp"
#include "simulation.hpp"
#include "types.hpp"
//#include "struct.hpp"

#include <deque>
#include <map>
#include <set>

#include <spot/misc/hashfunc.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/isunamb.hh>
#include <spot/twa/acc.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/misc/bddlt.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/misc/version.hh>
#include <spot/twa/acc.hh>

// Complementation of Buchi automara based on SCC decomposition
// We classify three types of SCCs in the input NBA:
// 1. inherently weak SCCs (IWCs): every cycle in the SCC will not visit accepting transitions or every cycle visits an accepting transition
// 2. deterministic accepting SCCs (DACs): states in the SCC have at most one successor remain in the same SCC for a letter
// 3. nondeterministic accepting SCCs (NACs): has an accepting transition and nondeterministic

namespace cola
{

  // The ranks for each state
  typedef std::pair<unsigned, int> rank;
  // (C, S, B) for complementing DACs
  const int NCSB_C = 2;
  const int NCSB_S = 4;
  const int NCSB_B = 3;

  class complement_mstate
  {
  public:
    // the number of states num, default values, and number of NACs
    complement_mstate(spot::scc_info &si)
        : si_(si)
    {
    }

    complement_mstate(const complement_mstate &other)
        : si_(other.si_)
    {
      this->break_set_.clear();
      this->break_set_.insert(other.break_set_.begin(), other.break_set_.end());
      this->weak_set_.clear();
      this->weak_set_.insert(other.weak_set_.begin(), other.weak_set_.end());

      this->detscc_ranks_ = other.detscc_ranks_; // copy
      this->detscc_index_ = other.detscc_index_;

      this->nondetscc_ranks_ = other.nondetscc_ranks_; // copy
    }

    std::set<unsigned>
    get_reach_set() const;

    std::set<unsigned>
    get_weak_set() const;

    bool is_empty() const;

    int get_max_rank() const;

    bool operator<(const complement_mstate &other) const;
    bool operator==(const complement_mstate &other) const;

    complement_mstate &
    operator=(const complement_mstate &other)
    {
      this->si_ = other.si_;
      this->break_set_.clear();
      this->break_set_.insert(other.break_set_.begin(), other.break_set_.end());
      this->weak_set_.clear();
      this->weak_set_.insert(other.weak_set_.begin(), other.weak_set_.end());

      this->detscc_ranks_ = other.detscc_ranks_;
      this->detscc_index_ = other.detscc_index_;

      this->nondetscc_ranks_ = other.nondetscc_ranks_;

      return *this;
    }

    size_t hash() const;

    // SCC information
    spot::scc_info &si_;
    // 1. NAC states point to its braces
    // Note yet decided
    std::vector<rank> nondetscc_ranks_;

    // 2. DAC states point to its labelling, C = 2, S = 1, B = 0
    std::vector<rank> detscc_ranks_;
    // current scc to be inspect
    int detscc_index_ = 0;
    // 3. IWC states point to RANK_WEAK
    // breakpoint construction for weak accepting SCCs
    std::set<unsigned> weak_set_;
    std::set<unsigned> break_set_;
  };

  struct complement_mstate_hash
  {
    size_t
    operator()(const complement_mstate &s) const noexcept
    {
      return s.hash();
    }
  };

  bool
  complement_mstate::operator<(const complement_mstate &other) const
  {
    if (weak_set_ == other.weak_set_)
    {
      if (break_set_ == other.break_set_)
      {
        if (detscc_ranks_ != other.detscc_ranks_)
        {
            return detscc_ranks_ < other.detscc_ranks_;
        }
        if (detscc_index_ == other.detscc_index_)
        {
          return detscc_index_ < other.detscc_index_;
        }
        if (nondetscc_ranks_ != other.nondetscc_ranks_)
        {
          return nondetscc_ranks_ < other.nondetscc_ranks_;
        }
        return false;
      }
      else
      {
        return break_set_ < other.break_set_;
      }
    }
    else
    {
      return weak_set_ < other.weak_set_;
    }
  }
  bool
  complement_mstate::operator==(const complement_mstate &other) const
  {
    if (this->weak_set_ != other.weak_set_)
    {
      return false;
    }
    if (this->break_set_ != other.break_set_)
    {
      return false;
    }
    if (detscc_ranks_ != other.detscc_ranks_)
      {
        return false;
      }

    if (nondetscc_ranks_ != other.nondetscc_ranks_)
      {
        return false;
      }
    return true;
  }
  int complement_mstate::get_max_rank() const
  {
    return -1;
  }
  std::set<unsigned>
  complement_mstate::get_reach_set() const
  {
    std::set<unsigned> result;
    result.insert(weak_set_.begin(), weak_set_.end());
    for (auto &p : detscc_ranks_)
    {
      result.insert(p.first);
    }
    for (auto &p : nondetscc_ranks_)
    {
        result.insert(p.first);
    }
    return result;
  }
  bool complement_mstate::is_empty() const
  {
    if (!weak_set_.empty())
    {
      return false;
    }
    if (!detscc_ranks_.empty())
    {
      return false;
    }
    if (!nondetscc_ranks_.empty())
    {
      return false;
    }

    return true;
  }

  std::set<unsigned>
  complement_mstate::get_weak_set() const
  {
    return weak_set_;
  }

  size_t
  complement_mstate::hash() const
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
    for (auto &p : detscc_ranks_)
      {
        res ^= (res << 3) ^ (p.first);
        res ^= (res << 3) ^ (p.second);
      }
    for (auto &p : nondetscc_ranks_)
      {
        res ^= (res << 3) ^ (p.first);
        res ^= (res << 3) ^ (p.second);
      }

    return res;
  }

  // complementation Buchi automata
  class tnba_complement
  {
  private:
    // The source automaton.
    const spot::const_twa_graph_ptr aut_;

    // SCCs information of the source automaton.
    spot::scc_info &si_;

    // Number of states in the input automaton.
    unsigned nb_states_;

    // state_simulator
    state_simulator simulator_;

    // delayed simulation
    delayed_simulation delayed_simulator_;

    // The parity automata being built.
    spot::twa_graph_ptr res_;

    // the number of indices
    unsigned sets_ = 0;

    unsigned num_colors_;

    spot::option_map &om_;

    // use ambiguous
    bool use_unambiguous_;

    bool use_scc_;

    // use stutter
    bool use_stutter_;

    bool use_simulation_;

    // Association between labelling states and state numbers of the
    // DPA.
    std::unordered_map<complement_mstate, unsigned, complement_mstate_hash> rank2n_;

    // States to process.
    std::deque<std::pair<complement_mstate, unsigned>> todo_;

    // Support for each state of the source automaton.
    std::vector<bdd> support_;

    // Propositions compatible with all transitions of a state.
    std::vector<bdd> compat_;

    // is accepting for states
    std::vector<bool> is_accepting_;

    // Whether a SCC is deterministic or not
    std::string scc_types_;

    // State names for graphviz display
    std::vector<std::string> *names_;

    // the index of each deterministic accepting SCCs
    std::vector<unsigned> acc_detsccs_;
    // the index of each deterministic accepting SCCs
    std::vector<unsigned> acc_nondetsccs_;

    // Show Rank states in state name to help debug
    bool show_names_;

    // maximal ranking in a labelling
    const int MAX_RANK_;

    std::string
    get_rank_string(const std::vector<rank>& states)
    {
      std::string res = "C = {";
      bool first_state = true;
        for (unsigned p = 0; p < states.size(); p++)
        {
          if (!(states[p].second & NCSB_C))
            continue;
          if (!first_state)
            res += ", ";
          first_state = false;
          res += std::to_string(states[p].first);
        }
        res += "}";
        res += ", S = {";
        first_state = true;
        for (unsigned p = 0; p < states.size(); p++)
        {
          if (states[p].second != NCSB_S)
            continue;
          if (!first_state)
            res += ", ";
          first_state = false;
          res += std::to_string(states[p].first);
        }
        res += "}";
        res += ", B = {";
        first_state = true;
        for (unsigned p = 0; p < states.size(); p++)
        {
          if (states[p].second != NCSB_B)
            continue;
          if (!first_state)
            res += ", ";
          first_state = false;
          res += std::to_string(states[p].first);
        }
        res += "}";
        return res;
    }

    std::string
    get_name(const complement_mstate &ms)
    {
      // nondeterministic states (including weak states)
      bool first_state = true;
      std::string res = "P=" + get_set_string(ms.weak_set_);
      res += ", O=" + get_set_string(ms.break_set_);
      // now output according SCCs
      std::vector<rank> states = ms.detscc_ranks_;
        res += ", " + get_rank_string(states);
        res += ", scc = " + std::to_string(ms.detscc_index_);

      // now output nondeterministic sccs
      // for (unsigned i = 0; i < acc_nondetsccs_.size(); i++)
      // {
      //   unsigned scc_id = acc_nondetsccs_[i];
      //   std::vector<safra_node> states = ms.get_safra_nodes(i);
      //   res += ",{";
      //   first_state = true;
      //   for (unsigned p = 0; p < states.size(); p++)
      //   {
      //     if (!first_state)
      //       res += " ,";
      //     first_state = false;
      //     res += std::to_string(states[p].first) + " - [";
      //     bool first_brace = true;
      //     for (unsigned b = 0; b < states[p].second.size(); b++)
      //     {
      //       if (!first_brace)
      //         res += " ,";
      //       first_brace = false;
      //       res += std::to_string(states[p].second[b]);
      //     }
      //     res += "]";
      //   }
      //   res += "} = scc " + std::to_string(scc_id);
      // }
      return res;
    }
    // From a Rank state, looks for a duplicate in the map before
    // creating a new state if needed.
    unsigned
    new_state(complement_mstate &s)
    {
      complement_mstate dup(s);
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

    bool exists(complement_mstate &s)
    {
      return rank2n_.end() != rank2n_.find(s);
    }

    void remove_rank(std::vector<rank> &nodes, std::set<unsigned> &to_remove)
    {
      std::vector<rank> tmp;
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

    void merge_redundant_states(complement_mstate &ms, std::vector<rank> &nodes, bool nondet)
    {
      // auto it1 = nodes.begin();
      // while (it1 != nodes.end())
      // {
      //   auto old_it1 = it1++;
      //   for (auto it2 = nodes.begin(); it2 != nodes.end(); ++it2)
      //   {
      //     if (old_it1 == it2)
      //       continue;
      //     unsigned i = old_it1->first;
      //     unsigned j = it2->first;
      //     if (!(simulator_.simulate(j, i) || delayed_simulator_.simulate(j, i)))
      //     {
      //       continue;
      //     }
      //     int brace_i = old_it1->second;
      //     int brace_j = it2->second;
      //     bool remove = false;
      //     if (nondet)
      //     {
      //       // need to compare there nesting pattern
      //       unsigned scc_i = si_.scc_of(i);
      //       int scc_index = get_nondetscc_index(scc_i);
      //       std::vector<int> &braces = ms.nondetscc_breaces_[scc_index];
      //       // std::cout << "State " << i << " brace: " << brace_i << std::endl;
      //       // std::cout << "State " << j << " brace: " << brace_j << std::endl;
      //       //print_pattern_vec(braces, braces.size());
      //       if (compare_braces(braces, brace_j, brace_i))
      //       {
      //         remove = true;
      //       }
      //     }
      //     else if (brace_j < brace_i)
      //     {
      //       remove = true;
      //     }
      //     if (remove)
      //     {
      //       it1 = nodes.erase(old_it1);
      //       break;
      //     }
      //   }
      // }
    }

    // remove a state i if it is simulated by a state j
    void
    make_simulation_state(complement_mstate &ms, std::set<unsigned>& level_states, std::vector<std::vector<rank>>& det_succs, std::vector<std::vector<rank>>& nondet_succs)
    {
      std::set<unsigned> det_remove;
      std::set<unsigned> nondet_remove;
      for (unsigned i : level_states)
      {
        for (unsigned j : level_states)
        {
          if (i == j)
            continue;
          unsigned scc_i = si_.scc_of(i);
          // j simulates i and j cannot reach i
          if ((simulator_.simulate(j, i) || delayed_simulator_.simulate(j, i)) && simulator_.can_reach(j, i) == 0)
          {
            // std::cout << j << " simulated " << i << std::endl;
            // std::cout << "can_reach = " << simulator_.can_reach(j, i) << std::endl;
            if (is_weakscc(scc_types_, scc_i))
            {
              ms.weak_set_.erase(i);
              ms.break_set_.erase(i);
            }
            else if (is_acepting_detscc(scc_types_, scc_i))
            {
              det_remove.insert(i);
            }
            else if (is_accepting_nondetscc(scc_types_, scc_i))
            {
              nondet_remove.insert(i);
            }
          }
        }
      }
      for (std::vector<rank>& succ: det_succs)
      {
        remove_rank(succ, det_remove);
      }
      // for (unsigned i = 0; i < det_remove.size(); i++)
      // {
      //   remove_label(ms.detscc_labels_[i], det_remove[i]);
      //   // now remove more
      //   merge_redundant_states(ms, ms.detscc_labels_[i], false);
      // }
      // for (unsigned i = 0; i < nondet_remove.size(); i++)
      // {
      //   remove_label(ms.nondetscc_labels_[i], nondet_remove[i]);
      //   merge_redundant_states(ms, ms.nondetscc_labels_[i], true);
      // }
    }

    void
    csb_successors(const std::vector<rank> &curr_det_states, int scc_index, std::vector<int>& next_scc_indices, std::vector<std::map<unsigned, int>> &succ_maps
    , std::vector<bool>& acc_succs, std::set<unsigned> &next_detstates, std::unordered_map<unsigned, std::vector<std::pair<bool, unsigned>>> &det_cache)
    {
      // std::cout << "csb_successor scc " << scc_index << " rank: " << get_rank_string(curr_det_states) << std::endl;
      //1. Handle S states.
      // Treated first because we can escape early if the letter
      // leads to an accepting transition for a Safe state.
      // std::vector<std::map<unsigned, int>> succ_maps;
      std::map<unsigned, int> succ_nodes;
      for (unsigned i = 0; i < curr_det_states.size(); ++i)
      {
        // ignore other states
        if (curr_det_states[i].second != NCSB_S)
          continue;
        
        unsigned curr_s = curr_det_states[i].first;
        // std::cout << "S curr_s: " << curr_s << std::endl;
        for (auto& p : det_cache[curr_s])
        {
          // only care about the transitions in the same SCC
          if (si_.scc_of(curr_s) != si_.scc_of(p.second))
          {
            continue;
          }
          // accepting state or accepting transition, abort
          if (p.first || is_accepting_[p.second])
            // Exit early; accepting transition is forbidden for safe state.
            return;
          // std::cout << "S succ: " << p.second << std::endl;
          // states are already safe will stay safe forever
          next_detstates.erase(p.second);
          succ_nodes[p.second] = NCSB_S;
          // No need to look for other compatible transitions
          // for this state; it's in the deterministic in the same SCC
          break;
        }
      }

      std::set<unsigned> scc_indices;
      //2. Handle C states.
      for (unsigned i = 0; i < curr_det_states.size(); ++i)
      {
        // including B-states
        if (!(curr_det_states[i].second & NCSB_C))
          continue;

        unsigned curr_s = curr_det_states[i].first;
        // std::cout << "C curr_s: " << curr_s << std::endl;
        for (auto& p : det_cache[curr_s])
        {
          // only care about the transitions in the same SCC
          if (si_.scc_of(curr_s) != si_.scc_of(p.second))
          {
            continue;
          }

          next_detstates.erase(p.second);
          // Ignore states that goes to S
          if (succ_nodes.find(p.second) == succ_nodes.end())
          {
            // std::cout << "C succ: " << p.second << std::endl;
            succ_nodes[p.second] = NCSB_C;
            scc_indices.insert(si_.scc_of(p.second));
          }
          break;
        }
      }

      //3. Handle incoming states.
      for (unsigned p : next_detstates)
      {
        if (succ_nodes.find(p) == succ_nodes.end())
        {
          // all incoming states will be set in C
          succ_nodes[p] = NCSB_C;
          // std::cout << "C incoming curr_s: " << p << std::endl;
          scc_indices.insert(si_.scc_of(p));
        }
      }

      //4. Handle B-states
      bool is_pre_b_empty = true;
      bool is_b_empty = true;
      for (unsigned i = 0; i < curr_det_states.size(); ++i)
      {
        // including B-states
        if (curr_det_states[i].second != NCSB_B)
          continue;
        
        is_pre_b_empty = false;
        unsigned curr_s = curr_det_states[i].first;
        for (auto& p : det_cache[curr_s])
        {
          if (si_.scc_of(curr_s) != si_.scc_of(p.second))
          {
            continue;
          }
          if (succ_nodes[p.second] == NCSB_C)
          {
            // std::cout << "B succ: " << p.second << std::endl;
            succ_nodes[p.second] = NCSB_B;
            is_b_empty = false;
          }
          break;
        }
      }
      
      int curr_scc_index;
      if (is_pre_b_empty)
      {
        // the DACs has just been reached
        curr_scc_index = ((int)acc_detsccs_.size()) - 1;
      }else 
      {
        curr_scc_index = scc_index;
      }
      // std::cout << "curr_scc_index = " << curr_scc_index << std::endl;

      int next_scc_index;
      // round rabin strategy for next DAC, we should select existing one if it is not 0
      if (curr_scc_index == 0)
      {
        next_scc_index = acc_detsccs_.size() - 1;
      }else 
      {
        next_scc_index = curr_scc_index - 1;
      }
      // std::cout << "next_scc_index: " << next_scc_index << std::endl;
      unsigned curr_scc = acc_detsccs_[next_scc_index];
      // std::cout << "Current scc: " << curr_scc << std::endl;
      
      if (next_scc_index != 0 && scc_indices.find(curr_scc) == scc_indices.end())
      {
        // need to find an index inside scc_indices
        int max_lower = -1;
        int max_upper = -1;
        // already sorted
        for (unsigned index : scc_indices)
        {
          if (index < curr_scc)
          {
            max_lower = std::max(max_lower, (int)index);
          }
          if (index > curr_scc)
          {
            max_upper = std::max(max_upper, (int)index);
          }
        }
        // std::cout << "C scc: " << get_set_string(scc_indices) << std::endl;
        // std::cout << "max_lower = " << max_lower << " max_upper = " << max_upper << std::endl;
        if (max_lower != -1)
        {
          next_scc_index = get_detscc_index(max_lower);
        }else if (max_upper != -1)
        {
          next_scc_index = get_detscc_index(max_upper);
        }else 
        {
          // C' maybe empty, so set it to 0
          next_scc_index = 0;
        }
      }
      std::map<unsigned, int> tmp(succ_nodes);
      //5. Now add the first successor
      // std::cout << "is_b_empty: " << is_b_empty << std::endl;
      if (is_b_empty)
      {
        acc_succs.emplace_back(true);
        // round rabin for checking next DAC
        for (auto & p : succ_nodes)
        {
          if (p.second == NCSB_C && si_.scc_of(p.first) == acc_detsccs_[next_scc_index])
          {
            tmp[p.first] = NCSB_B;
          }
        }
        next_scc_indices.emplace_back(next_scc_index);
      }else 
      {
        acc_succs.emplace_back(false);
        next_scc_indices.emplace_back(scc_index);
      }
      // std::cout << "Add first map: " << std::endl;
      // for (auto & p : tmp)
      // {
      //   std::cout << "s = " << p.first << " r = " << p.second << std::endl;
      // }
      succ_maps.emplace_back(tmp);

      //6. MaxRank in Ondra's paper, another successor
      if (! is_b_empty )
      {
        for (auto & p : succ_nodes)
        {
          // B' has accepting states
          if (is_accepting_[p.first] && p.second == NCSB_B)
          {
            is_b_empty = true;
            break;
          }
        }
      }
      if (! is_b_empty)
      {
        std::map<unsigned, int> tmp2(succ_nodes);
        for (auto & p : succ_nodes)
        {
          // Move all B'-states to S
          if (p.second == NCSB_B)
          {
            tmp2[p.first] = NCSB_S;
          }
        }
        for (auto & p : succ_nodes)
        {
          // Move all B'-states to S
          if (p.second == NCSB_C && si_.scc_of(p.first) == acc_detsccs_[next_scc_index])
          {
            tmp2[p.first] = NCSB_B;
          }
        }
        // std::cout << "Add second map: " << std::endl;
        // for (auto & p : tmp2)
        // {
        //   std::cout << "s = " << p.first << " r = " << p.second << std::endl;
        // }
        succ_maps.emplace_back(tmp2);
        acc_succs.emplace_back(true);
        next_scc_indices.emplace_back(next_scc_index);
      }
    }

    // adapted CSB complementation, every part may have at most two successors
    void det_succ(const complement_mstate &ms
    , std::vector<std::vector<rank>> &succs
    , std::vector<bool>& acc_succs
    , std::vector<int>& next_scc_index
    , std::set<unsigned> &next_detstates
    , std::unordered_map<unsigned, std::vector<std::pair<bool, unsigned>>> &det_cache)
    {
      std::vector<std::map<unsigned, int>> succ_maps;
      csb_successors(ms.detscc_ranks_, ms.detscc_index_, next_scc_index, succ_maps, acc_succs, next_detstates, det_cache);
      // std::cout << "map size: " << succ_maps.size() << std::endl;
      for (unsigned i = 0; i < succ_maps.size(); i ++)
      {
        std::vector<rank> succ;
        for (auto & p : succ_maps[i])
        {
          succ.emplace_back(p.first, p.second);
        }
        // std::cout << "next " << next_scc_index[i] << " rank: " << get_rank_string(succ) << std::endl;
        succs.emplace_back(succ);
      }
    }

    // compute the successor P={nondeterministic states and nonaccepting SCCs} O = {breakpoint for weak SCCs}
    // and labelling states for each SCC
    void
    compute_successors(const complement_mstate &ms, unsigned origin, bdd letter)
    {
      // std::cout << "current state: " << get_name(ms) << " src: " << origin << " letter: " << letter << std::endl;
      complement_mstate succ(si_);
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

      std::set<unsigned> level_states;
      std::set<unsigned> acc_weak_coming_states;
      // states at current level
      std::set<unsigned> current_states = ms.get_reach_set();
      // states at next level
      std::set<unsigned> next_nondetstates;
      std::set<unsigned> next_detstates;
      
      // deterministic transitions
      std::unordered_map<unsigned, std::vector<std::pair<bool, unsigned>>> det_cache;
      // nondeterministic transitions
      std::unordered_map<unsigned, std::vector<std::pair<bool, unsigned>>> nondet_cache;

      //1. first handle inherently weak states
      for (unsigned s : current_states)
      {
        // nondeterministic states or states in nonaccepting SCCs
        bool in_break_set = (ms.break_set_.find(s) != ms.break_set_.end());
        bool in_acc_det = is_acepting_detscc(scc_types_, si_.scc_of(s));
        if (in_acc_det)
        {
          det_cache.emplace(s, std::vector<std::pair<bool, unsigned>>());
        }
        bool in_acc_nondet = is_accepting_nondetscc(scc_types_, si_.scc_of(s));
        if (in_acc_nondet)
        {
          nondet_cache.emplace(s, std::vector<std::pair<bool, unsigned>>());
        }
        for (const auto &t : aut_->out(s))
        {
          if (!bdd_implies(letter, t.cond))
            continue;
          // it is legal to ignore the states have two incoming transitions
          // in unambiguous Buchi automaton
          if (can_ignore(use_unambiguous_, t.dst))
            continue;
          level_states.insert(t.dst);
          unsigned scc_id = si_.scc_of(t.dst);
          // we move the states in accepting det SCC to ordered states
          if (is_acepting_detscc(scc_types_, scc_id))
          {
            next_detstates.insert(t.dst);
            if (in_acc_det)
            {
              det_cache[s].emplace_back(t.acc.has(0), t.dst);
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
           //
           assert(false);
          }
          else
          {
            assert(false);
          }
        }
      }
      // std::cout << "det: " << get_set_string(next_detstates) << std::endl;
      // std::cout << "nondet: " << get_set_string(next_nondetstates) << std::endl;
      // std::cout << "After weak: " << get_name(succ) << std::endl;
      //2. Compute the successors in deterministic SCCs
      std::vector<std::vector<rank>> det_successors;
      std::vector<bool> det_acc_successors;
      std::vector<int> next_scc_index;
      if (!ms.detscc_ranks_.empty() || !next_detstates.empty()) 
        det_succ(ms, det_successors, det_acc_successors, next_scc_index, next_detstates, det_cache);
      // std::cout << "After det_succ " << std::endl;
      if (!ms.detscc_ranks_.empty() && det_successors.empty())
      {
        return ;
      }
      // std::cout << "After deterministic part = " << get_name(succ) << std::endl;
      //3. Compute the successors for nondeterministic SCCs
      std::vector<std::vector<rank>> nondet_successors;
      // compute_nondeterministic_successors(ms, succ, next_nondetstates, nondet_cache);
      // std::cout << "After nondeterministic part = " << get_name(succ) << std::endl;

      // remove redudant states
      if (use_simulation_)
      {
        make_simulation_state(succ, level_states, det_successors, nondet_successors);
        //merge_redundant_states(succ, det_successors, nondet_successors);
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
      if (det_successors.size() > 0)
      {
        succ.detscc_index_ = next_scc_index[0];
        succ.detscc_ranks_ = det_successors[0];
      }

      unsigned dst = new_state(succ);

      // std::cout << "First deterministic part = " << get_name(succ) << std::endl;

      
      spot::acc_cond::mark_t acc1 = {};
      
      if (break_empty)
      {
        acc1.set(0);
        sets_ = std::max((unsigned)0, sets_);
      }
      // if has no successors or has successors 
      // std::cout << "acc succ: " << det_acc_successors.size() << " det_succ " << det_successors.size() << std::endl;
      if (succ.detscc_ranks_.empty() || det_acc_successors[0] && next_scc_index[0] == 0)
      {
        acc1.set(1);
        sets_ = std::max((unsigned)1, sets_);
      }
      res_->new_edge(origin, dst, letter, acc1);
      
      // whether we need to add another one
      if (det_successors.size() <= 1)
      {
        return ;
      }
      
      complement_mstate succ1(si_);
      succ1.weak_set_ = succ.weak_set_;
      succ1.break_set_ = succ.break_set_;
      succ1.detscc_index_ = next_scc_index[1];
      succ1.detscc_ranks_ = det_successors[1];
      // std::cout << "Second deterministic part = " << get_name(succ1) << std::endl;

      dst = new_state(succ1);
      
      spot::acc_cond::mark_t acc2 = {};
      
      if (break_empty)
      {
        acc2.set(0);
        sets_ = std::max((unsigned)0, sets_);
      }
      // if acc and index is 0
      if (det_acc_successors[1] && next_scc_index[1] == 0)
      {
        acc2.set(1);
        sets_ = std::max((unsigned)1, sets_);
      }
      res_->new_edge(origin, dst, letter, acc2);
    
    }
   
    int get_nondetscc_index(unsigned scc)
    {
      for (int idx = 0; idx < acc_nondetsccs_.size(); idx++)
      {
        if (acc_nondetsccs_[idx] == scc)
        {
          return idx;
        }
      }
      return -1;
    }
    int get_detscc_index(unsigned scc)
    {
      for (int idx = 0; idx < acc_detsccs_.size(); idx++)
      {
        if (acc_detsccs_[idx] == scc)
        {
          return idx;
        }
      }
      return -1;
    }

  public:
    tnba_complement(const spot::const_twa_graph_ptr &aut, spot::scc_info &si, spot::option_map &om, std::vector<bdd> &implications)
        : aut_(aut),
          om_(om),
          use_simulation_(om.get(USE_SIMULATION) > 0),
          use_scc_(om.get(USE_SCC_INFO) > 0),
          use_stutter_(om.get(USE_STUTTER) > 0),
          use_unambiguous_(om.get(USE_UNAMBIGUITY) > 0),
          si_(si),
          nb_states_(aut->num_states()),
          support_(nb_states_),
          compat_(nb_states_),
          is_accepting_(aut->num_states(), false),
          MAX_RANK_(aut->num_states() + 2),
          simulator_(aut, si, implications, om.get(USE_SIMULATION) > 0),
          delayed_simulator_(aut, om),
          show_names_(om.get(VERBOSE_LEVEL) >= 1)
    {
      if (om.get(VERBOSE_LEVEL) >= 2)
      {
        simulator_.output_simulation();
      }
      res_ = spot::make_twa_graph(aut->get_dict());
      res_->copy_ap_of(aut);
      res_->prop_copy(aut,
                      {
                          false,        // state based
                          false,        // inherently_weak
                          false, false, // deterministic
                          true,         // complete
                          false         // stutter inv
                      });
      // Generate bdd supports and compatible options for each state.
      // Also check if all its transitions are accepting.
      for (unsigned i = 0; i < nb_states_; ++i)
      {
        bdd res_support = bddtrue;
        bdd res_compat = bddfalse;
        bool accepting = true;
        bool has_transitions = false;
        for (const auto &out : aut->out(i))
        {
          has_transitions = true;
          res_support &= bdd_support(out.cond);
          res_compat |= out.cond;
          if (!out.acc)
            accepting = false;
        }
        support_[i] = res_support;
        compat_[i] = res_compat;
        is_accepting_[i] = accepting && has_transitions;
      }
      // obtain the types of each SCC
      scc_types_ = get_scc_types(si_);
      // std::cout << "scc types : " << scc_types_ << " " << scc_types_.size() << std::endl;
      // find out the DACs and NACs
      for (unsigned i = 0; i < scc_types_.size(); i++)
      {
        // ignore weak types
        if ((scc_types_[i] & SCC_WEAK_TYPE))
          continue;
        // max_colors_.push_back(-1);
        // min_colors_.push_back(INT_MAX);
        // accepting deterministic scc
        if (is_acepting_detscc(scc_types_, i))
        {
          acc_detsccs_.push_back(i);
        }
        else if (is_accepting_nondetscc(scc_types_, i))
        {
          // accepting nondeterministic scc
          acc_nondetsccs_.push_back(i);
        }
      }

      // optimize with the fact of being unambiguous
      use_unambiguous_ = use_unambiguous_ && is_unambiguous(aut);
      if (show_names_)
      {
        names_ = new std::vector<std::string>();
        res_->set_named_prop("state-names", names_);
      }

      // we only handle one initial state
      unsigned init_state = aut->get_init_state_number();
      complement_mstate new_init_state(si_);
      unsigned init_scc = si_.scc_of(init_state);
      new_init_state.detscc_index_ = 0;
      if ((scc_types_[init_scc] & SCC_WEAK_TYPE))
      {
        new_init_state.weak_set_.insert(init_state);
      }
      else if (is_acepting_detscc(scc_types_, init_scc))
      {
        // now it is in DAC
        int init_scc_index = get_detscc_index(init_scc);
        new_init_state.detscc_index_ = init_scc_index;
        // move to C and B
        new_init_state.detscc_ranks_.emplace_back(init_state, NCSB_B);
      }
      else if (is_accepting_nondetscc(scc_types_, init_scc))
      {
        // initialize the safra_node
        // int init_scc_index = get_nondetscc_index(init_scc);
        // assert(init_scc_index != -1);
        // new_init_state.nondetscc_labels_[init_scc_index].emplace_back(init_state, 0);
        // new_init_state.nondetscc_breaces_[init_scc_index].emplace_back(RANK_TOP_BRACE);
      }
      // we assume that the initial state is not in deterministic part
      res_->set_init_state(new_state(new_init_state));
    }

    spot::twa_graph_ptr
    run()
    {
      // Main stuff happens here
      // todo_ is a queue for handling states
      unsigned sink = INT_MAX;

      while (!todo_.empty())
      {
        auto top = todo_.front();
        todo_.pop_front();
        // pop current state, (N, Rnk)
        complement_mstate ms = top.first;

        // Compute support of all available states.
        bdd msupport = bddtrue;
        bdd n_s_compat = bddfalse;
        const std::set<unsigned> &reach_set = ms.get_reach_set();
        // compute the occurred variables in the outgoing transitions of ms, stored in msupport
        for (unsigned s : reach_set)
        {
          msupport &= support_[s];
          n_s_compat |= compat_[s];
        }

        bdd all = n_s_compat;
        if (all != bddtrue)
        {
          // direct the rest to sink state
          complement_mstate succ(si_);
          sink = new_state(succ);
          // empty state use 0 as well as the weak ones
          res_->new_edge(top.second, sink, !all);
        }
        while (all != bddfalse)
        {
          bdd letter = bdd_satoneset(all, msupport, bddfalse);
          all -= letter;
          // std::cout << "Current state = " << get_name(ms) << " letter = "<< letter << std::endl;
          // the number of SCCs we care is the accepting det SCCs and the weak SCCs
          compute_successors(ms, top.second, letter);
        }
      }
      // amend the edges
      if (sink < res_->num_states())
      {
        for (auto& t : res_->out(sink))
        {
          if (t.dst == sink)
          {
            for (unsigned c = 0; c <= sets_; c ++)
            {
              t.acc.set(c);
            }
          }
        }
      }
      
      // set up the acceptance
      res_->set_generalized_buchi(sets_ + 1);
      if (aut_->prop_complete().is_true())
        res_->prop_complete(true);
      // res_->prop_universal(true);
      res_->prop_state_acc(false);
      if (om_.get(VERBOSE_LEVEL) >= 1)
      {
        output_file(res_, "nba.hoa");
        std::cout << "Before simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
        if (om_.get(VERBOSE_LEVEL) >= 2)
        {
          spot::twa_graph_ptr dual = spot::complement(aut_);
          check_equivalence(dual, res_);
        }
      }
      // if (om_.get(USE_SCC_INFO) > 0)
      //   res_ = postprocess(res_);
      // if (om_.get(VERBOSE_LEVEL) >= 1)
      // {
      //   std::cout << "After simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
      //   output_file(res_, "dpa1.hoa");
      //   if (om_.get(VERBOSE_LEVEL) >= 2)
      //     check_equivalence(aut_, res_);
      // }
      simplify_acceptance_here(res_);

      return res_;
    }
  };

  spot::twa_graph_ptr
  complement_tnba(const spot::const_twa_graph_ptr &aut, spot::option_map &om)
  {
    if (!aut->acc().is_buchi() || !is_elevator_automaton(aut))
      throw std::runtime_error("complement_tnba() requires a Buchi input");
    const int trans_pruning = om.get(NUM_TRANS_PRUNING);
    // now we compute the simulator
    spot::const_twa_graph_ptr aut_reduced;
    std::vector<bdd> implications;
    spot::twa_graph_ptr aut_tmp = nullptr;
    if (om.get(USE_SIMULATION) > 0)
    {
      aut_tmp = spot::scc_filter(aut);
      auto aut2 = spot::simulation(aut_tmp, &implications, trans_pruning);
      aut_tmp = aut2;
    }
    if (aut_tmp)
      aut_reduced = aut_tmp;
    else
      aut_reduced = aut;
    spot::scc_info scc(aut_reduced, spot::scc_info_options::ALL);
    auto det = cola::tnba_complement(aut_reduced, scc, om, implications);
    return det.run();
  }
}