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

//#include "optimizer.hpp"
#include "cola.hpp"
#include "simulation.hpp"
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

#include <spot/parseaut/public.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/misc/version.hh>
#include <spot/twa/acc.hh>

#include <types.hpp>

// Compositional determinization of Buchi automara based on SCC decomposition
// We classify three types of SCCs in the input NBA:
// 1. inherently weak SCCs (IWCs): every cycle in the SCC will not visit accepting transitions or every cycle visits an accepting transition
// 2. deterministic accepting SCCs (DACs): states in the SCC have at most one successor remain in the same SCC for a letter
// 3. nondeterministic accepting SCCs (NACs): has an accepting transition and nondeterministic

namespace cola
{
  // for missing states
  const int RANK_MISSING = -3;
  // for weak states
  const int RANK_WEAK = -2;
  // top brace for nondeterministic accepting SCC-states
  const int RANK_TOP_BRACE = -1;

  // state and the labelling value
  typedef std::pair<unsigned, int> label;
  typedef std::pair<unsigned, bdd> outgoing_trans;
  // a state and its labelling (list of integers)
  typedef std::pair<unsigned, std::vector<int>> safra_node;

  void print_pattern_vec(const std::vector<int>& res, unsigned len)
  {
    for (unsigned i = 0; i < len; i ++)
    {
      std::cout << " " << res[i];
    }
    std::cout << "\n";
  }
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
        size_a ++;
      }
      else
      {
        b_pattern.emplace_back(b);
        // go to the parent
        b = braces[b];
        size_b ++;
      }
    }
    return nesting_cmp(a_pattern, b_pattern);
  }

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

  struct
  {
    size_t
    operator()(label &p1, label &p2) const noexcept
    {
      if (p1.second == p2.second)
      {
        return p1.first < p2.first;
      }
      return p1.second < p2.second;
    }
  } label_compare;

  class tnba_mstate
  {
  public:
    // the number of states num, default values, and number of NACs
    tnba_mstate(spot::scc_info &si, size_t num, int value, unsigned num_nondet_acc_sccs)
        : si_(si), ordered_states_(num, value)
    {
      for (unsigned i = 0; i < num_nondet_acc_sccs; i++)
      {
        std::vector<int> braces;
        nondetscc_breaces_.push_back(braces);
      }
    }

    tnba_mstate(const tnba_mstate &other)
        : si_(other.si_)
    {
      this->ordered_states_.clear();
      for (unsigned i = 0; i < other.ordered_states_.size(); i++)
      {
        this->ordered_states_.push_back(other.ordered_states_[i]);
      }
      this->break_set_.clear();
      this->break_set_.insert(other.break_set_.begin(), other.break_set_.end());
      this->nondetscc_breaces_.clear();
      for (unsigned i = 0; i < other.nondetscc_breaces_.size(); i++)
      {
        std::vector<int> braces;
        for (unsigned j = 0; j < other.nondetscc_breaces_[i].size(); j++)
        {
          braces.push_back(other.nondetscc_breaces_[i][j]);
        }
        this->nondetscc_breaces_.push_back(braces);
      }
    }

    std::set<unsigned>
    get_reach_set() const;

    std::set<unsigned>
    get_weak_set() const;

    bool is_empty() const;

    int get_max_rank() const;

    std::vector<label>
    get_scc_states(unsigned scc) const;

    std::vector<int>
    get_nondet_braces(unsigned ith_nondet_scc) const;

    std::vector<safra_node>
    get_safra_nodes(unsigned scc, unsigned index) const;

    bool operator<(const tnba_mstate &other) const;
    bool operator==(const tnba_mstate &other) const;

    tnba_mstate &
    operator=(const tnba_mstate &other)
    {
      this->si_ = other.si_;
      this->ordered_states_.clear();
      for (unsigned i = 0; i < other.ordered_states_.size(); i++)
      {
        this->ordered_states_.push_back(other.ordered_states_[i]);
      }
      this->break_set_.clear();
      this->break_set_.insert(other.break_set_.begin(), other.break_set_.end());
      this->nondetscc_breaces_.clear();
      for (unsigned i = 0; i < other.nondetscc_breaces_.size(); i++)
      {
        std::vector<int> braces;
        for (unsigned j = 0; j < other.nondetscc_breaces_[i].size(); j++)
        {
          braces.push_back(other.nondetscc_breaces_[i][j]);
        }
        this->nondetscc_breaces_.push_back(braces);
      }
      return *this;
    }

    size_t hash() const;

    // SCC information
    spot::scc_info &si_;
    // 1. NAC states point to its braces
    // 2. DAC states point to its labelling
    // 3. IWC states point to RANK_WEAK
    std::vector<int> ordered_states_;
    // the braces for each NAC
    std::vector<std::vector<int>> nondetscc_breaces_;
    // breakpoint construction for weak accepting SCCs
    std::set<unsigned> break_set_;
  };

  struct tnba_mstate_hash
  {
    size_t
    operator()(const tnba_mstate &s) const noexcept
    {
      return s.hash();
    }
  };

  bool
  tnba_mstate::operator<(const tnba_mstate &other) const
  {
    if (ordered_states_ == other.ordered_states_)
    {
      if (break_set_ == other.break_set_)
      {
        // equal size
        unsigned minsize = nondetscc_breaces_.size();
        for (unsigned i = 0; i < minsize; i++)
        {
          if (nondetscc_breaces_[i] == other.nondetscc_breaces_[i])
          {
            continue;
          }
          else
          {
            return nondetscc_breaces_[i] < other.nondetscc_breaces_[i];
          }
        }
        return false;
      }
      else
      {
        return break_set_ < other.break_set_;
      }
    }
    return ordered_states_ < other.ordered_states_;
  }
  bool
  tnba_mstate::operator==(const tnba_mstate &other) const
  {
    if (ordered_states_ == other.ordered_states_ && break_set_ == other.break_set_)
    {
      for (unsigned i = 0; i < other.nondetscc_breaces_.size(); i++)
      {
        if (nondetscc_breaces_[i] == other.nondetscc_breaces_[i])
        {
          continue;
        }
        else
        {
          return false;
        }
      }
      return true;
    }
    return false;
  }
  int tnba_mstate::get_max_rank() const
  {
    int max_rnk = -1;
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      max_rnk = std::max(max_rnk, ordered_states_[i]);
    }
    return max_rnk;
  }
  bool tnba_mstate::is_empty() const
  {
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] != RANK_MISSING)
      {
        return false;
      }
    }
    return true;
  }
  std::set<unsigned>
  tnba_mstate::get_reach_set() const
  {
    std::set<unsigned> result;
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] == RANK_MISSING)
        continue;
      result.insert(i);
    }
    return result;
  }

  std::set<unsigned>
  tnba_mstate::get_weak_set() const
  {
    std::set<unsigned> result;
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] == RANK_WEAK)
        result.insert(i);
    }
    return result;
  }

  std::vector<label>
  tnba_mstate::get_scc_states(unsigned scc) const
  {
    std::vector<label> res;
    // traverse all states
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] == RANK_MISSING || ordered_states_[i] == RANK_WEAK)
      {
        continue;
      }
      if (si_.scc_of(i) == scc)
      {
        res.emplace_back(i, ordered_states_[i]);
      }
    }
    // std::cout << "\nBefore: ";
    // print_label_vec(res);
    // ordered the states
    std::sort(res.begin(), res.end(), label_compare);
    // std::cout << "After: ";
    // print_label_vec(res);
    return res;
  }

  // Return the nodes sorted in ascending order
  std::vector<safra_node>
  tnba_mstate::get_safra_nodes(unsigned scc, unsigned index) const
  {
    std::vector<safra_node> res;
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] == RANK_MISSING || ordered_states_[i] == RANK_WEAK)
      {
        continue;
      }
      if (si_.scc_of(i) == scc)
      {
        // last brace
        int brace = ordered_states_[i];
        std::vector<int> tmp;
        while (brace >= 0)
        {
          // insert in reverse order
          tmp.insert(tmp.begin(), brace);
          // obtain the i-th braces
          brace = nondetscc_breaces_[index][brace];
        }
        res.emplace_back(i, std::move(tmp));
      }
    }
    // compare the node according to its labelling
    std::sort(res.begin(), res.end(), node_compare());
    return res;
  }

  std::vector<int>
  tnba_mstate::get_nondet_braces(unsigned ith_nondet_scc) const
  {
    assert(ith_nondet_scc < nondetscc_breaces_.size());
    return nondetscc_breaces_[ith_nondet_scc];
  }

  size_t
  tnba_mstate::hash() const
  {
    size_t res = 0;
    for (unsigned i : ordered_states_) // not sure how you're storing them
    {
      res = (res << 3) ^ i;
    }
    for (unsigned i : break_set_)
    {
      res ^= (res << 3) ^ i;
    }

    return res;
  }

  // determinization of elevator automata
  class tnba_determinize
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
    std::unordered_map<tnba_mstate, unsigned, tnba_mstate_hash> rank2n_;

    // outgoing transition to its colors by each accepting SCCs (weak is the righmost)
    std::unordered_map<outgoing_trans, std::vector<int>, outgoing_trans_hash> trans2colors_;

    // maximal colors for each accepting SCCs, including DACs and NACs
    std::vector<int> max_colors_;
    std::vector<int> min_colors_;

    // States to process.
    std::deque<std::pair<tnba_mstate, unsigned>> todo_;

    // Support for each state of the source automaton.
    std::vector<bdd> support_;

    // Propositions compatible with all transitions of a state.
    std::vector<bdd> compat_;

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
    get_name(const tnba_mstate &ms)
    {
      // nondeterministic states (including weak states)
      std::string res = "N={";
      bool first_state = true;
      for (unsigned i = 0; i < ms.ordered_states_.size(); i++)
        if (ms.ordered_states_[i] == RANK_WEAK)
        {
          if (!first_state)
            res += ",";
          first_state = false;
          res += std::to_string(i);
        }
      res += "}";
      res += ", O=" + get_set_string(ms.break_set_);
      // now output according SCCs
      for (unsigned scc_id : acc_detsccs_)
      {
        std::vector<label> states = ms.get_scc_states(scc_id);
        res += ",[";
        first_state = true;
        for (unsigned p = 0; p < states.size(); p++)
        {
          if (!first_state)
            res += "<";
          first_state = false;
          res += std::to_string(states[p].first);
        }
        res += "] = scc " + std::to_string(scc_id);
      }
      // now output nondeterministic sccs
      for (unsigned i = 0; i < acc_nondetsccs_.size(); i++)
      {
        unsigned scc_id = acc_nondetsccs_[i];
        std::vector<safra_node> states = ms.get_safra_nodes(scc_id, i);
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
    // From a Rank state, looks for a duplicate in the map before
    // creating a new state if needed.
    unsigned
    new_state(tnba_mstate &s)
    {
      tnba_mstate dup(s);
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

    bool exists(tnba_mstate &s)
    {
      return rank2n_.end() == rank2n_.find(s);
    }

    // remove a state i if it is simulated by a state j
    void
    make_simulation_state(tnba_mstate &ms)
    {
      std::set<unsigned> reached_states = ms.get_reach_set();
      for (unsigned i : reached_states)
      {
        for (unsigned j : reached_states)
        {
          if (i == j)
            continue;
          // j simulates i and j cannot reach i
          if ((simulator_.simulate(j, i) || delayed_simulator_.simulate(j, i)) && simulator_.can_reach(j, i) == 0)
          {
            // std::cout << j << " simulated " << i << std::endl;
            // std::cout << "can_reach = " << simulator_.can_reach(j, i) << std::endl;
            ms.ordered_states_[i] = RANK_MISSING;
            ms.break_set_.erase(i);
          }
          // (j, k1) and (i, k2), if j simulates i and k1 < k2, then remove k2
          // Note that here i and j are not equivalent
          unsigned scc_i = si_.scc_of(i);
          if ((simulator_.simulate(j, i) || delayed_simulator_.simulate(j, i)) 
              && ms.ordered_states_[j] >= 0 && ms.ordered_states_[i] >= 0 && (scc_i == si_.scc_of(j)))
          // if j can reach i, then scc(j) must be larger scc(i) ms[j] > RANK_N && ms[j] < ms[i])
          {
            bool remove = false;
            if (is_acepting_detscc(scc_types_, scc_i) && ms.ordered_states_[j] < ms.ordered_states_[i])
            {
              remove = true;
            }else if (is_accepting_nondetscc(scc_types_, scc_i) )
            {
              // need to compare there nesting pattern
              int brace_i = ms.ordered_states_[i];
              int brace_j = ms.ordered_states_[j];
              int scc_index = get_nondetscc_index(scc_i);
              std::vector<int>& braces = ms.nondetscc_breaces_[scc_index];
              // std::cout << "State " << i << " brace: " << brace_i << std::endl;
              // std::cout << "State " << j << " brace: " << brace_j << std::endl;
              //print_pattern_vec(braces, braces.size());
              if (compare_braces(braces, brace_j, brace_i))
              {
                remove = true;
              }
            }
            if (remove)
            {
              // std::cout << j << " simulated " << i << std::endl;
              ms.ordered_states_[i] = RANK_MISSING;
              ms.break_set_.erase(i);
            }
          }
        }
      }
    }

    // Runs with higher labelling may be merged by those with lower labelling
    void compute_deterministic_successors(const tnba_mstate &ms, bdd letter, tnba_mstate &succ, std::vector<std::vector<label>> &det_scc_labellings, std::function<bool(bool, unsigned)> can_ignore)
    {
      for (unsigned i = 0; i < acc_detsccs_.size(); i++)
      {
        unsigned curr_scc = acc_detsccs_[i];
        // list of deterministic states, already ordered by its labelling
        std::vector<label> &acc_det_states = det_scc_labellings[i];
        // print_label_vec(acc_det_states);
        for (unsigned j = 0; j < acc_det_states.size(); j++)
        {
          unsigned s = acc_det_states[j].first;
          int curr_label = acc_det_states[j].second;
          // states and ranking
          for (const auto &t : aut_->out(s))
          {
            if (!bdd_implies(letter, t.cond))
              continue;
            if (can_ignore(use_unambiguous_, t.dst))
            {
              continue;
            }
            unsigned succ_scc = si_.scc_of(t.dst);
            // ignore the states that go to other SCCs
            if (curr_scc != succ_scc)
              continue;
            assert(succ.ordered_states_[t.dst] != RANK_MISSING);
            // Stay in the same accepting deterministic SCC or just enter this SCC
            // All DAC-states already have assigned with MAX_RANK
            succ.ordered_states_[t.dst] = std::min(succ.ordered_states_[t.dst], curr_label);
          }
        }
      }
    }

    void compute_deterministic_color(const tnba_mstate &ms, bdd letter, tnba_mstate &succ, std::vector<std::vector<label>> &det_scc_labellings, std::vector<std::pair<int, int>> &min_labellings, std::function<bool(bool, unsigned)> can_ignore)
    {
      // record the numbers
      for (unsigned i = 0; i < acc_detsccs_.size(); i++)
      {
        unsigned curr_scc = acc_detsccs_[i];
        int min_acc = MAX_RANK_;
        int min_dcc = MAX_RANK_;
        // list of deterministic states, already ordered by its labelling
        std::vector<label> &acc_det_states = det_scc_labellings[i];
        // std::cout << "Computing scc " << curr_scc << "\n";
        // print_label_vec(acc_det_states);
        for (unsigned j = 0; j < acc_det_states.size(); j++)
        {
          bool has_succ = false;
          bool has_acc = false;
          unsigned s = acc_det_states[j].first;
          int curr_label = acc_det_states[j].second;
          assert(curr_label == j);
          for (const auto &t : aut_->out(s))
          {
            if (!bdd_implies(letter, t.cond))
              continue;
            if (can_ignore(use_unambiguous_, t.dst))
            {
              continue;
            }
            // 1. first they should be in the same SCC
            // 2. second the label should be equal
            if (si_.scc_of(s) == si_.scc_of(t.dst) && succ.ordered_states_[t.dst] == curr_label)
            {
              has_succ = true;
              has_acc = has_acc || t.acc;
            }
          }
          if (!has_succ && min_dcc == MAX_RANK_)
          {
            // i. no successor, record the smaller label
            min_dcc = j;
          }
          else if (has_acc && min_acc == MAX_RANK_)
          {
            // ii. see an accepting transition
            min_acc = j;
          }
        }
        // record the pair of labellings for the SCC
        min_labellings.push_back(std::make_pair(min_dcc, min_acc));
      }
    }

  void
  compute_nondeterministic_successors(const tnba_mstate &ms, bdd letter, tnba_mstate &succ, std::vector<std::pair<std::vector<label>, std::vector<int>>> &nondet_scc_labellings, std::vector<std::set<unsigned>> &next_nondetstates, std::function<bool(bool, unsigned)> can_ignore)
  {
    for (unsigned i = 0; i < acc_nondetsccs_.size(); i++)
    {
      unsigned curr_scc = acc_nondetsccs_[i];
      // list of nondeterministic states, already ordered by its labelling (not necessary)
      std::vector<label> &acc_nondet_states = nondet_scc_labellings[i].first;
      // for (unsigned k = 0; k < acc_nondet_states.size(); k ++)
      // {
      //   std::cout << "State " << acc_nondet_states[k].first << " Label: " << acc_nondet_states[k].second << "\n";
      // }
      std::vector<int> braces = nondet_scc_labellings[i].second; //copy
      // for (unsigned k = 0; k < braces.size(); k ++)
      // {
      //   std::cout << " " << k << " parent: " << braces[k] << "\n";
      // }
      // std::cout << " reach_states: " << get_set_string(next_nondetstates[i]) << std::endl;
      // unsigned topbrace = braces.size();
      std::map<unsigned, int> succ_nodes;
      // nodes are pair of states and labelling, ordered according to
      // labels and then state number
      for (const auto &node : acc_nondet_states)
      {
        for (const auto &t : aut_->out(node.first))
        {
          if (!bdd_implies(letter, t.cond))
            continue;
          if (can_ignore(use_unambiguous_, t.dst))
            continue;
          unsigned succ_scc = si_.scc_of(t.dst);
          int newb = node.second;
          unsigned dst = t.dst;
          // Only care about the states in the current SCC
          if (curr_scc == succ_scc)
          {
            // std::cout << " " << node.first << " -> " << t.dst << " : " << letter << " " << t.acc << std::endl;
            // Delete a newincoming state who is already a successor from the same SCC
            next_nondetstates[i].erase(dst);
            if (t.acc)
            {
              // Step A1: Accepting edges generate new braces
              newb = braces.size();
              // put current brace node.second as the parent of newb
              braces.push_back(node.second);
              // std::cout << " " << newb << " parent: " << node.second << std::endl;
            }
            auto i = succ_nodes.emplace(dst, newb);
            if (!i.second) // dst already exists
            {
              // Step A2: Only keep the smallest nesting pattern.
              if (compare_braces(braces, newb, i.first->second))
              {
                // newb is smaller
                i.first->second = newb;
              }
              else
              {
                // the newb is not smaller than current one
                if (newb != node.second) // new brace was created but is not needed
                  braces.pop_back();
              }
            }
          }
        }
      }
      
      // std::cout << "After computation of nondet inside " << i << " size = " << next_nondetstates.size() << "\n";
      // New incoming states
      // Top level is 0, if we enter the SCC, we need more braces
      // Order each entry states since each run can have accepting runs
      for (unsigned dst : next_nondetstates[i])
      {
        // put them all in top brace 0
        int newb = braces.size();
        // Step A1
        auto i = succ_nodes.emplace(dst, newb);
        // If the state has not been added
        if (i.second || i.first->second == -1)
        {
          braces.push_back(RANK_TOP_BRACE);
          i.first->second = newb;
        }
      }
      // now store the results to succ
      for (auto &node : succ_nodes)
      {
        succ.ordered_states_[node.first] = node.second;
      }
      // replace the braces
      succ.nondetscc_breaces_[i] = braces;
    }
  }

  // This function is basically minor adaption from spot/twaalgos/deterministic.cc/finalize_construction
  void
  compute_nondeterministic_color(const tnba_mstate &ms, bdd letter, tnba_mstate &succ, std::vector<std::pair<int, int>> &nondet_labellings)
  {
    // now check the good events and the bad events
    for (unsigned i = 0; i < acc_nondetsccs_.size(); i++)
    {
      unsigned curr_scc = acc_nondetsccs_[i];
      std::vector<label> nodes = succ.get_scc_states(curr_scc);
      std::vector<int> braces = succ.get_nondet_braces(i); // copy the vector

      int min_dcc = MAX_RANK_;
      int min_acc = MAX_RANK_;

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
      nondet_labellings.push_back(std::make_pair(min_dcc, min_acc));
      // drease the values

      // Update nodes with new braces numbers
      std::vector<int> newbs = std::vector<int>(braces.size() - decr, -1);
      for (auto& n : nodes)
        {
          // if the brace is not -1
          if (n.second >= 0)
            {
              // highest ancester that is green
              unsigned i = highest_green_ancestor[n.second];
              int j = braces[i] >=0 // except 0, every ancester should be this way
                        ? braces[i] - decr_by[braces[i]]
                        : -1;
              n.second = i - decr_by[i];
              succ.ordered_states_[n.first] = n.second;
              newbs[n.second] = j;
            }
        }
      succ.nondetscc_breaces_[i] = newbs;
    }

  }

  int compute_parity_color(int min_dcc, int min_acc)
  {
    int parity;

    if (min_dcc == MAX_RANK_ && min_acc != MAX_RANK_)
    {
      // only good events
      parity = 2 * (min_acc + 1);
    }
    else if (min_dcc != MAX_RANK_ && min_acc == MAX_RANK_)
    {
      // only bad events
      parity = 2 * min_dcc + 1;
    }
    else if (min_dcc != MAX_RANK_ && min_acc != MAX_RANK_)
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

  // compute the successor N={nondeterministic states and nonaccepting SCCs} O = {breakpoint for weak SCCs}
  // and labelling states for each SCC
  void
  compute_successors(const tnba_mstate &ms, bdd letter, tnba_mstate &nxt, std::vector<int> &color)
  {
    tnba_mstate succ(si_, nb_states_, RANK_MISSING, acc_nondetsccs_.size());
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
    for (unsigned i = 0; i < acc_nondetsccs_.size(); i++)
    {
      std::set<unsigned> states;
      next_nondetstates.push_back(states);
    }
    int max_rnk = ms.get_max_rank();

    //1. first handle inherently weak states
    for (unsigned s : current_states)
    {
      // nondeterministic states or states in nonaccepting SCCs
      bool in_break_set = (ms.break_set_.find(s) != ms.break_set_.end());
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
          succ.ordered_states_[t.dst] = max_rnk + 1; //Sharing labels
        }
        else if (is_weakscc(scc_types_, scc_id))
        {
          // weak states or nondeterministic or nonaccepting det scc
          succ.ordered_states_[t.dst] = RANK_WEAK;
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
          int nondet_scc_index = get_nondetscc_index(scc_id);
          assert(nondet_scc_index != -1);
          // reached states for each NAC
          next_nondetstates[nondet_scc_index].insert(t.dst);
        }
        else
        {
          assert(false);
        }
      }
    }
    // std::cout << "After nondeterministic: " << get_name(succ) << std::endl;
    std::vector<std::vector<label>> det_scc_labellings;
    for (unsigned i = 0; i < acc_detsccs_.size(); i++)
    {
      std::vector<label> labellings = ms.get_scc_states(acc_detsccs_[i]);
      det_scc_labellings.push_back(labellings);
    }
    //2. Compute the labelling successors for deterministic SCCs
    compute_deterministic_successors(ms, letter, succ, det_scc_labellings, can_ignore);

    // std::cout << "After deterministic part = " << get_name(succ) << std::endl;


    std::vector<std::pair<std::vector<label>, std::vector<int>>> nondet_scc_labellings;
    for (unsigned i = 0; i < acc_nondetsccs_.size(); i++)
    {
      std::vector<label> labellings = ms.get_scc_states(acc_nondetsccs_[i]);
      nondet_scc_labellings.emplace_back(labellings, ms.get_nondet_braces(i));
    }
    //3. Compute the successors for nondeterministic SCCs
    compute_nondeterministic_successors(ms, letter, succ, nondet_scc_labellings, next_nondetstates, can_ignore);
    // std::cout << "After nondeterministic part = " << get_name(succ) << std::endl;

    // remove redudant states
    if (use_simulation_)
    {
      make_simulation_state(succ);
    }
    //now compute the labels
    std::vector<std::pair<int, int>> det_min_labellings;
    //4. decide the color for deterministic SCCs
    compute_deterministic_color(ms, letter, succ, det_scc_labellings, det_min_labellings, can_ignore);
    //5. decide the color for nondeterministic SCCs
    std::vector<std::pair<int, int>> nondet_min_labellings;
    compute_nondeterministic_color(ms, letter, succ, nondet_min_labellings);

    bool break_empty = succ.break_set_.empty();
    // now determine the break set
    if (break_empty)
    {
      // if the breakpoint is empty, then fill it with newly-incoming accepting weak SCC states
      std::set<unsigned> result;
      std::set<unsigned> reach_sucss = succ.get_reach_set();
      std::set_intersection(reach_sucss.begin(), reach_sucss.end(), acc_weak_coming_states.begin(), acc_weak_coming_states.end(), std::inserter(result, result.begin()));
      succ.break_set_ = result;
    }

    std::vector<int> colors;
    //3. Determine the color on the transition for each accepting deterministic SCC
    // the minimal even color is 2 and the minimal odd color is 1
    for (unsigned i = 0; i < acc_detsccs_.size(); i++)
    {
      int parity = compute_parity_color(det_min_labellings[i].first, det_min_labellings[i].second);
      colors.push_back(parity);
    }

    for (unsigned i = 0; i < acc_nondetsccs_.size(); i++)
    {
      int parity = compute_parity_color(nondet_min_labellings[i].first, nondet_min_labellings[i].second);
      colors.push_back(parity);
    }

    // give color for the weak SCCs
    if (break_empty)
    {
      colors.push_back(0);
    }
    else
    {
      colors.push_back(-1);
    }

    //4. Reorgnize the indices of each accepting deterministic SCC
    for (unsigned i = 0; i < acc_detsccs_.size(); i++)
    {
      std::vector<label> acc_det_states = succ.get_scc_states(acc_detsccs_[i]);
      for (unsigned j = 0; j < acc_det_states.size(); j++)
      {
        succ.ordered_states_[acc_det_states[j].first] = j;
      }
    }
    //5. Reorganize the indices for each accepting nondeterministic SCC
    // already done in deciding colors
    nxt = succ;
    color = colors;
  }
  // copied and adapted from deterministic.cc in Spot
  void
  make_stutter_state(const tnba_mstate &curr, bdd letter, tnba_mstate &succ, std::vector<int> &colors)
  {
    tnba_mstate ms(curr);
    std::vector<tnba_mstate> stutter_path;
    if (use_stutter_ && aut_->prop_stutter_invariant())
    {
      // The path is usually quite small (3-4 states), so it's
      // not worth setting up a hash table to detect a cycle.
      stutter_path.clear();
      std::vector<tnba_mstate>::iterator cycle_seed;
      std::vector<int> mincolor(acc_detsccs_.size() + acc_nondetsccs_.size() + 1, -1);
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
        tnba_mstate tmp_succ(si_, nb_states_, RANK_MISSING, acc_nondetsccs_.size());
        std::vector<int> tmp_color(acc_detsccs_.size() + acc_nondetsccs_.size() + 1, -1);
        compute_successors(stutter_path.back(), letter, tmp_succ, tmp_color);
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
      compute_successors(ms, letter, succ, colors);
    }
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

public:
  tnba_determinize(const spot::const_twa_graph_ptr &aut, spot::scc_info &si, spot::option_map &om, std::vector<bdd> &implications)
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
        MAX_RANK_(aut->num_states() + 2),
        simulator_(aut, si, implications, om.get(USE_SIMULATION) > 0),
        delayed_simulator_(aut, om),
        show_names_(om.get(VERBOSE_LEVEL) >= 2)
  {
    if (om.get(VERBOSE_LEVEL) >= 2)
    {
      simulator_.output_simulation();
    }
    // std::cout << "Hello NBA" << std::endl;
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
      for (const auto &out : aut->out(i))
      {
        res_support &= bdd_support(out.cond);
        res_compat |= out.cond;
      }
      support_[i] = res_support;
      compat_[i] = res_compat;
    }
    // obtain the types of each SCC
    scc_types_ = get_scc_types(si_);

    // find out the DACs and NACs
    for (unsigned i = 0; i < scc_types_.size(); i++)
    {
      // ignore weak types
      if ((scc_types_[i] & SCC_WEAK_TYPE))
        continue;
      max_colors_.push_back(-1);
      min_colors_.push_back(INT_MAX);
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
    tnba_mstate new_init_state(si_, nb_states_, RANK_MISSING, acc_nondetsccs_.size());
    unsigned init_scc = si_.scc_of(init_state);
    if ((scc_types_[init_scc] & SCC_WEAK_TYPE))
    {
      new_init_state.ordered_states_[init_state] = RANK_WEAK;
    }
    else if (is_acepting_detscc(scc_types_, init_scc))
    {
      new_init_state.ordered_states_[init_state] = 0;
    }
    else if (is_accepting_nondetscc(scc_types_, init_scc))
    {
      // initialize the safra_node
      new_init_state.ordered_states_[init_state] = 0;
      int init_scc_index = get_nondetscc_index(init_scc);
      assert (init_scc_index != -1);
      new_init_state.nondetscc_breaces_[init_scc_index].push_back(RANK_TOP_BRACE);
    }
    // we assume that the initial state is not in deterministic part
    res_->set_init_state(new_state(new_init_state));

  }

  // by default, the number of colors for each set is even
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

  bool
  has_weak_acc_sccs()
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

  void
  finalize_acceptance()
  {
    std::vector<bool> odds(max_colors_.size(), false);
    for (unsigned i = 0; i < max_colors_.size(); i++)
    {
      if (max_colors_[i] < 0)
        continue;
      // std::cout << i << "-th SCC "<< " max_color = " << max_colors_[i] << " min_color = " << min_colors_[i] << std::endl;
      // now we make all maximal colors an odd color (the color that cannot be visited infinitely often)
      max_colors_[i] = (max_colors_[i] & 1) ? max_colors_[i] : (max_colors_[i] + 1);
      // make minimal color an even color (no zero by construction, will shift to zero later)
      // min_colors_[i] = (min_colors_[i] & 1) ? min_colors_[i] - 1 : min_colors_[i];
      // std::cout << "SCC " << acc_detsccs_[i] << " max_color = " << max_colors_[i] << " min_color = " << min_colors_[i] << std::endl;
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
    bool has_weak_acc = has_weak_acc_sccs();
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
      if (has_weak_acc && p->second.back() >= 0)
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
  run()
  {
    // Main stuff happens here
    // todo_ is a queue for handling states
    while (!todo_.empty())
    {
      auto top = todo_.front();
      todo_.pop_front();
      // pop current state, (N, Rnk)
      tnba_mstate ms = top.first;

      // Compute support of all available states.
      bdd msupport = bddtrue;
      bdd n_s_compat = bddfalse;
      // compute the occurred variables in the outgoing transitions of ms, stored in msupport
      for (unsigned s = 0; s < nb_states_; ++s)
        if (ms.ordered_states_[s] != RANK_MISSING)
        {
          msupport &= support_[s];
          n_s_compat |= compat_[s];
        }

      bdd all = n_s_compat;
      while (all != bddfalse)
      {
        bdd letter = bdd_satoneset(all, msupport, bddfalse);
        all -= letter;

        // std::cout << "Current state = " << get_name(ms) << " letter = "<< letter << std::endl;
        tnba_mstate succ(si_, nb_states_, RANK_MISSING, acc_nondetsccs_.size());
        // the number of SCCs we care is the accepting det SCCs and the weak SCCs
        std::vector<int> colors(acc_detsccs_.size() + acc_nondetsccs_.size() + 1, -1);
        //compute_labelling_successors(std::move(ms), top.second, letter, succ, color);
        make_stutter_state(ms, letter, succ, colors);

        if (succ.is_empty())
          continue;

        unsigned origin = top.second;
        // add transitions
        // Create the automaton states
        unsigned dst = new_state(succ);
        // first add this transition
        res_->new_edge(origin, dst, letter);
        // handle with colors
        // std::cout << "max_color_size = " << max_colors_.size() << " colors_size = " << colors.size() << "\n";  
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
    if (om_.get(VERBOSE_LEVEL) >= 2)
    {
      output_file(res_, "dpa.hoa");
      std::cout << "Before simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
      check_equivalence(aut_, res_);
    }
    if (om_.get(USE_SCC_INFO) > 0)
      res_ = postprocess(res_);
    if (om_.get(VERBOSE_LEVEL) >= 2)
    {
      std::cout << "After simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
      output_file(res_, "dpa1.hoa");
      check_equivalence(aut_, res_);
    }
    simplify_acceptance_here(res_);

    return res_;
  }

  spot::twa_graph_ptr
  postprocess(spot::twa_graph_ptr aut)
  {
    spot::scc_info scc_dpa(aut, spot::scc_info_options::ALL);
    // set of states -> the forest of reachability in the states.
    mstate_equiv_map set2scc;
    // record the representative of every SCC
    for (auto p = rank2n_.begin(); p != rank2n_.end(); p++)
    {
      std::set<unsigned> set = p->first.get_reach_set();
      // first the set of reached states
      auto val = set2scc.find(set);
      if (val == set2scc.end())
      {
        // the set of macrostates in DPA
        std::set<unsigned> v;
        v.insert(p->second);
        set2scc[set] = v;
      }
      else
      {
        val->second.insert(p->second);
        set2scc[set] = val->second;
      }
    }
    mstate_merger merger(aut, set2scc, scc_dpa, om_);
    spot::twa_graph_ptr res = merger.run();
    if (om_.get(VERBOSE_LEVEL) >= 1)
      std::cout << "The number of states reduced by mstate_merger: "
                << (aut->num_states() - res->num_states()) << " {out of "
                << aut->num_states() << "}" << std::endl;
    return res;
  }
};

spot::twa_graph_ptr
determinize_tnba(const spot::const_twa_graph_ptr &aut, spot::option_map &om)
{
  if (!aut->acc().is_buchi())
    throw std::runtime_error("determinize_tnba() requires a Buchi input");

  // now we compute the simulator
  spot::const_twa_graph_ptr aut_reduced;
  std::vector<bdd> implications;
  spot::twa_graph_ptr aut_tmp = nullptr;
  if (om.get(USE_SIMULATION) > 0)
  {
    aut_tmp = spot::scc_filter(aut);
    auto aut2 = spot::simulation(aut_tmp, &implications);
    aut_tmp = aut2;
  }
  if (aut_tmp)
    aut_reduced = aut_tmp;
  else
    aut_reduced = aut;
  spot::scc_info scc(aut_reduced, spot::scc_info_options::ALL);
  auto det = cola::tnba_determinize(aut_reduced, scc, om, implications);
  return det.run();
}
}