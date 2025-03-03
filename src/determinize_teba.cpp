// Copyright (C) 2022  The COLA Authors
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
#include <bitset>
#include <bits/stdc++.h>

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
#include <spot/misc/trival.hh>
#include <spot/twa/acc.hh>


// specific determinization construction for elevator automata with Emeron-Lei condition
// elevator automata have only deterministic SCCs and inherently weak SCCs
namespace cola
{
  // state and the labelling value
  typedef std::pair<unsigned, int> label;
  typedef std::pair<unsigned, bdd> outgoing_trans;
  typedef std::set<unsigned> mark_labels;

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

  class elevator_mstate
  {
  public:
    elevator_mstate(spot::scc_info &si, unsigned num_det_acc_sccs)
        : si_(si)
    {
      for (unsigned i = 0; i < num_det_acc_sccs; i ++)
      {
        detscc_labels_.emplace_back(std::vector<label>());
      }
    }

    elevator_mstate(const elevator_mstate &other)
        : si_(other.si_)
    {
      this->break_set_.clear();
      this->break_set_.insert(other.break_set_.begin(), other.break_set_.end());
      this->weak_set_.clear();
      this->weak_set_.insert(other.weak_set_.begin(), other.weak_set_.end());

      this->detscc_labels_.clear();
      for (unsigned i = 0; i < other.detscc_labels_.size(); i ++)
      {
        std::vector<label> copy = other.detscc_labels_[i];
        detscc_labels_.emplace_back(copy);
      }
  
    }

    std::set<unsigned>
    get_reach_set() const;

    std::set<unsigned>
    get_unlabelled_set() const;

    bool is_empty() const;

    int get_max_rank() const;

    std::vector<label>
    get_detscc_states(unsigned scc) const;

    bool operator<(const elevator_mstate &other) const;
    bool operator==(const elevator_mstate &other) const;

    elevator_mstate &
    operator=(const elevator_mstate &other)
    {
      this->si_ = other.si_;
      this->break_set_.clear();
      this->break_set_.insert(other.break_set_.begin(), other.break_set_.end());
      this->weak_set_.clear();
      this->weak_set_.insert(other.weak_set_.begin(), other.weak_set_.end());

      this->detscc_labels_.clear();
      for (unsigned i = 0; i < other.detscc_labels_.size(); i ++)
      {
        std::vector<label> copy = other.detscc_labels_[i];
        detscc_labels_.emplace_back(copy);
      }
      return *this;
    }

    size_t hash() const;

    // SCC information
    spot::scc_info &si_;
    // states are ordered according to their SCCs
    std::vector<std::vector<label>> detscc_labels_;
    // std::vector<int> ordered_states_;
    // breakpoint construction for weak accepting SCCs
    std::set<unsigned> break_set_;
    std::set<unsigned> weak_set_;
  };

  struct elevator_mstate_hash
  {
    size_t
    operator()(const elevator_mstate &s) const noexcept
    {
      return s.hash();
    }
  };

  bool
  elevator_mstate::operator<(const elevator_mstate &other) const
  {
    if (weak_set_ == other.weak_set_)
    {
      if (break_set_ == other.break_set_)
      {
        for (unsigned i = 0; i < detscc_labels_.size(); i ++)
        {
          if (detscc_labels_[i] == other.detscc_labels_[i])
          {
            continue;
          }else 
          {
            return detscc_labels_[i] < other.detscc_labels_[i];
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
  elevator_mstate::operator==(const elevator_mstate &other) const
  {
    if (this->weak_set_ != other.weak_set_)
    {
      return false;
    }
    if (this->break_set_ != other.break_set_)
    {
      return false;
    }
    for (unsigned i = 0; i < detscc_labels_.size(); i ++)
    {
      if (detscc_labels_[i] != other.detscc_labels_[i])
      {
        return false;
      }
    }
    return true;
  }
  int elevator_mstate::get_max_rank() const
  {
    int max_rnk = -1;
    return max_rnk;
  }
  bool elevator_mstate::is_empty() const
  {
    if (! weak_set_.empty())
    {
      return false;
    }
    for (unsigned i = 0; i < detscc_labels_.size(); i ++)
    {
      if (! detscc_labels_[i].empty())
      {
        return false;
      }
    }
    return true;
  }
  std::set<unsigned>
  elevator_mstate::get_reach_set() const
  {
    std::set<unsigned> result;
    result.insert(weak_set_.begin(), weak_set_.end());
    for (auto & vec : detscc_labels_)
    {
      for (auto& p : vec)
      {
        result.insert(p.first);
      }
    }
    return result;
  }

  std::set<unsigned>
  elevator_mstate::get_unlabelled_set() const
  {
    std::set<unsigned> result;
    result.insert(weak_set_.begin(), weak_set_.end());
    for (auto & vec : detscc_labels_)
    {
      for (auto& p : vec)
      {
        result.insert(p.first);
      }
    }
    return result;
  }

  void print_label_vec(std::vector<label> res)
  {
    for (unsigned i = 0; i < res.size(); i ++)
    {
      std::cout << " " << res[i].first << " = label(" << res[i].second << ")";
    }
    std::cout << "\n";
  }

  size_t
  elevator_mstate::hash() const
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
    for (unsigned i = 0; i < detscc_labels_.size(); i ++)
    {
      for (auto& p : detscc_labels_[i])
      {
        res ^= (res << 3) ^ (p.first);
        res ^= (res << 3) ^ (p.second);
      }
    }
    return res;
  }

  // determinization of elevator automata
  class elevator_determinize
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

    unsigned num_colours_;

    spot::option_map &om_;

    // use ambiguous
    bool use_unambiguous_;

    bool use_scc_;

    // use stutter
    bool use_stutter_;

    bool use_simulation_;

    // Association between labelling states and state numbers of the
    // DPA.
    std::unordered_map<elevator_mstate, unsigned, elevator_mstate_hash> rank2n_;

    // outgoing transition to its colors by each accepting SCCs (weak is the righmost)
    std::unordered_map<unsigned, std::pair<unsigned, std::vector<mark_labels>>> trans2colors_;

    // States to process.
    std::deque<std::pair<elevator_mstate, unsigned>> todo_;

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

    // Show Rank states in state name to help debug
    bool show_names_;

    std::string
    get_name(const elevator_mstate &ms)
    {
      // nondeterministic states (including weak states)
      std::string res = "N={";
      bool first_state = true;
      for (unsigned i : ms.weak_set_)
        {
          if (!first_state)
            res += ",";
          first_state = false;
          res += std::to_string(i);
        }
      res += "}";
      res += ", O=" + get_set_string(ms.break_set_);
      // now output according SCCs
      for (unsigned i = 0; i < acc_detsccs_.size(); i ++)
      {
        unsigned scc_id = acc_detsccs_[i];
        std::vector<label> states = ms.detscc_labels_[i];
        std::sort(states.begin(), states.end(), label_compare);
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
      return res;
    }
    // From a Rank state, looks for a duplicate in the map before
    // creating a new state if needed.
    unsigned
    new_state(elevator_mstate &s)
    {
      elevator_mstate dup(s);
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

    bool exists(elevator_mstate &s)
    {
      return rank2n_.end() != rank2n_.find(s);
    }

    void remove_label(std::vector<label>& nodes, std::set<unsigned>& to_remove)
    {
      std::vector<label> tmp;
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

  void merge_redundant_states(elevator_mstate &ms, std::vector<label>& nodes, bool nondet)
  {
    auto it1 = nodes.begin();
    while (it1 != nodes.end())
      {
        auto old_it1 = it1++;
        // for deterministic ones, the labelling is already ordered 
        // so we can ignore all the values after old_it1 ?
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
            if (brace_j < brace_i)
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

    // remove a state i if it is simulated by a state j
    void
    make_simulation_state(elevator_mstate &ms)
    {
      const std::set<unsigned> reached_states = ms.get_reach_set();
      std::vector<std::set<unsigned>> det_remove(acc_detsccs_.size(), std::set<unsigned>());
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
            }else if (is_accepting_detscc(scc_types_, scc_i))
            {
              int index = get_detscc_index(scc_i);
              det_remove[index].insert(i);
            }
          }
        }
      }
      for (unsigned i = 0; i < det_remove.size(); i ++)
      {
        remove_label(ms.detscc_labels_[i], det_remove[i]);
        // now remove more
        merge_redundant_states(ms, ms.detscc_labels_[i], false);
      }
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

    void print_set(const std::set<unsigned>& states)
  {
    for (unsigned i : states)
    {
      std::cout << " " << i;
    }
    std::cout << "\n";
  }

    typedef spot::acc_cond::mark_t mark_set;

    // compute the successor N={nondeterministic states and nonaccepting SCCs} 
    // O = {breakpoint for weak SCCs}
    // and labelling states for each SCC
    void
    compute_successors(const elevator_mstate &ms, bdd letter, elevator_mstate &nxt, std::pair<unsigned
      , std::vector<std::set<unsigned>>> &colours)
    {
      // initialise the successor macrostate
      elevator_mstate succ(si_, nb_states_);
      // used for unambiguous automaton
      std::vector<bool> incoming(nb_states_, false);
      std::vector<bool> ignores(nb_states_, false);
      // std::cout << "current mstate: " << get_name(ms) << std::endl;
      // std::cout << "current letter: ";
      // bdd_printset(letter);
      // std::cout << std::endl;
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
          }else 
          {
            return false;
          }
      };

      //1. first handle nondeterministic states
      std::set<unsigned> acc_weak_coming_states;
      // all reachable states
      std::set<unsigned> current_states = ms.get_reach_set();
      
      std::vector<std::set<unsigned>> next_detstates;
      for (unsigned i = 0; i < acc_detsccs_.size(); i++)
      {
        std::set<unsigned> states;
        next_detstates.emplace_back(states);
      }
      int max_rnk = INT_MAX;

      std::unordered_map<unsigned, std::vector<std::pair<mark_set, unsigned>>> det_cache;
      
      //1. first handle inherently weak states
      for (unsigned s : current_states)
      {
        // nondeterministic states or states in nonaccepting SCCs
        bool in_break_set = (ms.break_set_.find(s) != ms.break_set_.end());
        bool in_acc_det = is_accepting_detscc(scc_types_, si_.scc_of(s));
        if (in_acc_det)
        {
          det_cache.emplace(s, std::vector<std::pair<mark_set, unsigned>>());
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
          // we move the states in accepting det SCC 
          if (is_accepting_detscc(scc_types_, scc_id))
          {
            int det_scc_index = get_detscc_index(scc_id); 
            assert(det_scc_index != -1);
            // incoming states
            next_detstates[det_scc_index].insert(t.dst);
            if (in_acc_det)
            {
              det_cache[s].emplace_back(t.acc, t.dst);
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
          else
          {
            assert(false);
          }
        }
      }
      // std::cout << "After step: " << get_name(succ) << std::endl;
      //2. Compute the labelling successors for deterministic SCCs
      compute_deterministic_successors(ms, succ, next_detstates, det_cache);
      // std::cout << "After receiving more successors: " << get_name(succ) << std::endl;
      if (use_simulation_)
      {
        make_simulation_state(succ);
      }
      std::vector<std::set<unsigned>> det_labellings;
      //4. decide the color for deterministic SCCs
      compute_deterministic_color(ms, succ, det_labellings, det_cache);

      bool break_empty = succ.break_set_.empty();
      // now determine the break set
      if (break_empty)
      {
        // std::cout << "new Incoming: ";
        // print_set(acc_weak_coming_states);
        // if the breakpoint is empty, then fill it with newly-incoming accepting weak SCC states
        std::set<unsigned> result;
        std::set<unsigned> reach_sucss = succ.get_reach_set();
        std::set_intersection(reach_sucss.begin(), reach_sucss.end()
        , acc_weak_coming_states.begin(), acc_weak_coming_states.end()
        , std::inserter(result, result.begin()));
        succ.break_set_ = result;
        colours.first = 1;
        // Should finitely see it
      }else {
        colours.first = 0;
      }

      colours.second = det_labellings;
      nxt = succ;
      // color = colors;
    }

    // Runs with higher labelling may be merged by those with lower labelling
    void compute_deterministic_successors(const elevator_mstate &ms, elevator_mstate &succ, std::vector<std::set<unsigned>>& next_detstates
      , std::unordered_map<unsigned, std::vector<std::pair<mark_set, unsigned>>>& det_cache)
      {
        for (unsigned i = 0; i < acc_detsccs_.size(); i++)
        {
          unsigned curr_scc = acc_detsccs_[i];
          // list of deterministic states, already ordered by its labelling
          const std::vector<label> &acc_det_states = ms.detscc_labels_[i];
          std::map<unsigned, int> succ_nodes;
          int max_rnk = -1;
          // print_label_vec(acc_det_states);
          for (unsigned j = 0; j < acc_det_states.size(); j++)
          {
            unsigned s = acc_det_states[j].first;
            int curr_label = acc_det_states[j].second;
            max_rnk = std::max(max_rnk, curr_label);
            assert (curr_label == j);
            // states and ranking
            for (const auto &t : det_cache[s])
            {
              unsigned succ_scc = si_.scc_of(t.second);
              // ignore the states that go to other SCCs
              if (curr_scc != succ_scc)
                continue;
              next_detstates[i].erase(t.second);
              // Stay in the same accepting deterministic SCC or just enter this SCC
              // All DAC-states already have assigned with MAX_RANK
              auto it = succ_nodes.emplace(t.second, curr_label);
              if (! it.second) // already there
              {
                int prev_label = it.first->second;
                it.first->second = std::min(curr_label, prev_label);
              }
            }
          }
          ++ max_rnk ;
          // put them into succ
          for (unsigned p : next_detstates[i])
          {
            // insertion failed is possible
            succ_nodes.emplace(p, max_rnk);
            ++ max_rnk;
          }
          //succ.detscc_labels_[i].clear();
          for (auto& node : succ_nodes)
          {
            succ.detscc_labels_[i].emplace_back(node.first, node.second);
          }
        }
      }
      // with each SCC
      // assume that the total used sets are [0,...,k-1]
      // k is the number of sets
      // for each run i, we use the colours (k + 1) * j, to, (k+1)*j + k
      // hence, for run 0, it is 0, ..., k-1, k
      // for run 1, k+1, ..., (k+1) + k
      //     run 2, 2*(k+1), ..., 2*(k+1) + c, ... , 2*(k+1)+k
      //     ...
      //     run j, j*(k+1), ..., j*(k+1) + c, ..., j*(k+1) + k
      //     ...
      //  where c is the original colour; the last colour j*(k+1)+k 
      // indicates the run has been discontinued
      // note that if a j*(k+1) + k occurs, all larger ones must also occur
      void compute_deterministic_color(const elevator_mstate &ms, elevator_mstate &succ
        , std::vector<std::set<unsigned>> &labellings
        , std::unordered_map<unsigned, std::vector<std::pair<mark_set, unsigned>>>& det_cache)
        {
          // now we need to check for each color c
          // For Inf(c), it is quite similar to accepting transition
          // For Fin(c), we need to reject, so we just shift one bit maybe
          const int MAX_RANK = aut_->num_states() + 2;
          // std::vector<std::set<unsigned>> discontinued_runs;
          // auto num_colours = used_sets.max_set(); // k + 1
          // record the colours we put on this transition
          // note that these are relative colours, need to shift afterwards
          std::vector<std::set<unsigned>> colours;
          // std::cout << "num_colours: " << num_colours_ << std::endl;
          unsigned num_colours_plus_one = num_colours_plus_one_;

          // record the numbers
          for (unsigned i = 0; i < acc_detsccs_.size(); i++)
          {
            unsigned curr_scc = acc_detsccs_[i];
            // list of deterministic states, already ordered by its labelling
            const std::vector<label> &acc_det_states = ms.detscc_labels_[i];
            std::map<unsigned, int> succ_nodes;
            for (auto & p : succ.detscc_labels_[i])
            {
              succ_nodes[p.first] = p.second;
            }

            // discontinued_runs.emplace_back(std::set<unsigned>());
            colours.emplace_back(std::set<unsigned>());
            unsigned decr = 0;
            // the runs must be from 0 to size-1
            for (unsigned j = 0; j < acc_det_states.size(); j++)
            {
              unsigned base_colour = j * (num_colours_plus_one);
              bool has_succ = false;
              unsigned s = acc_det_states[j].first;
              int curr_label = acc_det_states[j].second;
              assert(curr_label == j);
              mark_set colour_set;
              for (const auto &t : det_cache[s])
              {
                // t.first contains all colours
                // t.second is the successor
                // std::cout << "curr: " << s << " succ: " << t.second
                //   << " colour: " << t.first << std::endl;
                
                // ignore the states that are not existing any more
                if (succ_nodes.find(t.second) == succ_nodes.end())
                {
                  continue;
                }
                // 1. first they should be in the same SCC
                // 2. second the label should be equal
                if (si_.scc_of(s) == si_.scc_of(t.second) 
                  && succ_nodes[t.second] == curr_label)
                {
                  has_succ = true;
                  colour_set = t.first;
                }
              }
              if (has_succ && decr <= 0)
              {
                // ii. see a transition, record all the colours
                for (unsigned c = 0; c < num_colours_; c ++) {
                  if (colour_set.has(c)) {
                    colours[i].insert(base_colour + c);
                    // std::cout << "run " << j << " id=" << "colour=" 
                    // << base_colour + c << " from orginal colour " << c << std::endl;
                  }
                }
              }else // (!has_succ) or the labelling is going to change
              {
                ++ decr;
                // i. no successor, record the smaller label
                colours[i].insert(base_colour + num_colours_);
                // std::cout << "run " << j << " id=" << "Fin=" 
                // << base_colour + num_colours_ << std::endl;
              }
            }
            // there are still runs that comes just now or do not present for now
            // those runs should also be assigned finite colours
            unsigned num_scc_states = si_.states_of(curr_scc).size();
            for (unsigned j = acc_det_states.size(); j < num_scc_states; j ++) {
              colours[i].insert(j * num_colours_plus_one + num_colours_);
              // std::cout << "run " << j << " id=" << "Fin=" 
              //   << j * num_colours_plus_one + num_colours_ << std::endl;
            }
            // reorganize the indices
            std::sort(succ.detscc_labels_[i].begin(), succ.detscc_labels_[i].end(), label_compare);
            for (int k = 0; k < succ.detscc_labels_[i].size(); k ++)
            {
              succ.detscc_labels_[i][k].second = k;
            }
            labellings = colours;
          }

    }

    unsigned compute_run_colour(unsigned run_j, unsigned shift) {
      return run_j * num_colours_plus_one_ + shift;
    }
    
  
    // copied and adapted from deterministic.cc in Spot
    // for emerson-lei automata, we need to define stutter path
    // before using this optimisation
    void
    make_stutter_state(const elevator_mstate &curr, bdd letter, elevator_mstate &succ
      , std::pair<unsigned, std::vector<std::set<unsigned>>> &colors)
    {
      elevator_mstate ms(curr);
      // std::vector<elevator_mstate> stutter_path;
      // if (use_stutter_ && aut_->prop_stutter_invariant())
      // {
      //   std::cout << "enter stutter" << std::endl;
      //   // The path is usually quite small (3-4 states), so it's
      //   // not worth setting up a hash table to detect a cycle.
      //   stutter_path.clear();
      //   std::vector<elevator_mstate>::iterator cycle_seed;
      //   std::vector<int> mincolor(acc_detsccs_.size() + 1, -1);
      //   // stutter forward until we   cycle
      //   for (;;)
      //   {
      //     // any duplicate value, if any, is usually close to
      //     // the end, so search backward.
      //     auto it = std::find(stutter_path.rbegin(),
      //                         stutter_path.rend(), ms);
      //     if (it != stutter_path.rend())
      //     {
      //       cycle_seed = (it + 1).base();
      //       break;
      //     }
      //     stutter_path.emplace_back(std::move(ms));
      //     // next state
      //     elevator_mstate tmp_succ(si_, nb_states_);
      //     std::vector<std::set<unsigned>> det_colours;
      //     std::pair<unsigned, std::vector<std::set<unsigned>>> tmp_colours;
      //     compute_successors(stutter_path.back(), letter, tmp_succ, tmp_colours);
         
      //     ms = tmp_succ;
      //     for (unsigned i = 0; i < mincolor.size(); i++)
      //     {
      //       if (tmp_color[i] != -1 && mincolor[i] != -1)
      //       {
      //         mincolor[i] = std::min(tmp_color[i], mincolor[i]);
      //       }
      //       else if (tmp_color[i] != -1 && mincolor[i] == -1)
      //       {
      //         mincolor[i] = tmp_color[i];
      //       }
      //     }
      //   }
      //   // check whether this ms has been seen before
      //   bool in_seen = exists(*cycle_seed);
      //   for (auto it = cycle_seed + 1; it < stutter_path.end(); ++it)
      //   {
      //     if (in_seen)
      //     {
      //       // if *cycle_seed is already in seen, replace
      //       // it with a smaller state also in seen.
      //       if (exists(*it) && (*it < *cycle_seed))
      //         cycle_seed = it;
      //     }
      //     else
      //     {
      //       // if *cycle_seed is not in seen, replace it
      //       // either with a state in seen or with a smaller
      //       // state
      //       if (exists(*it))
      //       {
      //         cycle_seed = it;
      //         in_seen = true;
      //       }
      //       else if (*it < *cycle_seed)
      //       {
      //         cycle_seed = it;
      //       }
      //     }
      //   }
      //   succ = std::move(*cycle_seed);

      //   colors = mincolor;
      // }
      // else
      {
        compute_successors(ms, letter, succ, colors);
      }
    }
    bool
    is_acc_detscc(unsigned scc)
    {
      return (scc_types_[scc] & SCC_INSIDE_DET_TYPE) > 0 && (scc_types_[scc] & SCC_ACC) > 0 && ((scc_types_[scc] & SCC_WEAK_TYPE) == 0);
    }

    bool
    is_acc_weakscc(unsigned scc)
    {
      return (scc_types_[scc] & SCC_ACC) > 0 && (scc_types_[scc] & SCC_WEAK_TYPE) > 0;
    }

    // enum class acc_type {
    //   NONE = 0,
    //   FIN = 1,
    //   INF = 2,
    //   BOTH = 3
    // };

    // typedef std::bitset<2> mark_type;
    
    
    // we need to collect the colours for each SCC
    void prepare_acc(const spot::acc_cond::acc_code& acc_f) {
      mark_set used_sets = acc_f.used_sets();
      num_colours_ = used_sets.max_set();
      // std::vector<char> colour_sets;
      // for (unsigned c = 0; c < used_sets.max_set(); c ++) {
      //   colour_sets.push_back(0);
      // }
      // std::cout << "used sets: " << used_sets << std::endl;
      // std::cout << "max used sets: " << used_sets.max_set() << std::endl;

      // // compute the occurrences of colours
      // auto pos = aut_->acc().get_acceptance().size();
      // std::cout << "EL condition:" << acc_f << std::endl;
      // std::cout << "EL pos:" << pos << std::endl;

      // // there is  a shifting <<
      // while (pos > 0)
      // {
      //   auto op = acc_f[pos - 1].sub.op;
      //   auto sz = acc_f[pos - 1].sub.size;
      //   switch (op)
      //     {
      //     case spot::acc_cond::acc_op::And:
      //     case spot::acc_cond::acc_op::Or:
      //       // can we travese the operands?
      //       --pos;
      //       break;
      //     case spot::acc_cond::acc_op::Inf:
      //       pos -= 2;
      //       std::cout << "Inf mark: " << acc_f[pos].mark << std::endl;
      //       for (auto c : acc_f[pos].mark.sets()) {
      //         colour_sets[c] |= 2;
      //       }
      //       break;
      //     case spot::acc_cond::acc_op::Fin:
      //       pos -= 2;
      //       // mark is a set of colours, we need to enumerate them
      //       std::cout << "Fin mark: " << acc_f[pos].mark << std::endl;
      //       for (auto c : acc_f[pos].mark.sets()) {
      //         colour_sets[c] |= 1;
      //       }
      //       break;
      //     }
      // }
      // for (unsigned i = 0; i < colour_sets.size(); i ++) {
      //   std::cout << i << ": " << (int)colour_sets[i] << std::endl;
      // }
      // we need to collect all these colours and then 
      // create intervals for all of them
    }
  
    unsigned num_colours_plus_one_;

  public:
    elevator_determinize(const spot::const_twa_graph_ptr &aut, spot::scc_info &si, spot::option_map &om, std::vector<bdd> &implications)
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
          // is_accepting_(nb_states_),
          simulator_(aut, si, implications, om.get(USE_SIMULATION) > 0),
          delayed_simulator_(aut, om),
          show_names_(om.get(VERBOSE_LEVEL) > 0)
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
        for (const auto &out : aut->out(i))
        {
          res_support &= bdd_support(out.cond);
          res_compat |= out.cond;
        }
        support_[i] = res_support;
        compat_[i] = res_compat;
      }
      if (use_stutter_ && aut_->prop_stutter_invariant())
      {
        for (unsigned c = 0; c != si_.scc_count(); ++c)
            {
              bdd c_supp = si_.scc_ap_support(c);
              for (const auto& su: si_.succ(c))
                c_supp &= support_[si_.one_state_of(su)];
              for (unsigned st: si_.states_of(c))
                support_[st] = c_supp;
            }
      }
      // we assume that no negations
      scc_types_ = get_scc_types(si_);
      // we compute the number of colours used
      const spot::acc_cond::acc_code& aut_acc_formula = aut_->acc().get_acceptance();
      mark_set used_sets = aut_acc_formula.used_sets();
      num_colours_ = used_sets.max_set();
      num_colours_plus_one_ = num_colours_ + 1;

      // find out the accepting and deterministic SCCs
      for (unsigned i = 0; i < scc_types_.size(); i++)
      {
        if (is_acc_detscc(i))
        {
          acc_detsccs_.push_back(i);
        }
        // std::cout << "scc " << i << std::endl;
        // std::cout << " {" ;
        // for (auto s : si_.states_of(i)) {
        //   std::cout << " " << s;
        // }
        // std::cout << std::endl;
      }

      // optimize with the fact of being unambiguous
      use_unambiguous_ = use_unambiguous_ && is_unambiguous(aut);
      if (show_names_)
      {
        names_ = new std::vector<std::string>();
        res_->set_named_prop("state-names", names_);
      }
      // Because we only handle one initial state, we assume it
      // belongs to the N set. (otherwise the automaton would be
      // deterministic)
      unsigned init_state = aut->get_init_state_number();
      elevator_mstate new_init_state(si_, nb_states_);
      unsigned init_scc = si_.scc_of(init_state);
      if ((scc_types_[init_scc] & SCC_WEAK_TYPE))
      {
        new_init_state.weak_set_.insert(init_state);
      }
      else if (is_accepting_detscc(scc_types_, init_scc))
      {
        int init_scc_index = get_detscc_index(init_scc);
        new_init_state.detscc_labels_[init_scc_index].emplace_back(init_state, 0);
      }
      // we assume that the initial state is not in deterministic part
      res_->set_init_state(new_state(new_init_state));
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
      std::vector<unsigned> num_scc_colours(acc_detsccs_.size(), 0);
      std::vector<unsigned> num_scc_states(acc_detsccs_.size(), 0);
      for (unsigned i = 0; i < acc_detsccs_.size(); i++) {
        num_scc_states[i] = si_.states_of(acc_detsccs_[i]).size();
      }
      unsigned num_colours_plus_one = num_colours_plus_one_;
      // this is fixed, we can just compute it without max and min colours
      for (unsigned i = 0; i < acc_detsccs_.size(); i++)
      {
        // we compute for each DAC, how many colours needed
        num_scc_colours[i] = num_scc_states[i] * num_colours_plus_one;
        // should be equal to scc_size * (k + 1)
      }
      // now max_colors_ has the maximal color for each accepting deterministic SCC
      // compute the color base of each SCC
      std::vector<unsigned> color_bases(acc_detsccs_.size(), 0);
      // the size of max_colors must be larger than 0
      unsigned accumulated_colors = 0;
      for (unsigned i = 0; i < acc_detsccs_.size(); i++)
      {
        color_bases[i] = accumulated_colors;
        accumulated_colors += num_scc_colours[i];
      }
      unsigned weak_base = accumulated_colors;
      // std::cout << "weak_base " << weak_base << " accu " << accumulated_colors << std::endl;
      bool has_weak = false;
      bool has_weak_acc = has_weak_acc_sccs();
      for (auto &t : res_->edges())
      {
        unsigned edge_id = res_->get_graph().index_of_edge(t);
        auto p = trans2colors_.find(edge_id);
        if (p == trans2colors_.end())
        {
          throw std::runtime_error("No outgoing transition found in finalize_acceptance()");
        }
        // the list of colors, including the last one for weak SCCs
        // ->second contains first a weak and a set of colours for each DAC
        auto & det_colours = p->second.second;
        for (unsigned i = 0; i < det_colours.size(); i++)
        {
          // std::cout << "scc " << i << std::endl;
          // DAC i: base + colour
          for (auto& c : det_colours[i]) {
            t.acc.set(color_bases[i] + c );
          }
          // should be set to the relative color
        }
        // has the value of fin
        if (has_weak_acc && (p->second.first & 1))
        {
          has_weak = true;
          t.acc.set(weak_base);
        }
      }
      // now set up the acceptance
      spot::acc_cond::acc_code acceptance = spot::acc_cond::acc_code::f();
      const auto aut_acc = aut_->acc().get_acceptance();
      for (unsigned i = 0; i < acc_detsccs_.size(); i++)
      {
        unsigned num_scc_i_states = num_scc_states[i];
        // we need to set up the acceptance for every run
        for (unsigned j = 0; j < num_scc_i_states; j ++) {
          auto base = j * num_colours_plus_one;
          // std::cout << "shift " << base << " total " << color_bases[i] + base << std::endl;
          auto scc_acceptance = aut_acc << color_bases[i] + base;
          // now we need to add finitely many colours
          scc_acceptance &= spot::acc_cond::acc_code::fin({base + num_colours_});
          // std::cout << "scc " << i << " acc="<< scc_acceptance << std::endl;
          // max_colors are all odd colors, the biggest one
          acceptance |= scc_acceptance;
        }
         // first move to zero, but should be alright
      }
      if (has_weak_acc && has_weak)
      {
        acceptance |= spot::acc_cond::acc_code::fin({weak_base});
      }
      unsigned num_sets = has_weak_acc && has_weak ? weak_base + 1 : weak_base;
      // the final one
      res_->set_acceptance(num_sets, acceptance);
      // std::cout << acceptance << std::endl;
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
        elevator_mstate ms = top.first;

        // Compute support of all available states.
        bdd msupport = bddtrue;
        bdd n_s_compat = bddfalse;
        std::set<unsigned> reach_set = ms.get_reach_set();

        // compute the occurred variables in the outgoing transitions of ms, stored in msupport
        for (unsigned s : reach_set)
          {
            msupport &= support_[s];
            n_s_compat |= compat_[s];
          }

        bdd all = n_s_compat;
        while (all != bddfalse)
        {
          bdd letter = bdd_satoneset(all, msupport, bddfalse);
          all -= letter;

          elevator_mstate succ(si_, nb_states_);
          // the number of SCCs we care is the accepting det SCCs and the weak SCCs
          std::pair<unsigned, std::vector<std::set<unsigned>>> colours;
          //compute_labelling_successors(std::move(ms), top.second, letter, succ, color);
          make_stutter_state(ms, letter, succ, colours);
          // std::cout << "computed succ: " << get_name(succ) << std::endl;
          if (succ.is_empty()) continue;

          unsigned origin = top.second;
          // add transitions
          // Create the automaton states
          unsigned dst = new_state(succ);
          // first add this transition
          unsigned edge_id = res_->new_edge(origin, dst, letter);
          // handle with colors
          trans2colors_.emplace(edge_id, colours);
        }
      }
      
      res_->prop_state_acc(spot::trival(false));
      finalize_acceptance();

      res_->prop_universal(true);
      // res_->prop_deterministic(spot::trival(true));
      res_->prop_complete(true);
      if (om_.get(VERBOSE_LEVEL) >= 1)
      {
        output_file(res_, "dpa.hoa");
        std::cout << "Before simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
        if (om_.get(VERBOSE_LEVEL) >= 2) check_equivalence(aut_, res_);
      }
      if (om_.get(USE_SCC_INFO) > 0) res_ = postprocess(res_);
      if (om_.get(VERBOSE_LEVEL) >= 1)
      {
        std::cout << "After simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
        output_file(res_, "dpa1.hoa");
        if (om_.get(VERBOSE_LEVEL) >= 2) check_equivalence(aut_, res_);
      }
      
      simplify_acceptance_here(res_);
      // spot::print_hoa(std::cout, res_);
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
  determinize_televator(const spot::const_twa_graph_ptr &aut, spot::option_map &om)
  {
    if (!is_elevator_automaton(aut))
      throw std::runtime_error("determinize_teba() requires a elevator input");

    // now we compute the simulator
    spot::const_twa_graph_ptr aut_reduced;
    std::vector<bdd> implications;
    spot::twa_graph_ptr aut_tmp = nullptr;
    if (om.get(USE_SIMULATION) > 0)
    {
      aut_tmp = spot::scc_filter(aut);
      auto aut2 = spot::simulation(aut_tmp, &implications, om.get(NUM_TRANS_PRUNING));
      aut_tmp = aut2;
    }
    if (aut_tmp)
      aut_reduced = aut_tmp;
    else
      aut_reduced = aut;
    spot::scc_info scc(aut_reduced, spot::scc_info_options::ALL);
    auto det = cola::elevator_determinize(aut_reduced, scc, om, implications);
    return det.run();
  }
}