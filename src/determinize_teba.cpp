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
#include <spot/twaalgos/hoa.hh>
#include <spot/misc/version.hh>
#include <spot/twa/acc.hh>

#include <types.hpp>


// specific determinization construction for elevator automata
// elevator automata have only deterministic SCCs and inherently weak SCCs
namespace cola
{
  // state and the labelling value
  typedef std::pair<unsigned, int> label;
  typedef std::pair<unsigned, bdd> outgoing_trans;

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
    elevator_mstate(spot::scc_info &si, size_t num, int value)
        : si_(si), ordered_states_(num, value)
    {
    }

    elevator_mstate(const elevator_mstate &other)
        : si_(other.si_)
    {
      ordered_states_.clear();
      for (unsigned i = 0; i < other.ordered_states_.size(); i++)
      {
        ordered_states_.push_back(other.ordered_states_[i]);
      }
      break_set_.clear();
      break_set_.insert(other.break_set_.begin(), other.break_set_.end());
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
      this->ordered_states_.clear();
      for (unsigned i = 0; i < other.ordered_states_.size(); i++)
      {
        this->ordered_states_.push_back(other.ordered_states_[i]);
      }
      this->break_set_.clear();
      this->break_set_.insert(other.break_set_.begin(), other.break_set_.end());
      return *this;
    }

    size_t hash() const;

    // SCC information
    spot::scc_info &si_;
    // states are ordered according to their SCCs
    std::vector<int> ordered_states_;
    // breakpoint construction for weak accepting SCCs
    std::set<unsigned> break_set_;
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
    if (ordered_states_ == other.ordered_states_)
    {
      return break_set_ < other.break_set_;
    }
    return ordered_states_ < other.ordered_states_;
  }
  bool
  elevator_mstate::operator==(const elevator_mstate &other) const
  {
    return ordered_states_ == other.ordered_states_ && break_set_ == other.break_set_;
  }
  int elevator_mstate::get_max_rank() const
  {
    int max_rnk = -1;
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      max_rnk = std::max(max_rnk, ordered_states_[i]);
    }
    return max_rnk;
  }
  bool elevator_mstate::is_empty() const
  {
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] != RANK_M)
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
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] == RANK_M)
        continue;
      result.insert(i);
    }
    return result;
  }

  std::set<unsigned>
  elevator_mstate::get_unlabelled_set() const
  {
    std::set<unsigned> result;
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] == RANK_N)
        result.insert(i);
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

  std::vector<label>
  elevator_mstate::get_detscc_states(unsigned scc) const
  {
    std::vector<label> res;
    // traverse all states
    for (unsigned i = 0; i < ordered_states_.size(); i++)
    {
      if (ordered_states_[i] == RANK_M || ordered_states_[i] == RANK_N)
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

  size_t
  elevator_mstate::hash() const
  {
    size_t res = 0;
    for (unsigned i = 0; i < ordered_states_.size(); i ++)
    {
      if (ordered_states_[i] == RANK_M) continue;
      res = (res << 3) ^ (i);
      res = (res << 3) ^ (ordered_states_[i]);
    }
    for (unsigned i : break_set_)
    {
      res ^= (res << 3) ^ i;
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
    std::unordered_map<elevator_mstate, unsigned, elevator_mstate_hash> rank2n_;

    // outgoing transition to its colors by each accepting SCCs (weak is the righmost)
    std::unordered_map<outgoing_trans, std::vector<int>, outgoing_trans_hash> trans2colors_;

    // maximal colors for each accepting SCCs
    std::vector<int> max_colors_;
    std::vector<int> min_colors_;
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
      for (unsigned i = 0; i < ms.ordered_states_.size(); i++)
        if (ms.ordered_states_[i] == RANK_N)
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
        std::vector<label> states = ms.get_detscc_states(scc_id);
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

    // remove a state i if it is simulated by a state j
    void
    make_simulation_state(elevator_mstate &ms)
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
            ms.ordered_states_[i] = RANK_M;
            ms.break_set_.erase(i);
          }
          // (j, k1) and (i, k2), if j simulates i and k1 < k2, then remove k2
          // Note that here i and j are not equivalent
          if ((simulator_.simulate(j, i) || delayed_simulator_.simulate(j, i)) && ms.ordered_states_[j] > RANK_N && (si_.scc_of(i) == si_.scc_of(j)) && ms.ordered_states_[j] < ms.ordered_states_[i])
          // if j can reach i, then scc(j) must be larger scc(i) ms[j] > RANK_N && ms[j] < ms[i])
          {
            // std::cout << j << "simulated" << i << std::endl;
            ms.ordered_states_[i] = RANK_M;
            ms.break_set_.erase(i);
          }
        }
      }
    }

    // compute the successor N={nondeterministic states and nonaccepting SCCs} O = {breakpoint for weak SCCs}
    // and labelling states for each SCC
    void
    compute_successors(const elevator_mstate &ms, bdd letter, elevator_mstate &nxt, std::vector<int> &color)
    {
      elevator_mstate succ(si_, nb_states_, RANK_M);
      // used for unambiguous automaton
      std::vector<bool> incoming(nb_states_, false);
      std::vector<bool> ignores(nb_states_, false);

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
      std::set<unsigned> unlabelled_states = ms.get_unlabelled_set();
      int max_rnk = ms.get_max_rank();

      for (unsigned s : unlabelled_states)
      {
        // nondeterministic states or states in nonaccepting SCCs
        bool in_break_set = (ms.break_set_.find(s) != ms.break_set_.end());
        for (const auto &t : aut_->out(s))
        {
          if (!bdd_implies(letter, t.cond))
            continue;
          // it is legal to ignore the states have two incoming transitions
          // in unambiguous Buchi automaton
          if (can_ignore(use_unambiguous_, t.dst)) continue;
          unsigned scc_id = si_.scc_of(t.dst);
          // we move the states in accepting det SCC to ordered states
          if (is_acc_detscc(scc_id))
          {
            succ.ordered_states_[t.dst] = max_rnk + 1; //Sharing labels
          }
          else
          {
            // weak states or nondeterministic or nonaccepting det scc
            succ.ordered_states_[t.dst] = RANK_N;
            bool in_acc_set = // must be accepting and weak
                (scc_types_[scc_id] & SCC_ACC) > 0 && (scc_types_[scc_id] & SCC_WEAK_TYPE) > 0;
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
        }
      }
      // std::cout << "After nondeterministic: " << get_name(succ) << std::endl;

      //2. Compute the labelling successors
      const int MAX_RANK = max_rnk + 3;
      std::vector<std::pair<int, int>> min_labellings;

      for (unsigned i = 0; i < acc_detsccs_.size(); i++)
      {
        unsigned scc_curr_id = acc_detsccs_[i];
        // list of deterministic states, already ordered by its labelling
        std::vector<label> acc_det_states = ms.get_detscc_states(scc_curr_id);
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

            // NORMAL way, inherit the labelling
            //int update_rnk = label;
            unsigned scc_succ_id = si_.scc_of(t.dst);
            // get out of the SCC and go to non-accepting or deterministic SCC
            // 1). go to a different SCC and it is not accepting deterministic SCC
            //      in this case, the state is not labelled
            if (scc_curr_id != scc_succ_id && !is_acc_detscc(scc_succ_id))
            {
              succ.ordered_states_[t.dst] = RANK_N; // go back to nondeterministic part
              bool in_acc_set =    // must be accepting and weak
                  (scc_types_[scc_succ_id] & SCC_ACC) > 0 && (scc_types_[scc_succ_id] & SCC_WEAK_TYPE) > 0;
              // record accepting weak SCC states
              if (in_acc_set)
              {
                acc_weak_coming_states.insert(t.dst);
              }
            } else if (scc_curr_id != scc_succ_id && is_acc_detscc(scc_succ_id))
            {
              //2). go to a different and smaller accepting deterministic SCC
              // if it is a new state entering that SCC
              if (succ.ordered_states_[t.dst] < RANK_N)
              {
                succ.ordered_states_[t.dst] = max_rnk + 1;
              }
              // else it is not new, must already inherit some labelling
            } else if (scc_curr_id == scc_succ_id)
            {
              //2). stay in the same accepting deterministic SCC
              // will inherit the same labelling
      
              // else the successor is also in the same scc, no change, inherit the labelling
              if (succ.ordered_states_[t.dst] == RANK_M) succ.ordered_states_[t.dst] = curr_label;
              else succ.ordered_states_[t.dst] = std::min(succ.ordered_states_[t.dst], curr_label);
            }
          }
        }
      }
      
      // remove redudant states
      if (use_simulation_)
      {
        make_simulation_state(succ);
      }
      min_labellings.clear();
        // record the numbers
        for (unsigned i = 0; i < acc_detsccs_.size(); i++)
        {
          unsigned scc_curr_id = acc_detsccs_[i];
          int min_acc = MAX_RANK;
          int min_dcc = MAX_RANK;
          // list of deterministic states, already ordered by its labelling
          std::vector<label> acc_det_states = ms.get_detscc_states(scc_curr_id);
          // std::cout << "Computing scc " << scc_curr_id << "\n";
          // print_label_vec(acc_det_states);
          for (unsigned j = 0; j < acc_det_states.size(); j++)
          {
            bool has_succ = false;
            bool has_acc = false;
            unsigned s = acc_det_states[j].first;
            int curr_label = acc_det_states[j].second;
            assert (curr_label == j);
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
              if (si_.scc_of(s) == si_.scc_of(t.dst)
              && succ.ordered_states_[t.dst] == curr_label)
              {
                has_succ = true;
                has_acc = has_acc || t.acc;
              }
            }
            if (!has_succ && min_dcc == MAX_RANK)
            {
              // i. no successor, record the smaller label 
              min_dcc = j;
            } else if (has_acc && min_acc == MAX_RANK)
            {
              // ii. see an accepting transition
              min_acc = j;
            }
          }
          // record the pair of labellings for the SCC
          min_labellings.emplace_back(min_dcc, min_acc);
        }

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
        int parity;
        int min_dcc = min_labellings[i].first;
        int min_acc = min_labellings[i].second;
        if (min_dcc == MAX_RANK && min_acc != MAX_RANK)
        {
          parity = 2 * (min_acc + 1);
        }
        else if (min_dcc != MAX_RANK && min_acc == MAX_RANK)
        {
          parity = 2 * min_dcc + 1;
        }
        else if (min_dcc != MAX_RANK && min_acc != MAX_RANK)
        {
          parity = std::min(2 * min_dcc + 1, 2 * min_acc + 2);
        }
        else
        {
          parity = -1;
        }
        colors.push_back(parity);
      }
      // give color for the weak SCCs
      if (break_empty)
      {
        colors.push_back(1);
      }
      else
      {
        colors.push_back(2);
      }

      //4. Reorgnize the indices of each accepting deterministic SCC
      for (unsigned i = 0; i < acc_detsccs_.size(); i++)
      {
        std::vector<label> acc_det_states = succ.get_detscc_states(acc_detsccs_[i]);
        for (unsigned j = 0; j < acc_det_states.size(); j++)
        {
          succ.ordered_states_[acc_det_states[j].first] = j;
        }
      }

      nxt = succ;
      color = colors;
    }
    // copied and adapted from deterministic.cc in Spot
    void
    make_stutter_state(const elevator_mstate &curr, bdd letter, elevator_mstate &succ, std::vector<int> &colors)
    {
      elevator_mstate ms(curr);
      std::vector<elevator_mstate> stutter_path;
      if (use_stutter_ && aut_->prop_stutter_invariant())
      {
        // The path is usually quite small (3-4 states), so it's
        // not worth setting up a hash table to detect a cycle.
        stutter_path.clear();
        std::vector<elevator_mstate>::iterator cycle_seed;
        std::vector<int> mincolor(acc_detsccs_.size() + 1, -1);
        // stutter forward until we   cycle
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
          elevator_mstate tmp_succ(si_, nb_states_, RANK_M);
          std::vector<int> tmp_color(acc_detsccs_.size() + 1, -1);
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
      scc_types_ = get_scc_types(si_);
      // find out the accepting and deterministic SCCs
      for (unsigned i = 0; i < scc_types_.size(); i++)
      {
        if (is_acc_detscc(i))
        {
          acc_detsccs_.push_back(i);
          max_colors_.push_back(-1);
          min_colors_.push_back(INT_MAX);
        }
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
      elevator_mstate new_init_state(si_, nb_states_, RANK_M);
      if (! is_acc_detscc(si_.scc_of(init_state)))
      {
        new_init_state.ordered_states_[init_state] = RANK_N;
      }else 
      {
        new_init_state.ordered_states_[init_state] = 0;
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
        // std::cout << "SCC " << acc_detsccs_[i] << " max_color = " << max_colors_[i] << " min_color = " << min_colors_[i] << std::endl;
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
    run()
    {
      std::unordered_map<bdd, std::vector<bdd>, spot::bdd_hash> cache;
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
        for (unsigned s = 0; s < nb_states_; ++s)
          if (ms.ordered_states_[s] != RANK_M)
          {
            msupport &= support_[s];
            // n_s_compat |= compat_[s];
          }
      
      auto i = cache.emplace(msupport, std::vector<bdd>());
      if (i.second) // 
      {
          std::vector<bdd>& rs = i.first->second;
          //enumerate all possible letters
          for (bdd one: minterms_of(bddtrue, msupport))
              rs.emplace_back(one);
      }
      const std::vector<bdd>& letters_vec = i.first->second;
      for (auto & letter : letters_vec)
      {
          elevator_mstate succ(si_, nb_states_, RANK_M);
          // the number of SCCs we care is the accepting det SCCs and the weak SCCs
          std::vector<int> colors(acc_detsccs_.size() + 1, -1);
          //compute_labelling_successors(std::move(ms), top.second, letter, succ, color);
          make_stutter_state(ms, letter, succ, colors);
      
          if (succ.is_empty()) continue;

          unsigned origin = top.second;
          // add transitions
          // Create the automaton states
          unsigned dst = new_state(succ);
          // first add this transition
          res_->new_edge(origin, dst, letter);
          // handle with colors
          for (unsigned i = 0; i < colors.size(); i++)
          {
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
          trans2colors_.emplace(std::make_pair(origin, letter), colors);
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
      if (om_.get(USE_SCC_INFO) > 0) res_ = postprocess(res_);
      if (om_.get(VERBOSE_LEVEL) >= 1)
      {
        std::cout << "After simplification #States: " << res_->num_states() << " #Colors: " << res_->num_sets() << std::endl;
        output_file(res_, "dpa1.hoa");
        if (om_.get(VERBOSE_LEVEL) >= 2) check_equivalence(aut_, res_);
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
  determinize_televator(const spot::const_twa_graph_ptr &aut, spot::option_map &om)
  {
    if (!is_elevator_automaton(aut))
      throw std::runtime_error("determinize_teba() requires a elevator input");

    // now we compute the simulator
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
    auto det = cola::elevator_determinize(aut_reduced, scc, om, implications);
    return det.run();
  }
}