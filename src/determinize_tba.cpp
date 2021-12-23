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

// #include "optimizer.hpp"
#include "cola.hpp"
//#include "struct.hpp"

#include <deque>
#include <map>
#include <set>
#include <algorithm>
#include <functional>

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

#include <types.hpp>

// Determinization of TBAs via semi-determinization of TBAs and determinization of TLDBAs
namespace cola
{

  template <class T>
  struct pair_compare
  {
    bool operator()(const std::pair<T, T> &lhs,
                    const std::pair<T, T> &rhs) const
    {
      if (lhs.first == rhs.first)
        return lhs.second < rhs.second;
      else
        return lhs.first < rhs.first;
    }
  };
  // using state_t = unsigned;
  // using state_set = state_set;
  //using node_t = std::pair<, state_set>;
  const int RANK_N = -1; // nondeterministic
  const int RANK_M = -2; // missing value

  void copy_set_to(state_set &S1, state_set &S2)
  {
    for (auto s : S1)
    {
      S2.insert(s);
    }
  }
  // macrostate
  class mstate final
  {
    void
    check() const
    {
      // all states in P and Q are in reach_set_ and Q \subseteq P
      assert(qset_.size() == pset_.size());
      unsigned num = qset_.size();
      for (unsigned i = 0; i < num; i++)
      {
        for (state_t s : qset_[i])
        {
          assert(pset_[i].find(s) != pset_[i].end());
        }
        for (state_t s : pset_[i])
        {
          assert(reach_set_.find(s) != reach_set_.end());
        }
      }
    }

  public:
    // this constructor is only for the initial state
    mstate(state_t init_state)
    {
      reach_set_.insert(init_state);
    }
    mstate(const mstate &other)
    {
      reach_set_.clear();
      state_set oreach_set = other.reach_set_;
      copy_set_to(oreach_set, reach_set_);
      pset_.clear();
      qset_.clear();
      for (unsigned i = 0; i < other.pset_.size(); i++)
      {
        state_set pset;
        state_set qset;
        state_set opset = other.pset_[i];
        state_set oqset = other.qset_[i];
        copy_set_to(opset, pset);
        copy_set_to(oqset, qset);
        pset_.push_back(pset);
        qset_.push_back(qset);
      }
    }
    mstate() {}
    bool operator<(const mstate &other) const;
    bool operator==(const mstate &other) const;

    size_t hash() const;

    // A macrostate consists of a set of NBA-states S (reach_set)
    // and a sequence of deterministic LDBA-states (without explicit construction)
    // (P_0, Q_0), (P_1, Q_1), ..., (P_k, Q_k) represented by (pset_, qset_)
    // the set of reachable states in this level
    state_set reach_set_;
    // this is the list of nodes that ordered due to later introduction record
    std::vector<state_set> qset_;
    std::vector<state_set> pset_;
  };

  size_t
  hash_unsigned_set(const state_set &uset)
  {
    size_t hash = 0;
    for (auto i : uset) // not sure how you're storing them
    {
      hash = ((31 * hash) + (unsigned)i);
    }
    return hash;
  }

  bool
  mstate::operator<(const mstate &other) const
  {
    if (reach_set_ < other.reach_set_)
    {
      return true;
    }
    if (reach_set_ > other.reach_set_)
    {
      return false;
    }
    if (pset_.size() < other.pset_.size())
    {
      return true;
    }
    if (pset_.size() > other.pset_.size())
    {
      return false;
    }
    for (unsigned i = 0; i < pset_.size(); i++)
    {
      if (pset_[i] < other.pset_[i])
      {
        return true;
      }
      if (pset_[i] > other.pset_[i])
      {
        return false;
      }
      if (qset_[i] < other.qset_[i])
      {
        return true;
      }
      if (qset_[i] > other.qset_[i])
      {
        return false;
      }
    }
    return false;
  }
  bool
  mstate::operator==(const mstate &other) const
  {
    if (reach_set_ != other.reach_set_)
    {
      return false;
    }
    if (pset_.size() != other.pset_.size())
    {
      return false;
    }
    for (unsigned i = 0; i < pset_.size(); i++)
    {
      if (pset_[i] != other.pset_[i])
      {
        return false;
      }
      if (qset_[i] != other.qset_[i])
      {
        return false;
      }
    }
    return true;
  }

  size_t
  mstate::hash() const
  {
    size_t res = 0;

    for (unsigned i = 0; i < pset_.size(); i++)
    {
      res ^= (res << 3) ^ hash_unsigned_set(pset_[i]);
      res ^= (res << 3) ^ hash_unsigned_set(qset_[i]);
    }
    for (state_t s : reach_set_)
    {
      res ^= (res << 3) ^ s;
    }
    return res;
  }

  std::string
  get_name(const mstate &ms)
  {
    std::string res = get_set_string(ms.reach_set_) + ",[";
    bool first = true;
    for (unsigned i = 0; i < ms.pset_.size(); i++)
    {
      if (!first)
      {
        res += ", ";
      }
      else
      {
        first = false;
      }
      res += "(" + get_set_string(ms.pset_[i]) + ", " 
                 + get_set_string(ms.qset_[i]) + ") = "
                 + std::to_string(i);
    }
    res += "]";
    return res;
  }
  struct mstate_hash
  {
    size_t
    operator()(const mstate &s) const noexcept
    {
      return s.hash();
    }
  };

  // x is contained in y
  bool
  is_subset(state_set &x, state_set &y)
  {
    for (auto s : x)
    {
      if (y.find(s) == y.end())
      {
        return false;
      }
    }
    return true;
  }

  class tba_determinize
  {
  private:
    // The source automaton.
    const spot::const_twa_graph_ptr aut_;

    // SCCs information of the source automaton.
    spot::scc_info si_;

    //optimizer opt_;

    // Number of states in the input automaton.
    unsigned nb_states_;

    // simulation relation of source automaton;
    state_simulator simulator_;

    // The parity automata being built.
    spot::twa_graph_ptr res_;

    // the number of indices
    unsigned sets_ = 0;

    // option map
    spot::option_map &om_;

    // number of colors used
    unsigned num_colors_;

    // use ambiguous
    bool use_unambiguous_;
    // 
    bool use_simulation_;
    // use optimization with SCC information
    bool use_scc_;
    // use stutter
    bool use_stutter_;

    // Association between labelling states and state numbers of the
    // DPA.
    std::unordered_map<mstate, unsigned, mstate_hash> rank2n_;

    // States to process.
    std::deque<std::pair<mstate, unsigned>> todo_;

    // Support for each state of the source automaton.
    std::vector<bdd> support_;

    // Propositions compatible with all transitions of a state.
    std::vector<bdd> compat_;

    // Whether a SCC is deterministic or not
    //std::vector<bool> is_deter_;

    // Whether a state only has accepting transitions
    std::vector<bool> is_accepting_;

    // State names for graphviz display
    std::vector<std::string> *names_;

    // Show Rank states in state name to help debug
    bool show_names_;

    // From a Rank state, looks for a duplicate in the map before
    // creating a new state if needed.
    unsigned
    new_state(mstate &s)
    {
      //std::cout << "new state: " << get_name(s) << std::endl;
      //mstate s_p(s);
      // std::cout << "copy state: " << get_name(s) << std::endl;
      auto p = rank2n_.emplace(s, 0);
      if (p.second) // This is a new state
      {
        p.first->second = res_->new_state();
        if (show_names_)
          names_->push_back(get_name(p.first->first));
        todo_.emplace_back(s, p.first->second);
      }
      return p.first->second;
    }

    bool exists(mstate &s)
    {
      return rank2n_.end() == rank2n_.find(s);
    }

    // remove a state i if it is simulated by a state j
    void
    make_simulation_state(mstate &ms)
    {
      state_set reached_states;
      state_set removed_states;
      for (auto s : ms.reach_set_)
      {
        reached_states.insert(s);
      }
      for (unsigned i : reached_states)
      {
        for (unsigned j : reached_states)
        {
          // if j is not reached at this level
          if (i == j)
            continue;
          //std::cout << "start simulated" << std::endl;
          // j simulates i and j cannot reach i
          if (simulator_.simulate(j, i) && simulator_.can_reach(j, i) == 0)
          {
            removed_states.insert(i);
          }
        }
      }
      // now remove all states in removed_states
      ms.reach_set_.erase(removed_states.begin(), removed_states.end());
      for (unsigned i = 0; i < ms.pset_.size(); i++)
      {
        ms.pset_[i].erase(removed_states.begin(), removed_states.end());
        ms.qset_[i].erase(removed_states.begin(), removed_states.end());
      }
      // keep the empty set
      //compare (P1, Q1) and (P2, Q2) such that P1 = P2, and Q1 \superset Q2
      // then the language of (P1, Q1) includes the language of (P2, Q2)
      std::set<unsigned> removed_indices;
      for (unsigned i = 0; i < ms.pset_.size(); i++)
      {
        if (ms.pset_[i].empty())
          continue;
        for (unsigned j = i + 1; j < ms.pset_.size(); j++)
        {
          if ((ms.pset_[i] == ms.pset_[j]) && is_subset(ms.qset_[j], ms.qset_[i]))
          {
            removed_indices.insert(j);
          }
        }
      }
      // if (om_.get(VERBOSE_LEVEL) > 0) 
        // std::cout << "Removed indices: " << removed_indices.size() << "\n";
      // clear those indices
      for (unsigned i : removed_indices)
      {
        ms.pset_[i].clear();
        ms.qset_[i].clear();
      }
    }

    std::pair<state_set, state_set>
    get_set_successors(const state_set &P, const state_set &Q, bdd letter, const state_set &restricts, bool &acc)
    {
      state_set p_prime;
      state_set p_acc_prime;
      state_set q_dprime;
      state_set q_prime;

      for (auto s : P)
      {
        for (const auto &t : aut_->out(s))
        {
          // ignore unreachable states and states that are not in restructs
          if (!bdd_implies(letter, t.cond) 
               || (restricts.find(t.dst) == restricts.end()))
            continue;
          p_prime.insert(t.dst);
          if (t.acc || is_accepting_[t.dst])
          {
            p_acc_prime.insert(t.dst);
          }
          if (Q.find(s) != Q.end())
          {
            q_prime.insert(t.dst);
          }
        }
      }
      // std::cout << "P = " << get_set_string(P) << " Q = " << get_set_string(Q) << " letter = " << letter << std::endl;
      // std::cout << "P' = " << get_set_string(p_prime) << " Q' = " << get_set_string(q_prime) << " PA' = " << get_set_string(p_acc_prime) << std::endl;
      q_dprime.insert(q_prime.begin(), q_prime.end());
      q_dprime.insert(p_acc_prime.begin(), p_acc_prime.end());
      if (q_dprime == p_prime)
      {
        acc = !p_prime.empty();
        q_prime = p_acc_prime;
      }
      else
      {
        acc = false;
        q_prime = q_dprime;
      }
      // std::cout << "Final : P' = " << get_set_string(p_prime) << " Q' = " << get_set_string(q_prime) << std::endl;
      return std::make_pair(p_prime, q_prime);
    }

    void
    rank_successors(const mstate &ms, unsigned origin, bdd letter, mstate &nxt, int &color)
    {
      mstate succ;
      std::vector<bool> incoming(nb_states_, false);
      std::vector<bool> ignores(nb_states_, false);
      // first handle nondeterministic states
      std::set<unsigned> coming_states;
      //std::vector<unsigned> acc_coming_states;
      for (unsigned s : ms.reach_set_)
      {
        for (const auto &t : aut_->out(s))
        {
          if (!bdd_implies(letter, t.cond))
            continue;
          // it is legal to ignore the states have two incoming transitions
          // in unambiguous Buchi automaton
          if (use_unambiguous_)
          {
            if (incoming[t.dst])
            {
              // this is the second incoming transitions
              ignores[t.dst] = true;
            }
            else
            {
              incoming[t.dst] = true;
            }
          }
          if (ignores[t.dst])
          {
            // ignore this state
            continue;
          }
          succ.reach_set_.insert(t.dst);
          // via accepting transitions
          if (t.acc || is_accepting_[t.dst])
          {
            coming_states.insert(t.dst);
          }
        }
      }
      // now compute the successors for (P, Q) states
      std::set<std::pair<std::string, std::string>, pair_compare<std::string>> visited;
      unsigned acc_index = ms.pset_.size();
      unsigned rej_index = ms.pset_.size();
      for (unsigned i = 0; i < ms.pset_.size(); i++)
      {
        bool accepting_trans = false;
        std::pair<state_set, state_set> set_pair = get_set_successors(ms.pset_[i], ms.qset_[i], letter, succ.reach_set_, accepting_trans);
        state_set pset_succ = set_pair.first;
        state_set qset_succ = set_pair.second;
        // std::cout << "P = " << get_set_string(ms.pset_[i]) << " Q = " << get_set_string(ms.qset_[i]) << std::endl;
        // std::cout << "P' = " << get_set_string(pset_succ) << " Q' = " << get_set_string(qset_succ) << " Acc = " << accepting_trans << std::endl;
        // check whether this set is already existing
        std::pair<std::string, std::string> str_pair = std::make_pair(get_set_string(pset_succ), get_set_string(qset_succ));
        if (visited.find(str_pair) == visited.end())
        {
          succ.pset_.push_back(pset_succ);
          succ.qset_.push_back(qset_succ);
          visited.insert(str_pair);
        }
        else
        // already there, so ignore
        {
          rej_index = std::min(rej_index, i);
        }
        if (accepting_trans)
        {
          acc_index = std::min(acc_index, i);
        }
      }
      for (auto s : coming_states)
      {
        state_set acc_set;
        acc_set.insert(s);
        state_set empty_set;
        std::pair<std::string, std::string> str_pair = std::make_pair(get_set_string(acc_set), get_set_string(empty_set));
        if (visited.find(str_pair) == visited.end())
        {
          succ.pset_.push_back(acc_set);
          succ.qset_.push_back(empty_set);
        }
      }
      // std::cout << "state= " << get_name(ms) << " letter = " << letter << std::endl;
      // std::cout << "State before simulation: " << get_name(succ) << std::endl;
      // remove redudant states
      if (use_simulation_)
        make_simulation_state(succ);
      // std::cout << "State after simulation: " << get_name(succ) << std::endl;
      // now compute min_dcc (minimal index disappeared) and min_acc (minimal index accepted)
      // std::cout << "ms-num= " << ms.pset_.size() << " succ-num=" << succ.pset_.size() << std::endl;
      //rej_index = std::min(rej_index, succ.pset_.size());
      for (unsigned i = 0; i < ms.pset_.size() && i < succ.pset_.size(); i++)
      {
        if (succ.pset_[i].empty())
        {
          rej_index = std::min(rej_index, i);
        }
        else if (succ.pset_[i] == succ.qset_[i])
        {
          acc_index = std::min(acc_index, i);
        }
      }
      //std::cout << "Acc = " << acc_index << " rej = " << rej_index << "\n";

      int parity;
      int acc_color = 2 * ((int)acc_index + 1);
      int rej_color = 2 * ((int)rej_index) + 1;
      if (rej_index == ms.pset_.size() && acc_index != ms.pset_.size())
      {
        parity = acc_color;
      }
      else if (rej_index != ms.pset_.size() && acc_index == ms.pset_.size())
      {
        parity = rej_color;
      }
      else if (rej_index != ms.pset_.size() && acc_index != ms.pset_.size())
      {
        parity = std::min(acc_color, rej_color);
      }
      else
      {
        parity = -1;
      }
      std::vector<state_set> pset;
      std::vector<state_set> qset;
      // std::cout << "Reorganize  \n";
      visited.clear();
      for (unsigned i = 0; i < succ.pset_.size(); i++)
      {
        std::pair<std::string, std::string> str_pair = std::make_pair(get_set_string(succ.pset_[i]), get_set_string(succ.qset_[i]));
        if (visited.find(str_pair) == visited.end() && !succ.pset_[i].empty())
        {
          pset.push_back(succ.pset_[i]);
          qset.push_back(succ.qset_[i]);
        }
      }
      succ.pset_ = pset;
      succ.qset_ = qset;
      // std::cout << "Final state = " << get_name(succ) << " color=" << parity<< std::endl;
      // now we find whether there is bisimulate-states
      //new_bisim_state(succ);
      nxt = succ;
      color = parity;
    }
    // copied and adapted from deterministic.cc in Spot
    void
    make_stutter_state(const mstate &curr, unsigned origin, bdd letter, mstate &succ, int &color)
    {
      mstate ms(curr);
      std::vector<mstate> stutter_path;
      if (use_stutter_ && aut_->prop_stutter_invariant())
      {
        // The path is usually quite small (3-4 states), so it's
        // not worth setting up a hash table to detect a cycle.
        stutter_path.clear();
        std::vector<mstate>::iterator cycle_seed;
        int mincolor = -1;
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
          stutter_path.emplace_back(ms);
          // next state
          mstate tmp_succ;
          int tmp_color = -1;
          rank_successors(stutter_path.back(), origin, letter, tmp_succ, tmp_color);
          ms = tmp_succ;
          if (tmp_color != -1 && mincolor != -1)
          {
            mincolor = std::min(tmp_color, mincolor);
          }
          else if (tmp_color != -1)
          {
            mincolor = tmp_color;
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
            if (exists(*it) && *it < *cycle_seed)
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
        succ = *cycle_seed;
        color = mincolor;
      }
      else
      {
        rank_successors(ms, origin, letter, succ, color);
      }
    }

  public:
    tba_determinize(const spot::const_twa_graph_ptr &aut, spot::option_map &om)
        : aut_(aut),
          om_(om),
          use_simulation_(om.get(USE_SIMULATION) > 0),
          use_scc_(om.get(USE_SCC_INFO) > 0),
          use_stutter_(om.get(USE_STUTTER) > 0),
          use_unambiguous_(om.get(USE_UNAMBIGUITY) > 0),
          si_(aut, spot::scc_info_options::ALL),
          nb_states_(aut->num_states()),
          support_(nb_states_),
          compat_(nb_states_),
          is_accepting_(nb_states_),
          simulator_(aut_, si_, use_simulation_),
          show_names_(om.get(VERBOSE_LEVEL) >= 2)
    {
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
        // all outgoing transitions are accepting
        is_accepting_[i] = accepting && has_transitions;
      }
      // optimize with the fact of being unambiguous
      use_unambiguous_ = use_unambiguous_ && is_unambiguous(aut);
      if (show_names_)
      {
        names_ = new std::vector<std::string>();
        res_->set_named_prop("state-names", names_);
      }
      unsigned init_state = aut->get_init_state_number();
      mstate new_init_state(init_state);
      unsigned index = new_state(new_init_state);
      res_->set_init_state(index);
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
        mstate ms = top.first;
        // Compute support of all available states.
        bdd msupport = bddtrue;
        bdd n_s_compat = bddfalse;
        // compute the occurred variables in the outgoing transitions of ms
        //, stored in msupport
        for (unsigned s : ms.reach_set_)
        {
          msupport &= support_[s];
          n_s_compat |= compat_[s];
        }

        bdd all = n_s_compat;
        while (all != bddfalse)
        {
          bdd letter = bdd_satoneset(all, msupport, bddfalse);
          all -= letter;
          // Compute all new states available from the generated
          // letter.

          mstate succ;
          int color = -1;
          // std::cout << "Current state=" << get_name(ms) << std::endl;
          //rank_successors(std::move(ms), top.second, letter, succ, color);
          make_stutter_state(ms, top.second, letter, succ, color);

          unsigned origin = top.second;
          // add transitions
          // Create the automaton states
          unsigned dst = new_state(succ);
          // const unsigned MAX_PRI = 2* nb_det_states_ + 1;
          if (color >= 0)
          {
            unsigned pri = (unsigned)color;
            sets_ = std::max(pri, sets_);
            res_->new_edge(origin, dst, letter, {pri});
          }
          else
          {
            res_->new_edge(origin, dst, letter);
          }
        }
      }
      // check the number of indices
      unsigned max_odd_pri = -1;
      // sets_ stores the maximal priority has ever seen
      if (sets_ & 1)
      {
        max_odd_pri = sets_;
      }
      else
      {
        max_odd_pri = sets_ + 1;
      }

      for (auto &t : res_->edges())
      {
        if (t.acc.count() <= 0)
        {
          t.acc = spot::acc_cond::mark_t{max_odd_pri};
        }
      }
      // Acceptance is now min(odd) since we can emit Red on paths 0 with new opti
      num_colors_ = max_odd_pri + 1;

      res_->set_acceptance(num_colors_, spot::acc_cond::acc_code::parity_min_even(num_colors_));
      if (aut_->prop_complete().is_true())
        res_->prop_complete(true);
      res_->prop_universal(true);
      res_->prop_state_acc(false);
      res_ = postprocess(res_);
      cleanup_parity_here(res_);
      return res_;
    }

    spot::twa_graph_ptr
    postprocess(spot::twa_graph_ptr aut)
    {
      // set of states -> the forest of reachability in the states.
      mstate_equiv_map set2scc;
      // record the representative of every SCC
      for (auto p = rank2n_.begin(); p != rank2n_.end(); p++)
      {
        std::set<unsigned> set;
        for (unsigned s : p->first.reach_set_)
        {
          set.insert(s);
        }
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
      mstate_merger merger(aut, set2scc);
      spot::twa_graph_ptr res = merger.run();
      if (om_.get(VERBOSE_LEVEL) >= 1)
        std::cout << "The number of states reduced by mstate_merger: "
                  << (aut->num_states() - res->num_states()) << " {out of "
                  << aut->num_states() << "}" << std::endl;
      return res;
    }
  };

  spot::twa_graph_ptr
  determinize_tba(const spot::const_twa_graph_ptr &aut, spot::option_map &om)
  {
    if (!aut->acc().is_buchi())
      throw std::runtime_error("determinize_tba() requires a Buchi input");

    auto det = cola::tba_determinize(aut, om);
    return det.run();
  }
}