// Copyright (C) 2017-2020  The Seminator Authors
// Copyright (C) 2021  The COLA Authors
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

#include "simulation.hpp"

#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/dualize.hh>
#include <spot/twaalgos/postproc.hh>

namespace cola
{
    // adapted from RABIT/Simulation.java
    delayed_simulation::delayed_simulation(const spot::const_twa_graph_ptr nba, spot::option_map &om)
        : nba_(nba), om_(om)
    {
        if (om.get(USE_DELAYED_SIMULATION) <= 0)
        {
            return ;
        }
        unsigned n_states = nba->num_states();
        for (unsigned i = 0; i < n_states; i++)
        {
            compact_.push_back(bddfalse);
            support_.push_back(bddfalse);
        }

        std::set<unsigned> states_has_incoming_acc;
        // compute the latters and support
        for (int p = 0; p < n_states; p++)
        {
            bdd c_compact = bddfalse;
            bdd c_support = bddtrue;

            for (auto &e : nba_->out(p))
            {
                bdd cond = e.cond;
                c_compact |= cond;
                c_support &= bdd_support(cond);
                if (e.acc)
                {
                    states_has_incoming_acc.insert(e.dst);
                }
            }

            compact_[p] = c_compact;
            support_[p] = c_support;
            std::pair<unsigned, bool> s = std::make_pair(p, false);
            states_.push_back(s);
            s2index_[s] = p;
        }

        // now the number of states will be
        unsigned index = n_states;
        for (auto p : states_has_incoming_acc)
        {
            std::pair<unsigned, bool> s = std::make_pair(p, true);
            states_.push_back(s);
            s2index_[s] = index;
            ++index;
        }

        num_states_ = n_states + states_has_incoming_acc.size();
        // initialize win_region_
        for (unsigned i = 0; i < num_states_; i++)
        {
            std::vector<bool> bool_vec;
            for (unsigned j = 0; j < num_states_; j++)
            {
                bool_vec.push_back(false);
            }
            win_region_.push_back(bool_vec);
        }

        // Initialize result W (winning for spolier). This will grow by least fixpoint
        // iteration.
        for (int p = 0; p < num_states_; p++)
            for (int q = 0; q < num_states_; q++)
            {
                win_region_[p][q] = false;
                unsigned p_repr = states_[p].first;
                unsigned q_repr = states_[q].first;
                bdd act = compact_[p_repr] & !compact_[q_repr];
                // p can do action \a act, but q cannot
                if (act != bddfalse)
                {
                    win_region_[p][q] = true;
                }
            }

        bool_mat avoid;
        for (unsigned i = 0; i < num_states_; i++)
        {
            std::vector<bool> bool_vec;
            for (unsigned j = 0; j < num_states_; j++)
            {
                bool_vec.push_back(false);
            }
            avoid.push_back(bool_vec);
        }

        bool changed = true;
        while (changed)
        {
            changed = false;
            // what is the meaning?
            get_avoid_set(avoid);
            changed = get_winning_set(avoid);
        }

        if (om_.get(VERBOSE_LEVEL) >= 2)
        {
            for (unsigned p = 0; p < num_states_; p++)
                for (unsigned q = 0; q < num_states_; q++)
                    if (p == q)
                        continue;
                    else
                    {
                        if (!win_region_[p][q]) // W is winning for spoiler here, so the result is the opposite.
                        {
                            // std::cout << "(" << states_[p].first << ", " << states_[p].second << ") is simulated by "
                            //           << "(" << states_[q].first << ", " << states_[q].second << ")" << std::endl;
                            //twa::prop_set pro;
                            //twa::prop_copy(aut, pro);

                            if (states_[p].first == states_[q].first)
                            {
                                continue;
                            }
                            std::cout << states_[p].first << " is simulated by " << states_[q].first << std::endl;

                            // spot::twa::prop_set pro(false, false, false, false, false, false);
                            // spot::twa_graph_ptr p_aut = spot::make_twa_graph(nba_, pro);
                            // p_aut->set_init_state(states_[p].first);
                            // spot::twa_graph_ptr q_aut = spot::make_twa_graph(nba_, pro);
                            // q_aut->set_init_state(states_[q].first);
                            // spot::postprocessor pq;
                            // pq.set_type(spot::postprocessor::Generic);
                            // pq.set_pref(spot::postprocessor::Deterministic);
                            // spot::twa_graph_ptr qaut_c = pq.run(q_aut);
                            // qaut_c = spot::dualize(qaut_c);
                            // std::cout << "Correctness = " << !p_aut->intersects(qaut_c) << std::endl;
                        }
                    }
        }
    }

    void
    delayed_simulation::get_avoid_set(bool_mat &avoid)
    {
        // avoid = avoid_set(Q ,  old_win)
        for (int p = 0; p < num_states_; p++)
        {
            for (int q = 0; q < num_states_; q++)
            {
                // p does more than q or p sees an accepting states Winhile q does not
                avoid[p][q] = win_region_[p][q] || !(states_[q].second);
            }
        }

        // that can force to reach old_win
        int sincechanged = 0;
        while (true)
        {
            for (int p = 0; p < num_states_; p++)
                for (int q = 0; q < num_states_; q++)
                {
                    ++sincechanged;
                    // p des no more than q and no need to avoid p Winhen seeing q
                    if (!win_region_[p][q] && avoid[p][q])
                    {
                        // p does no more than q
                        if (!back_reach(p, q, avoid))
                        {
                            // no need to avoid p
                            avoid[p][q] = false;
                            sincechanged = 0;
                        }
                    }
                    if (sincechanged >= num_states_ * num_states_)
                        return;
                }
        }
    }

    bool
    delayed_simulation::get_winning_set(bool_mat &avoid)
    {
        bool changed = false;
        // imm_win = (avoid /\ P ) \/ old_win
        for (unsigned p = 0; p < num_states_; p++)
            for (unsigned q = 0; q < num_states_; q++)
            {
                // if p does more than q, continue
                if (win_region_[p][q])
                    continue;
                // p does not do more than q, but for some edge p has accepting trans, while q does not
                // isFinal(p) && avoid[p][q]
                // immediate winning, if p reach p or
                if (states_[p].second && avoid[p][q])
                {
                    win_region_[p][q] = true;
                    changed = true;
                }
            }
        int sincechanged = 0;
        // win = back_reach(imm_win)
        // p can force to a winning state
        while (true)
        {
            for (unsigned p = 0; p < num_states_; p++)
            {
                for (unsigned q = 0; q < num_states_; q++)
                {
                    ++sincechanged;
                    if (!win_region_[p][q])
                    {
                        // if p can win through a successor
                        if (back_reach(p, q, win_region_))
                        {
                            win_region_[p][q] = true;
                            changed = true;
                            sincechanged = 0;
                        }
                    }
                }
            }
            if (sincechanged >= num_states_ * num_states_)
                return (changed);
        }
    }

    unsigned get_pair_index(pair_vec &states, std::pair<unsigned, bool> pair)
    {
        for (unsigned i = 0; i < states.size(); i++)
        {
            if (pair == states[i])
                return i;
        }
        throw std::runtime_error("get_pair_index(): no such pair found");
    }

    bool
    delayed_simulation::back_reach(unsigned p, unsigned q, bool_mat &imm_win)
    {
        bool trapped = false;

        p = states_[p].first;
        q = states_[q].first;

        bdd all = compact_[p];
        bdd supp = support_[p] & support_[q];
        while (all != bddfalse)
        {
            bdd letter = bdd_satoneset(all, supp, bddfalse);
            all -= letter;
            // for the letter from p
            for (auto &e1 : nba_->out(p))
            {
                if (!bdd_implies(letter, e1.cond))
                {
                    continue;
                }
                trapped = true;
                for (auto &e2 : nba_->out(q))
                {
                    if (!bdd_implies(letter, e2.cond))
                        continue;
                    // p has a and q has a transition
                    // there exists a successor p' of p that is simulated by q'
                    bool e1_acc = e1.acc ? true : false;
                    bool e2_acc = e2.acc ? true : false;
                    std::pair<unsigned, bool> fst = std::make_pair(e1.dst, e1_acc);
                    unsigned p_succ = s2index_[fst];
                    std::pair<unsigned, bool> snd = std::make_pair(e2.dst, e2_acc);
                    unsigned q_succ = s2index_[snd];
                    if (!imm_win[p_succ][q_succ])
                    {
                        trapped = false;
                        break;
                    }
                }
                // all successors of p can not be simulated by one successor of q
                // or letter not enabled by q
                if (trapped)
                    return true;
            }
        }
        return false;
    }

}