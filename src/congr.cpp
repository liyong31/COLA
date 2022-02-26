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
#include "congr.hpp"
#include "simulation.hpp"
#include "types.hpp"
//#include "struct.hpp"

#include <deque>
#include <map>
#include <set>

#include <spot/twa/bddprint.hh>

namespace cola
{

	bool arc::operator<(const arc &other) const
	{
		if (src_ != other.src_)
		{
			return src_ < other.src_;
		}
		if (dst_ != other.dst_)
		{
			return dst_ < other.dst_;
		}
		return acc_ - other.acc_;
	}
	bool arc::operator==(const arc &other) const
	{
		return src_ == other.src_ && dst_ == other.dst_ && acc_ == other.acc_;
	}
	arc &arc::operator=(const arc &other)
	{
		src_ = other.src_;
		dst_ = other.dst_;
		acc_ = other.acc_;
		return *this;
	}

	size_t arc::hash() const
	{
		size_t res = 0;
		res = (res << 3) ^ src_;
		res = (res << 3) ^ dst_;
		res = (res << 3) ^ (acc_ ? 1 : 0);
		return res;
	}

	ostream &operator<<(ostream &os, const arc &c)
	{
		os << "(" << c.src_ << ", " << c.dst_ << ": " << c.acc_ << ")";
		return os;
	}

	bool prefix_graph::operator<(const prefix_graph &other) const
	{
		if (repr_ != other.repr_)
		{
			return repr_ < other.repr_;
		}
		return false;
	}
	bool prefix_graph::operator==(const prefix_graph &other) const
	{
		return repr_ == other.repr_;
	}
	prefix_graph &prefix_graph::operator=(const prefix_graph &other)
	{
		//repr_.clear();
		repr_ = other.repr_; 
		word_ = other.word_;
		return *this;
	}
	size_t prefix_graph::hash() const
	{
		size_t res = 0;
		for (unsigned s : repr_)
		{
			res = (res << 3) ^ s;
		}
		return res;
	}

	ostream &operator<<(ostream &os, const prefix_graph &g)
	{
		os << get_set_string(g.repr_) << " :";
		for (const bdd &b : g.word_)
		{
			os << " " << b;
		}
		return os;
	}

	bool period_graph::operator<(const period_graph &other) const
	{
		if (repr_ != other.repr_)
		{
			return repr_ < other.repr_;
		}
		return false;
	}
	bool period_graph::operator==(const period_graph &other) const
	{
		return repr_ == other.repr_;
	}
	period_graph &period_graph::operator=(const period_graph &other)
	{
		repr_.clear();
		repr_.insert(other.repr_.begin(), other.repr_.end());
		word_ = other.word_;
		return *this;
	}
	size_t period_graph::hash() const
	{
		size_t res = 0;
		for (const arc &s : repr_)
		{
			res = (res << 3) ^ s.hash();
		}
		return res;
	}

	ostream &operator<<(ostream &os, const period_graph &g)
	{
		os << "{";
		bool first = true;
		for (const arc &r : g.repr_)
		{
			if (!first)
				os << ", ";
			os << r;
			first = false;
		}
		os << " :";
		for (const bdd &b : g.word_)
		{
			os << " " << b;
		}
		os << "}";
		return os;
	}

	congr::congr(spot::option_map &om, spot::twa_graph_ptr B, spot::scc_info &si_B, spot::twa_graph_ptr A, spot::scc_info &si_A, std::vector<bdd> &implications)
		: om_(om), A_(A), B_(B), si_B_(si_B), si_A_(si_A), simulator_(B, si_B, implications, om.get(USE_SIMULATION) > 0)
	{
		std::cout << "Reached here" << std::endl;
		// first, make A_ state-based
		support_A_ = std::vector<bdd>(A_->num_states(), bddfalse);
		compact_A_ = std::vector<bdd>(A_->num_states(), bddfalse);
		is_accepting_A_ = std::vector<bool>(A_->num_states(), false);

		// now collect info of A
		for (unsigned i = 0; i < A_->num_states(); i++)
		{
			prefix_map_.emplace(i, std::set<prefix_graph>());
			bdd res_support = bddtrue;
			bdd res_compat = bddfalse;
			bool accepting = true;
			bool has_transitions = false;
			for (const auto &out : A_->out(i))
			{
				has_transitions = true;
				res_support &= bdd_support(out.cond);
				res_compat |= out.cond;
				if (!out.acc)
					accepting = false;
			}
			support_A_[i] = res_support;
			compact_A_[i] = res_compat;
			is_accepting_A_[i] = accepting && has_transitions;
		}
		std::cout << "Support of A computed..\n";
		scc_types_B_ = get_scc_types(si_B_);
		support_B_ = std::vector<bdd>(B_->num_states(), bddfalse);
		for (unsigned i = 0; i < B_->num_states(); i++)
		{
			bdd res_support = bddtrue;
			for (const auto &out : B_->out(i))
			{
				res_support &= bdd_support(out.cond);
			}
			support_B_[i] = res_support;
		}
		std::cout << "Support of B computed..\n";
	}

	void congr::add_to_minimized_prefix_set(std::set<unsigned> &update, unsigned q)
	{
		auto it1 = update.begin();
		while (it1 != update.end())
		{
			auto old_it1 = it1++;
			std::cout << "Current state in check: " << *old_it1 << " " << q << std::endl;
			// q is simulated by exiting state
			if (simulator_.simulate(*old_it1, q))
			{
				return;
			}
			else if (simulator_.simulate(q, *old_it1))
			{
				std::cout << "Remove " << *old_it1 << std::endl;
				it1 = update.erase(old_it1);
			}
			std::cout << " out? " << (it1 == update.end()) << std::endl;
		}
		// q is not simulated by any states in update
		update.insert(q);
	}

	bool congr::is_simulated(const state_set &left, const state_set &right)
	{
		for (unsigned p : left)
		{
			bool simulated = false;
			for (unsigned q : right)
			{
				if (simulator_.simulate(q, p))
				{
					simulated = true;
					break;
				}
			}
			if (!simulated)
			{
				return false;
			}
		}
		return true;
	}

	bool congr::can_add_to_prefix_set(std::set<prefix_graph> &orig, state_set &update)
	{
		for (const prefix_graph &g : orig)
		{
			// some set in orig can be simulated by update
			if (is_simulated(g.repr_, update))
			{
				return false;
			}
		}
		return true;
	}

	// PRECONDITION: we know that update can not simulate any set in orig
	void congr::add_to_prefix_antichain(std::set<prefix_graph> &orig, prefix_graph &update, std::set<prefix_graph> &to_removed)
	{
		//HashSet<ISet> result = new HashSet<>();
		//if(debug) System.out.println("Current set = " + orig + " update = " + update);
		// a set corresponds to a class of finite prefixes to an accepting state in A
		// check whether there is set that can simulate update
		auto it1 = orig.begin();
		while (it1 != orig.end())
		{
			auto old_it1 = it1++;
			// q is simulated by exiting state
			prefix_graph tmp = *old_it1;
			if (is_simulated(update.repr_, tmp.repr_))
			{
				to_removed.insert(*old_it1);
				it1 = orig.erase(old_it1);
			}
		}
		orig.insert(update);
	}

	void congr::compute_prefix_simulation()
	{
		std::cout << "Entering prefix simulation..." << std::endl;
		// initialization
		unsigned init_A = A_->get_init_state_number();
		prefix_graph init_val;
		init_val.repr_.insert(B_->get_init_state_number());
		prefix_map_[init_A].insert(init_val);

		std::cout << "Add todo\n";
		std::deque<unsigned> todo;
		todo.emplace_back(init_A);
		state_set visited;
		visited.insert(init_A);
		std::cout << "Start loop\n";
		while (!todo.empty())
		{
			unsigned s = todo.front();
			todo.pop_front();
			visited.erase(s);

			std::cout << "Current A-state " << s << std::endl;
			std::set<state_set> removed;
			for (auto &tr_A : A_->out(s))
			{
				// s - a - > t in A_
				// f(s) - a -> P'
				// p \in f(s), then P' \subseteq f(t) in B
				// compute mapping relations to B
				// a set corresponds to a word u
				unsigned t = tr_A.dst;
				bdd letters = tr_A.cond;
				std::cout << "Next A-state " << t << std::endl;

				// copy this set
				std::set<prefix_graph> copy = prefix_map_[s];
				for (const prefix_graph &gr : copy)
				{
					// for every graph, we update the graphs

					bdd supp = support_A_[s];
					for (unsigned p : gr.repr_)
					{
						supp &= support_B_[p];
					}
					bdd all = letters;

					while (all != bddfalse)
					{
						bdd letter = bdd_satoneset(all, supp, bddfalse);
						all -= letter;
						std::cout << "Letter " << letter << std::endl;

						prefix_graph update;
						update.word_ = gr.word_;
						update.word_.emplace_back(letter);
						std::cout << "Initialize graph: " << update << std::endl;
						for (unsigned p : gr.repr_)
						{
							for (auto &tr_B : B_->out(p))
							{
								if (!bdd_implies(letter, tr_B.cond))
									continue;
								std::cout << "add B-state " << tr_B.dst << std::endl;
								std::cout << "preSet : " << get_set_string(update.repr_) << std::endl;
								// update the states for t
								add_to_minimized_prefix_set(update.repr_, tr_B.dst);
								std::cout << "Set : " << get_set_string(update.repr_) << std::endl;
							}
							std::cout << "Hello end " << p << std::endl;
						}
						std::cout << "The graph for " << t << ": " << update << std::endl;
						// for this letter, we update the representative
						std::set<prefix_graph> orig = prefix_map_[t];
						// update is the word ua and check whether we need to update
						if (can_add_to_prefix_set(orig, update.repr_))
						{
							// POSTCONDITION: update can not simulate any set in orig
							std::set<prefix_graph> to_removed;
							// if (debug)
							// 	System.out.println("Next state is " + t);
							add_to_prefix_antichain(orig, update, to_removed);
							prefix_map_[t] = orig;
							std::cout << "Add " << update << " to representative of " << t << std::endl;
							if (visited.find(t) == visited.end())
							{
								todo.emplace_back(t);
								visited.insert(t);
							}
						}
						// detected that update is empty for the first time
						// now need to update
						if (update.repr_.empty())
						{
							// must already
							std::vector<bdd> tmp;
							print_counterexample(update.word_, tmp);
							exit(0);
						}
					}
				}
			}
		}
	}

	// keep the maximal elements over simulation
	void congr::add_to_minimized_period_set(std::set<arc> &set, arc &triple)
	{
		auto it1 = set.begin();
		while (it1 != set.end())
		{
			auto old_it1 = it1++;
			// q is simulated by exiting state
			arc tpl = *old_it1;
			if (tpl.src_ == triple.src_ && (tpl.acc_ < 1 || triple.acc_ == 1) && simulator_.simulate(triple.dst_, tpl.dst_))
			{
				// some triple in set can be simulated by triple
				it1 = set.erase(old_it1);
			}
			else if (tpl.src_ == triple.src_ && (tpl.acc_ == 1 || triple.acc_ < 1) && simulator_.simulate(tpl.dst_, triple.dst_))
			{
				// triple can be simulated by some triple in it
				return;
			}
		}
		set.insert(triple);
	}

	// the set left is either a subset or simulated by right
	bool congr::is_simulated(const period_graph &left, const period_graph &right)
	{
		for (const arc &lft : left.repr_)
		{
			bool simulated = false;
			for (const arc &rgt : right.repr_)
			{
				if (lft.src_ == rgt.src_ && simulator_.simulate(rgt.dst_, lft.dst_) && (lft.acc_ < 1 || rgt.acc_ == 1))
				{
					simulated = true;
					break;
				}
			}
			if (!simulated)
			{
				return false;
			}
		}
		return true;
	}

	bool congr::can_add_to_period_set(std::set<period_graph> &orig, period_graph &update)
	{
		for (const period_graph &g : orig)
		{
			// if g in sets can be simulated by update, no need to add update
			if (is_simulated(g, update))
			{
				return false;
			}
		}
		return true;
	}

	void congr::add_to_period_antichain(std::set<period_graph> &orig, period_graph &update, std::set<period_graph> &to_removed)
	{
		bool changed = false;
		auto it1 = orig.begin();
		while (it1 != orig.end())
		{
			auto old_it1 = it1++;
			// q is simulated by exiting state
			period_graph tmp = *old_it1;
			// update is smulated by tmp
			if (is_simulated(update, tmp))
			{
				to_removed.insert(*old_it1);
				it1 = orig.erase(old_it1);
			}
		}
		orig.insert(update);
	}

	// precondition: s is an accepting state
	void congr::compute_period_simulation(unsigned acc_state, const prefix_graph &simulated_graph)
	{
		std::cout << "Entering period simulation \n";
		period_map_.clear();

		std::deque<unsigned> todo;
		std::set<unsigned> visited;
		std::set<unsigned> simulated_set = simulated_graph.repr_;
		std::cout << "Computing the congruence representation of periods for accepting state " << acc_state << " ...\n";
		// 1. initialization
		{
			period_graph gr;
			for (unsigned p : simulated_set)
			{
				// reachable states
				arc tpl = arc(p, p, -1);
				gr.repr_.insert(tpl);
			}
			std::set<period_graph> val;
			val.insert(gr);
			period_map_.emplace(acc_state, val);
			todo.emplace_back(acc_state);
			visited.insert(acc_state);
		}
		// {
		
		// 	unsigned s = acc_state;
		// 	for (auto &tr_A : A_->out(s))
		// 	{
		// 		unsigned t = tr_A.dst;
		// 		// only care about the states in the same SCC
		// 		if (si_A_.scc_of(s) != si_A_.scc_of(t))
		// 		{
		// 			continue;
		// 		}
		// 		if (visited.find(t) == visited.end())
		// 		{
		// 			todo.emplace_back(t);
		// 			visited.insert(t);
		// 		}
		// 		bdd letters = tr_A.cond;
		// 		// copy this set

		// 		bdd supp = support_A_[s];
		// 		for (unsigned p : simulated_set)
		// 		{
		// 			supp &= support_B_[p];
		// 		}
		// 		bdd all = letters;

		// 		while (all != bddfalse)
		// 		{
		// 			bdd letter = bdd_satoneset(all, supp, bddfalse);
		// 			all -= letter;
		// 			period_graph update;
		// 			std::set<unsigned> reached_states;
		// 			// fixed (set, letter)
		// 			for (unsigned p : simulated_set)
		// 			{
		// 				for (auto &tr_B : B_->out(p))
		// 				{
		// 					if (!bdd_implies(letter, tr_B.cond))
		// 						continue;
		// 					std::cout << p << " to " << tr_B.dst << ": " << tr_B.acc << std::endl;
		// 					// only state pair in the same accepting SCC
		// 					if (si_B_.scc_of(p) == si_B_.scc_of(tr_B.dst) && si_B_.is_accepting_scc(si_B_.scc_of(p)))
		// 					{
		// 						// add arc p->tr_B.dst
		// 						arc tpl = arc(p, tr_B.dst, tr_B.acc.has(0));
		// 						std::cout << "period triple: " << tpl << std::endl;
		// 						add_to_minimized_period_set(update.repr_, tpl);
		// 					}
		// 					// reachable states will be kept simply as (q, false, q)
		// 					reached_states.insert(tr_B.dst);
		// 				}
		// 			}
		// 			// now there are states we need to add
		// 			for (unsigned q : reached_states)
		// 			{
		// 				arc tpl = arc(q, q, false);
		// 				add_to_minimized_period_set(update.repr_, tpl);
		// 			}
		// 			update.word_.emplace_back(letter);
		// 			// check update
		// 			std::set<period_graph> &graphs = period_map_[t];
		// 			if (can_add_to_period_set(graphs, update))
		// 			{
		// 				// POSTCONDITION: need to add this set, this set cannot simulate any set in curr
		// 				std::set<period_graph> to_removed;
		// 				// only keep the smallest ones?
		// 				add_to_period_antichain(graphs, update, to_removed);
		// 				period_map_[t] = graphs;
		// 				// if (t == acc_state)
		// 				// {
		// 				// 	//decide whether it ...
		// 				// 	for (auto &pref : prefix_map_[t])
		// 				// 	{
		// 				// 		if (std::includes(is_empty(pref.repr_, update))
		// 				// 		{
		// 				// 			std::cout << "Early-0 terminated for accepting state " << acc_state << std::endl;
		// 				// 			if (update.repr_.empty())
		// 				// 			{
		// 				// 				std::vector<bdd> left;
		// 				// 				left.insert(left.end(), pref.word_.begin(), pref.word_.end());
		// 				// 				left.emplace_back(letter);
		// 				// 				std::vector<bdd> tmp;
		// 				// 				print_counterexample(left, tmp);
		// 				// 			}
		// 				// 			else
		// 				// 			{
		// 				// 				print_counterexample(pref.word_, update.word_);
		// 				// 			}
		// 				// 			std::cout << "Prefix: " << pref << std::endl;
		// 				// 			std::cout << "Period: " << update << std::endl;
		// 				// 			exit(0);
		// 				// 		}
		// 				// 		std::cout << "Out of emptiness checking" << std::endl;
		// 				// 	}
		// 				// }
		// 			}
		// 			// no states there
		// 			if (update.repr_.empty())
		// 			{
		// 				std::vector<bdd> left;
		// 				left.insert(left.end(), simulated_graph.word_.begin(), simulated_graph.word_.end());
		// 				left.emplace_back(letter);
		// 				print_counterexample(left, std::vector<bdd>());
		// 				exit(0);
		// 			}
		// 		}
		// 	}
		// }

		// 2. computation of simulated relations
		while (!todo.empty())
		{
			int s = todo.front();
			todo.pop_front();
			visited.erase(s);

			for (auto &tr_A : A_->out(s))
			{
				unsigned t = tr_A.dst;
				// only care about the states in the same SCC
				if (si_A_.scc_of(s) != si_A_.scc_of(t))
				{
					continue;
				}

				bdd letters = tr_A.cond;
				// copy this set
				std::set<period_graph> copy = period_map_[s];
				for (const period_graph &gr : copy)
				{
					bdd supp = support_A_[s];
					for (const arc &tpl : gr.repr_)
					{
						supp &= support_B_[tpl.dst_];
					}
					bdd all = letters;

					while (all != bddfalse)
					{
						bdd letter = bdd_satoneset(all, supp, bddfalse);
						all -= letter;
						period_graph update;
						update.word_ = gr.word_;
						std::set<unsigned> reached_states;
						// fixed (set, letter)
						for (const arc &curr_tpl : gr.repr_)
						{
							unsigned p = curr_tpl.src_;
							for (auto &tr_B : B_->out(curr_tpl.dst_))
							{
								if (!bdd_implies(letter, tr_B.cond))
									continue;
								// (p -> dst_ -> tr_B.dst)
								// only state pair in the same accepting SCC
								if (si_B_.scc_of(p) == si_B_.scc_of(tr_B.dst) && si_B_.is_accepting_scc(si_B_.scc_of(p)))
								{
									// add arc
									int acc = (tr_B.acc.has(0) || curr_tpl.acc_ == 1) ? 1 : 0;
									// std::cout << p << " to " << tr_B.dst << ": " << acc << std::endl;
									arc tpl = arc(p, tr_B.dst, acc);
									add_to_minimized_period_set(update.repr_, tpl);
								}
								// reachable states will be kept simply as (q, false, q)
								reached_states.insert(tr_B.dst);
							}
						}
						// now there are states we need to add
						for (unsigned q : reached_states)
						{
							arc tpl = arc(q, q, -1);
							add_to_minimized_period_set(update.repr_, tpl);
						}
						update.word_.emplace_back(letter);
						// check update
						std::set<period_graph> &graphs = period_map_[t];
						if (can_add_to_period_set(graphs, update))
						{
							// POSTCONDITION: need to add this set, this set cannot simulate any set in curr
							std::set<period_graph> to_removed;
							// only keep the smallest ones?
							add_to_period_antichain(graphs, update, to_removed);
							period_map_[t] = graphs;

							if (t == acc_state)
							{
								// decide whether it ...
								for (const prefix_graph &pref : prefix_map_[acc_state])
								{
									if (is_valid_period(update) && is_empty(pref.repr_, update))
									{
										std::cout << "Early-1 terminated for accepting state " << acc_state << std::endl;
										if (update.repr_.empty())
										{
											std::vector<bdd> left;
											left.insert(left.end(), pref.word_.begin(), pref.word_.end());
											left.insert(left.end(), update.word_.begin(), update.word_.end());
											print_counterexample(pref.word_, std::vector<bdd>());
										}
										else
										{
											print_counterexample(pref.word_, update.word_);
										}
										exit(0);
									}
									std::cout << "Out of is_empty\n";
								}
							}

							// the graphs must have been changed
							if (visited.find(t) == visited.end())
							{
								todo.emplace_back(t);
								visited.insert(t);
							}
						}
						// no states there
						if (update.repr_.empty())
						{
							std::vector<bdd> word;
							word.insert(word.end(), simulated_graph.word_.begin(), simulated_graph.word_.end());
							word.insert(word.end(), update.word_.begin(), update.word_.end());
							std::vector<bdd> cycle;
							print_counterexample(word, cycle);
							exit(0);
						}
					}
				}
			}
		}
	}

	void congr::print_counterexample(const std::vector<bdd> &prefix, const std::vector<bdd> &period)
	{
		std::cout << "Not contained: ";
		if (!prefix.empty())
			for (const bdd &c : prefix)
			{
				bdd_print_formula(std::cout, A_->get_dict(), c);
				std::cout << "; ";
			}
		if (period.empty())
			return;
		bool notfirst = false;
		std::cout << "cycle{";
		for (auto &i : period)
		{
			if (notfirst)
				std::cout << "; ";
			notfirst = true;
			bdd_print_formula(std::cout, A_->get_dict(), i);
		}
		std::cout << '}' << std::endl;
	}

	// state_set congr::get_reachable_states(const state_set &prefix, const period_graph &period)
	// {
	// 	state_set reachable_states = prefix;
	// 	for (unsigned i = 0; i < period.word_.size(); i++)
	// 	{
	// 		bdd letter = period.word_[i];
	// 		state_set next;
	// 		for (unsigned s : reachable_states)
	// 		{
	// 			for (auto &tr : B_->out(s))
	// 			{
	// 				if (!bdd_implies(letter, tr.cond))
	// 					continue;
	// 				next.insert(tr.dst);
	// 			}
	// 		}
	// 		reachable_states.insert(next.begin(), next.end());
	// 	}
	// 	return reachable_states;
	// }

	// we test the emptiness
	bool congr::is_empty(const state_set &prefix, const period_graph &period)
	{
		// compute the reachable states from prefix
		std::cout << "Entering is_empty\n";
		state_set reachable_states = prefix;
		for (unsigned i = 0; i < period.word_.size(); i++)
		{
			bdd letter = period.word_[i];
			state_set next;
			for (unsigned s : reachable_states)
			{
				for (auto &tr : B_->out(s))
				{
					if (!bdd_implies(letter, tr.cond))
						continue;
					next.insert(tr.dst);
				}
			}
			reachable_states.insert(next.begin(), next.end());
		}
		std::cout << "Reached states: " << get_set_string(reachable_states) << " from " << get_set_string(prefix) << std::endl;
		spot::bdd_dict_ptr alphabet = spot::make_bdd_dict();
		spot::twa_graph_ptr nba = spot::make_twa_graph(alphabet);
		bdd p1 = bdd_ithvar(nba->register_ap("p"));
		nba->set_buchi();

		unsigned num = 0;
		std::map<arc, unsigned> from_map;
		std::set<unsigned> inits;
		for (const arc &tpl : period.repr_)
		{
			from_map[tpl] = num;
			if (reachable_states.find(tpl.src_) != reachable_states.end())
			{
				inits.insert(num);
			}
			nba->new_state();
			num++;
		}
		std::cout << "Inits: " << get_set_string(inits) << std::endl;
		for (auto& p : from_map)
		{
			std::cout << p.first << " mapped to " << p.second << std::endl;
		}
		std::cout << "Num " << num << " map size: " << from_map.size() << std::endl;
		// the initial state
		unsigned init_state = -1U;
		if (inits.size() > 1)
		{
			// add one more state as initial state
			nba->new_state();
			init_state = nba->num_states() - 1;
			for (unsigned s : inits)
			{
				nba->new_acc_edge(init_state, s, p1, false);
			}
		}
		else
		{
			for (unsigned s : inits)
			{
				init_state = s;
				break;
			}
		}
		nba->set_init_state(init_state);

		// now add transition
		for (const arc &from : period.repr_)
		{
			unsigned s = from_map[from];
			for (const arc &to : period.repr_)
			{
				unsigned t = from_map[to];
				// can be simulated
				// backward simulation for these two states
				if (from.dst_ == to.src_)
				{
					std::cout << "Edge: " << s << " to " << t << " : " << from.acc_ << std::endl;
					std::cout << "Map: " << from << " to " << to << std::endl;
					nba->new_acc_edge(s, t, p1, from.acc_== 1);
				}
			}
		}
		
		return nba->is_empty();
	}

	bool congr::is_valid_period(const period_graph &period)
	{
		// std::map<unsigned, state_set> src_map;
		// std::map<unsigned, state_set> dst_map;
		for (auto& tp : period.repr_)
		{
			if (tp.acc_ != -1)
				return true;
		}
		return false;
	}

	void congr::contains()
	{
		std::cout << "Entering contains..." << std::endl;
		unsigned count = 1;
		state_set acc_states;
		for (unsigned state = 0; state < A_->num_states(); state++)
		{
			if (!is_accepting_A_[state])
				continue;
			acc_states.insert(state);
		}
		std::cout << "Start computing prefix simulation..." << std::endl;
		compute_prefix_simulation();

		for (unsigned acc_state : acc_states)
		{
			std::cout << "Checking for " << count << "-th accepting state " << acc_state << " out of " << acc_states.size() << std::endl;
			count++;
			// obtain the necessary part for accState
			// we assume that prefSims is already computed under subsumption relation
			std::set<prefix_graph> &prefixes = prefix_map_[acc_state];
			if (prefixes.empty())
			{
				continue;
			}

			prefix_graph all_prefixes;
			for (const prefix_graph &p : prefixes)
			{
				// if there is one
				all_prefixes.repr_.insert(p.repr_.begin(), p.repr_.end());
				// any word would do
				all_prefixes.word_ = p.word_;
			}
			std::cout << "Reprs: " << get_set_string(all_prefixes.repr_) << std::endl;
			std::cout << "Deciding the language inclusion between L(A^i_f) (A^f_f)^w and L(B) ...\n";
			compute_period_simulation(acc_state, all_prefixes);
			// now decide whether there is one word accepted by A but not B
			for(auto& period : period_map_[acc_state])
			{
				std::cout << "Period: " << period << std::endl;
			}
			for (auto & prefix : prefix_map_[acc_state])
			{
				unsigned num = 1;
				for (auto& period : period_map_[acc_state])
				{
					if (is_valid_period(period) && is_empty(prefix.repr_, period))
					{
						std::cout << "Prefix: " << prefix << std::endl;
						std::cout << "Period: " << period << std::endl;
						print_counterexample(prefix.word_, period.word_);
						exit(0);
					}
					std::cout << "Out of is_empty: " << num << " out of "<< period_map_[acc_state].size() << std::endl;
					num ++;
				}
				std::cout << "Next pref\n";
			}
			std::cout << "End of acc_state = " << acc_state << std::endl;
		}

		//std::cout << "Contained"<< std::endl;
	}

	void
	congr_contain(spot::twa_graph_ptr B, spot::twa_graph_ptr A, spot::option_map &om)
	{
		std::cerr << "Congruence-based approach is still under development and may give wrong answers\n";
		// first, make A_ state-based, so we can work independently with each accepting state
		spot::postprocessor p;
		p.set_pref(spot::postprocessor::SBAcc);
		p.set_level(spot::postprocessor::Low);
		A = p.run(A);
		spot::scc_info si_A = spot::scc_info(A, spot::scc_info_options::ALL);

		const int trans_pruning = om.get(NUM_TRANS_PRUNING);
		// now we compute the simulator of B
		std::vector<bdd> implications;
		spot::twa_graph_ptr aut_tmp = nullptr;
		if (om.get(USE_SIMULATION) > 0)
		{
			aut_tmp = spot::scc_filter(B);
			auto aut2 = spot::simulation(aut_tmp, &implications, trans_pruning);
			aut_tmp = aut2;
		}
		if (aut_tmp)
			B = aut_tmp;

		spot::scc_info si_B = spot::scc_info(B, spot::scc_info_options::ALL);

		std::cout << "Entering congruence...\n";
		congr checker(om, B, si_B, A, si_A, implications);
		checker.contains();
	}

}