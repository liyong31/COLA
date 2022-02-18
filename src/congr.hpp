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

#include "optimizer.hpp"

#include <iostream>

#include <spot/twaalgos/word.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/hoa.hh>

using namespace std;
// Apply congruence relations for Buchi automata to inclusion checking

namespace cola
{
    // Arc: indicates whether src_ visits dst_ via accepting transitions (acc_) 
    class arc
    {
        public:

        unsigned src_;
        unsigned dst_;
        bool     acc_;

        arc(unsigned src, unsigned dst, bool acc)
        : src_ (src), dst_ (dst), acc_ (acc)
        {}

        bool operator<(const arc &other) const;
        bool operator==(const arc &other) const;
        arc & operator=(const arc &other);

        size_t hash() const;
        friend ostream& operator<<(ostream& os, const arc& c);
    };

    struct arc_hash
    {
        size_t
        operator()(const arc &s) const noexcept
        {
        return s.hash();
        }
    };

    typedef std::set<arc> arc_set;

    class prefix_graph
    {
        public:

        std::set<unsigned> repr_;
        std::vector<bdd> word_;

        prefix_graph() {}

        bool operator<(const prefix_graph &other) const;
        bool operator==(const prefix_graph &other) const;
        prefix_graph & operator=(const prefix_graph &other);

        size_t hash() const;
        friend ostream& operator<<(ostream& os, const prefix_graph& g);
    };

    class period_graph
    {
        public:

        std::set<arc> repr_;
        std::vector<bdd> word_;

        period_graph() {}

        bool operator<(const period_graph &other) const;
        bool operator==(const period_graph &other) const;
        period_graph & operator=(const period_graph &other);

        size_t hash() const;
        friend ostream& operator<<(ostream& os, const period_graph& g);
    };

    typedef std::pair<unsigned, std::set<unsigned>> prefix_word_key;
    typedef std::pair<unsigned, std::set<arc>> period_word_key;

    
    struct word_key_hash
    {
        template <class T1, class T2>
        size_t
        operator()(const std::pair<T1, std::set<T2>> &s) const noexcept
        {
            size_t res = 0;
            res = (res << 3)^ std::hash<T1>{}(s.first);
            for (T2& e : s.second)
            {
                res = (res << 3)^std::hash<T2>{}(e);
            }
            return res;
        }
    };

    // Congruence relations for checking language containment between A_ and B_ 
    class congr
    {
        public:

        const spot::option_map& om_;
        spot::scc_info si_B_; 
        spot::scc_info si_A_; 


        spot::twa_graph_ptr A_;
        std::vector<bool> is_accepting_A_;
        std::vector<bdd> support_A_;
        std::vector<bdd> compact_A_;

        spot::twa_graph_ptr B_;
        std::vector<bdd> support_B_;
        std::string scc_types_B_;

        std::map<unsigned, std::set<prefix_graph>> prefix_map;
        std::map<unsigned, std::set<period_graph>> period_map; 

        // word map
        //std::unordered_map<std::pair<unsigned, state_set>, spot::twa_word_ptr, word_key_hash> prefix_word_map;
	    //std::unordered_map<std::pair<unsigned, arc_set>, spot::twa_word_ptr, word_key_hash> period_word_map;

        state_simulator simulator_;

        congr(spot::option_map& om, spot::twa_graph_ptr B, spot::scc_info& si_B, spot::twa_graph_ptr A, spot::scc_info& si_A, std::vector<bdd>& implications);

        void add_to_minimized_prefix_set(std::set<unsigned>& update, unsigned q);

        bool can_add_to_prefix_set(std::set<prefix_graph>& orig, state_set& update);

        bool is_simulated(const state_set& left, const state_set& right);

        void add_to_prefix_antichain(std::set<prefix_graph>& orig, prefix_graph& update, std::set<prefix_graph>& to_removed);

        void compute_prefix_simulation();

        void add_to_minimized_period_set(std::set<arc>& set, arc& triple);

        bool is_simulated(const period_graph& left, const period_graph& right);

        void add_to_period_antichain(std::set<period_graph>& orig, period_graph& update, std::set<period_graph>& to_removed);

        bool can_add_to_period_set(std::set<period_graph>& orig, period_graph& update);

        void compute_period_simulation(unsigned s, const prefix_graph&  set);

        bool is_empty(const state_set& prefix, const period_graph& period);

        void contains();

        void print_counterexample(const std::vector<bdd>& prefix, const std::vector<bdd>& period);

    };

}