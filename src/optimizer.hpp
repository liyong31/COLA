#pragma once

#include <set>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/isunamb.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/sccfilter.hh>

class optimizer
{

    private:
        spot::twa_graph_ptr aut_;
        // Simplifications options
        std::vector<std::vector<char>> implies_;
        std::vector<bdd> support_;
    
        // res[i + scccount*j] = 1 iff SCC i is reachable from SCC j
        std::vector<char>
        find_scc_paths(const spot::scc_info& scc);

    public:
        optimizer(spot::twa_graph_ptr aut, bool use_simulation, bool use_stutter);

    void output_simulation()
    {
        for(int i = 0; i < implies_.size() ; i ++)
        {
            for(int j = 0; j < implies_[i].size(); j ++)
            {
                if( i == j) continue;
                // j contains the language of i
                std::cout << j << " simulates " << i << " : " << (unsigned)(implies_[i][j]) << " " << simulate(j, i) << std::endl;

            }
        }              
    }

    // check whether state i simulates state j
    bool simulate(unsigned i, unsigned j)
    {
        if(i == j) return true;
        if(j < implies_.size() && i < implies_[j].size())
        {
            return implies_[j][i] > 0;
        }else 
        {
            return false;
        }
    }



};