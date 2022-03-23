// Copyright (C) 2022-present  The COLA Authors
//
// This file is a part of COLA, a tool for complementation and determinization
// of omega automata.
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

#include "cola.hpp"

#include <map>
#include <fstream>
#include <ctime>
#include <string>
#include <vector>
#include <sstream>

#include <spot/twaalgos/hoa.hh>


using namespace std;

void print_help()
{
  print_usage(std::cout);
  std::cout <<
      R"(The tool checks whether L(A) <= L(B) based on determinization in COLA.

Input options:
    --A FILENAME reads the input A from FILENAME
    --B FILENAME reads the input B from FILENAME
    
Miscellaneous options:
  -h, --help    Print this help
  --version     Print program version
)";
}

unsigned get_num_bits(unsigned num) 
{
    unsigned count = 0;
	while(num)
	{
		count ++;
		n = n >> 1;
	}
	return count;
}

string encode(unsigned value, unsigned numBits) 
{
    string res = "";
    int bit = 1;
    for (unsigned index = 0; index < numBits; index ++) 
    {
        if ((bit & value) == 0) 
        {
            res += "!";
        }
        res += "" + to_string(index);
        if (index != numBits - 1) 
        {
            res += "&";
        }
        bit <<= 1;
    }
    return res;
}

class alphabet
{
    map<string, unsigned> ap2index_;
    vector<string> apvec_;

    alphabet()
    {

    }

    unsigned add_ap(string ap)
    {
        auto i = ap2index_.emplace(ap, 0);
        if (i.second) // insertion successfully
        {
            unsigned index = apvec_.size();
            apvec_.emplace_back(ap);
            i.first->second = index;
            return index;
        }else 
        {
            return i.first->second;
        }
    }

    static 
}

class ba_graph
{
    
    



}



int main(int argc, char *argv[])
{

  spot::option_map om;
  // default setting
  om.set(USE_SIMULATION, 0);
  om.set(USE_STUTTER, 0);
  om.set(USE_UNAMBIGUITY, 0);
  om.set(USE_SCC_INFO, 0);
  om.set(VERBOSE_LEVEL, 0);
  om.set(USE_DELAYED_SIMULATION, 0);
  om.set(MORE_ACC_EDGES, 0);
  om.set(NUM_TRANS_PRUNING, 512);
  om.set(MSTATE_REARRANGE, 0);
  om.set(OUTPUT_AUT_TYPE, Parity);

  om.set(SCC_REACH_MEMORY_LIMIT, 0);
  om.set(NUM_SCC_LIMIT_MERGER, 0);
  om.set(MAX_NUM_SIMULATION, 4096);

}