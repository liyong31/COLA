import spot
from spot import buddy


import multiprocessing
import os
import subprocess
import getopt, sys
import queue # import PriorityQueue
import time
# import heapq

arg_list = [] ## the 

output_bas = "outputs/"
input_bas = "inputs/"
input_name = "nba"
output_name = "dpa"
suffix = ".hoa"
cola_exe = "./cola" # please use exact path
verbose = 0

scc_types = []
scc_sizes = []
scc_num_preds = []
scc_time = []

setattr(spot.twa_graph, "__lt__", lambda self, other: self.num_states() <= other.num_states())

# check whether an SCC is inner deterministic
def is_deterministic_scc(si, scc):
    for s in list(si.states_of(scc)):
        left = buddy.bddtrue
        for t in si.get_aut().out(s):
            if si.scc_of(t.dst) != scc:
                continue
            if not buddy.bdd_implies(t.cond, left):
                return False
            else:
                left -= t.cond
    return True

# make an NBA with empty language
def make_empty_nba(bdict):
    aut = spot.make_twa_graph(bdict)
    aut.set_acceptance(1, "Inf(0)");
    aut.new_states(1)
    aut.set_init_state(0)
    aut.new_edge(0, 0, buddy.bddtrue)
    return aut

def get_all_files(path, file = ""):
    tmpList = os.listdir(path)
    
    for tmp in tmpList:
        arg_list.append(path + tmp)

def run_command(arg, file_name):
    command = [cola_exe, '--determinize=ba', arg, '-o', output_bas + file_name, '--acd', '--parity', '--simulation', '--stutter', '--use-scc']
    subprocess.call(command)
    return file_name

# given the list of automaton names
def run_command_all(aut_names):
    for aut_name in aut_names:
        filepath, filename = os.path.split(aut_name)
        t_start = time.time()
        run_command(aut_name, filename)
        t_end = time.time()
        scc_time.append(t_end - t_start)

# write decomposed automaton to files
def write_aut_to_file(small_auts, file_name):
    global verbose
    # get file name
    filepath, aut_name = os.path.split(file_name)

    num_count = 0
    aut_names = []
    for sub_aut in small_auts:
        sub_aut_name = input_bas + aut_name + str(num_count) + suffix
        aut_names.append(sub_aut_name)
        if verbose > 0:
            print (sub_aut_name + " num= " + str(sub_aut.num_states()))
        text_file = open(sub_aut_name, "w")
        n = text_file.write(sub_aut.to_str('hoa'))
        text_file.close()
        num_count += 1   
    return aut_names
    
def decompose_nba(file_name):
    global verbose
    aut = spot.automaton(file_name)
    # now prepare to decompose this NBA
    if verbose > 0:
        print("Number of states in the input: " + str(aut.num_states()))
    si = spot.scc_info(aut)
    
    # now decompose for DACs and NACs
    small_auts = []
    weak_count = "" # accepting weak SCC counts
    
    num_weak_states = 0
    for scc in range(si.scc_count()):
        num_scc_states = len(list(si.states_of(scc)))
        if not spot.is_inherently_weak_scc(si, scc) and si.is_accepting_scc(scc):
            # only keep those SCCs as accepting
            other_aut =  spot.decompose_scc(si, str(scc))
            small_auts.append(other_aut)
            num_preds = other_aut.num_states() - num_scc_states
            if is_deterministic_scc(si, scc):
                scc_types.append("DAC")
            else:
                scc_types.append("NAC")
            scc_sizes.append(num_scc_states)
            scc_num_preds.append(num_preds)
        elif spot.is_inherently_weak_scc(si, scc) and si.is_accepting_scc(scc):
            if len(weak_count) == 0:
                weak_count = str(scc)
            else:
                weak_count += "," + str(scc)
            num_weak_states += num_scc_states
        
    if len(weak_count) > 0:
        weak_aut = spot.decompose_scc(si, weak_count)
        small_auts.append(weak_aut)
        scc_types.append("IWC")
        scc_sizes.append(num_weak_states)
        scc_num_preds.append(weak_aut.num_states() - num_weak_states)
        
    if verbose > 1:
        for other_aut in small_auts:
            print(other_aut.to_str('hoa'))
        print ("#smallnbas = " + str(len(small_auts)))
    
    # in case the language is empty
    if len(small_auts) == 0:
        small_auts.append(make_empty_nba(aut.get_dict()))
        scc_types.append("IWC")
        scc_sizes.append(1)
        scc_num_preds.append(0)
    
    return small_auts
    # now do postprocessing on each of them
#    res_auts = []
#    for sub_aut in small_auts:
#        sub_aut = sub_aut.postprocess('low', 'buchi')
#        res_auts.append(sub_aut)

def main():
    opts, args = getopt.getopt(sys.argv[1:], 'f:v:', )
    #print(opts)
    #print(args)
    global verbose
    if not os.path.isdir(input_bas):
        os.mkdir(input_bas)
    if not os.path.isdir(output_bas):
        os.mkdir(output_bas)
    
    file_name = None
    for prefix, arg in opts:
        if prefix == '-f':
            file_name = arg
        if prefix == '-v':
            verbose = int(arg)
            

    if file_name is None:
        print("File may not exist")
        exit(1)
    
    if verbose > 0: print(file_name)
    if not os.path.exists(file_name):
        print(file_name + " not exists")
        exit(1)
    
    arg_list.append(file_name)
    #print(arg_list)
    small_auts = decompose_nba(file_name)
    aut_names = write_aut_to_file(small_auts, file_name)
    run_command_all(aut_names)
    # output
    for i in range(len(aut_names)):
        print("type:" + scc_types[i] + ", size:" + str(scc_sizes[i]) + ", pred:" + str(scc_num_preds[i]) + ", time:" + str(scc_time[i]))
    
    
if __name__ == "__main__":
    main()
