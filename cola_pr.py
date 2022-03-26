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
    
def compose_dpas2(p_queue):
    while p_queue.qsize() > 1:
        fst_num_states, fst_aut = p_queue.get() #heapq.heappop(hq)#
        if verbose > 0: print ("get num = " + str(fst_num_states))
        snd_num_states, snd_aut = p_queue.get() # heapq.heappop(hq)#
        if verbose > 0: print ("get num = " + str(snd_num_states))
        res_aut = spot.product_or(fst_aut, snd_aut)
        if verbose > 0: print ("get res = " + str(res_aut.num_states()))
        spot.simplify_acceptance_here(res_aut)
        res_aut = res_aut.postprocess('generic', 'deterministic', 'low')
        p_queue.put((res_aut.num_states(), res_aut))

# given the list of automaton names
def run_command_all(aut_names):
    pool = multiprocessing.Pool(processes = len(aut_names))
    pool_results = []
    for aut_name in aut_names:
        filepath, filename = os.path.split(aut_name)
        pool_results.append(pool.apply_async(run_command, args=(aut_name, filename)))
    pool.close()
    res_aut = None
    p_queue = queue.PriorityQueue()
    
    while len(pool_results) > 0:
        to_remove = [] #avoid removing objects during for_loop
        for r in pool_results:
            # check if process is finished
            if r.ready(): 
                # print result (or do any operation with result)
                filename = r.get()
                # print(filename)
                to_remove.append(r)
                aut = spot.automaton(output_bas + filename)
                aut = aut.postprocess('parity', 'deterministic', 'low')
                #print ('current aut: ' + str(aut.num_states()))
                p_queue.put((aut.num_states(), aut))
        # compose
        compose_dpas2(p_queue)
        for remove in to_remove:
            pool_results.remove(remove)
    
        #time.sleep(1) # ensures that this thread doesn't consume too much memory
    # waiting for all sub-processes finishing
    pool.join()
    num_states, res_aut = p_queue.get() #heapq.heappop(hq)#
    return res_aut

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
    for scc in range(si.scc_count()):
        if not spot.is_inherently_weak_scc(si, scc) and si.is_accepting_scc(scc):
            # only keep those SCCs as accepting
            other_aut =  spot.decompose_scc(si, str(scc))
            small_auts.append(other_aut)
        elif spot.is_inherently_weak_scc(si, scc) and si.is_accepting_scc(scc):
            if len(weak_count) == 0:
                weak_count = str(scc)
            else:
                weak_count += "," + str(scc)
    if len(weak_count) > 0:
        weak_aut = spot.decompose_scc(si, weak_count)
        small_auts.append(weak_aut)
        
    if verbose > 1:
        for other_aut in small_auts:
            print(other_aut.to_str('hoa'))
        print ("#smallnbas = " + str(len(small_auts)))
    
    # in case the language is empty
    if len(small_auts) == 0:
        small_auts.append(make_empty_nba(aut.get_dict()))
        
    # now do postprocessing on each of them
    res_auts = []
    for sub_aut in small_auts:
        sub_aut = sub_aut.postprocess('low', 'buchi')
        res_auts.append(sub_aut)
    
    return res_auts
    

def compose_dpas(aut_names):
    global verbose
    p_queue = queue.PriorityQueue()
    setattr(spot.twa_graph, "__lt__", lambda self, other: self.num_states() <= other.num_states())
    
    for aut_name in aut_names:
        filepath, filename = os.path.split(aut_name)
        # print (output_bas + filename)
        aut = spot.automaton(output_bas + filename)
        aut = aut.postprocess('parity', 'deterministic', 'low')
        #print ('current aut: ' + str(aut.num_states()))
        p_queue.put((aut.num_states(), aut))

    while p_queue.qsize() > 1:
        fst_num_states, fst_aut = p_queue.get() #heapq.heappop(hq)#
        if verbose > 0: print ("get num = " + str(fst_num_states))
        snd_num_states, snd_aut = p_queue.get() # heapq.heappop(hq)#
        if verbose > 0: print ("get num = " + str(snd_num_states))
        res_aut = spot.product_or(fst_aut, snd_aut)
        if verbose > 0: print ("get res = " + str(res_aut.num_states()))
        spot.simplify_acceptance_here(res_aut)
        res_aut = res_aut.postprocess('generic', 'deterministic', 'low')
        p_queue.put((res_aut.num_states(), res_aut))

    num_states, res_aut = p_queue.get() #heapq.heappop(hq)#
    return res_aut
    # only one left

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
    res_aut = run_command_all(aut_names)
    # res_aut = compose_dpas(aut_names)
    print(res_aut.to_str('hoa'))
    
if __name__ == "__main__":
    main()
