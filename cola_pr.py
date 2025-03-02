import spot
from spot import buddy


import multiprocessing
import os
import subprocess
import getopt, sys
import queue # import PriorityQueue
import time
import argparse
import shutil

# import heapq


ARG_MGR_STR = "--use-scc"
ARG_SIM_STR = "--simulation"
# ARG_ACD_STR = "--acd"
ARG_STU_STR = "--stutter"
ARG_VERB_LEVEL = 0
ARG_IWC_PAR = 0

mgr_str = ""
sim_str = ""
# acd_str = ""
stu_str = ""
verbose = 0
parity = False
compl = False
pariwc = False 
num_workers = 0


arg_list = [] ## the 
output_bas = "cola-outputs/"
input_bas = "cola-inputs/"
suffix = ".hoa"
cola_exe = "./cola" # please use exact path
input_file = ""



header="""
---------------------------------------------------------------
COLA -- A determinization library for Büchi automata
---------------------------------------------------------------
  
  Reads a nondeterministic Büchi automaton and transforms it to 
  deterministic Emerson-Lei automaton
  
  Copyright (c) 2022 - Present  COLA authors
  
  Please report bugs via email (liyong@ios.ac.cn) or on 
  github (https://github.com/liyong31/COLA)	
---------------------------------------------------------------
"""

short_header="""COLA -- A determinization library for nondeterministic Büchi automata
Copyright (c) 2022 - Present  COLA authors"""

def getopts(header):
    num_cores = multiprocessing.cpu_count()
    p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('file', help='file name for the input automaton in HOA format', type=str)
#    p.add_argument('--acd',             help='Use Alternating Cycle Decompostion for obtaining Parity automata', action="count", default=0)
    p.add_argument('--comp',            help='Output complement automaton after determinization', action="count", default=0)
    p.add_argument('--merge',           help='Use state-merging after determinization', action="count", default=0)
    p.add_argument('--stutter',         help='Use stutter-invarince in determinization', action="count", default=0)
    p.add_argument('--sim',             help='Use simulation relation in determinization', action="count", default=0)
    p.add_argument('--pariwc',          help='Handle IWC separately in determinization', action="count", default=0)
    p.add_argument('--parity',          help='Output deterministic Parity automaton', action="count", default=0)
    p.add_argument('--workers',         help='Number of workers (default: %s)' % num_cores, type=int, default=num_cores)
    p.add_argument('--verbose',         help='Verbose level (default: %s)' % ARG_VERB_LEVEL, type=int, default=ARG_VERB_LEVEL)
    args, leftovers = p.parse_known_args()
    return args, p.parse_args()
    
def setup():
    global opts
    global input_file
    global verbose
    global parity
    global sim_str
    global stu_str
    global mgr_str
    global compl
    global pariwc
    global num_workers
    
    num_workers = multiprocessing.cpu_count()
    
    known, opts = getopts(header)
    
    if not os.path.isfile(opts.file):
        raise Exception("Unable to find file: %s" % opts.file)
    input_file = opts.file

    #print(opts.acd)
    #if (opts.acd > 0):
    #    acd_str = ARG_ACD_STR
    
    if (opts.sim > 0):
        sim_str = ARG_SIM_STR
    
    if (opts.merge > 0):
        mgr_str = ARG_MGR_STR
        
    if (opts.stutter > 0):
        stu_str = ARG_STU_STR
        
    if (opts.verbose > 0):
        verbose = opts.verbose
    
    if (opts.parity > 0):
        parity = True
    
    if (opts.comp > 0):
        compl = True
        
    if (opts.pariwc > 0):
        pariwc = True
        
    if not (opts.workers == num_workers):
        num_workers = opts.workers
        
    if verbose > 0:
        print("setting: " + sim_str + ", " + mgr_str + ", " + stu_str + ", " + str(parity) + ", " + str(compl) + ", " + str(pariwc) + ", " + str(num_workers))

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
    command = [cola_exe, '--determinize=ba', arg, '-o', output_bas + file_name, '--acd', '--parity']
    
    if sim_str:
        command.append(sim_str)
    if stu_str:
        command.append(stu_str)
    if mgr_str:
        command.append(mgr_str)

    if verbose > 0:
        print(command)
    subprocess.call(command)
    return file_name
    
def compose_dpas(p_queue):
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
    global num_workers
    
    if num_workers == 0:
        num_workers = len(aut_names)
    
    pool = multiprocessing.Pool(processes = num_workers)
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
                #print(filename)
                to_remove.append(r)
                aut = spot.automaton(output_bas + filename)
                aut = aut.postprocess('parity', 'deterministic', 'low')
                #print ('current aut: ' + str(aut.num_states()))
                p_queue.put((aut.num_states(), aut))
        # compose
        compose_dpas(p_queue)
        for remove in to_remove:
            pool_results.remove(remove)
    
        #time.sleep(1) # ensures that this thread doesn't consume too much memory
    # waiting for all sub-processes finishing
    pool.join()
    num_states, res_aut = p_queue.get() #heapq.heappop(hq)#
    return res_aut

# write decomposed automaton to files
def write_aut_to_file(small_auts, file_name):
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
    aut = spot.automaton(file_name)
    # now prepare to decompose this NBA
    if verbose > 0:
        print("Number of states in the input: " + str(aut.num_states()))
    si = spot.scc_info(aut)
    
    num_iwcs = 0
    num_others = 0

    # now decompose for DACs and NACs
    small_auts = []
    weak_count = "" # accepting weak SCC counts
    for scc in range(si.scc_count()):
        if not spot.is_inherently_weak_scc(si, scc) and si.is_accepting_scc(scc):
            # only keep those SCCs as accepting
            other_aut =  spot.decompose_scc(si, str(scc))
            small_auts.append(other_aut)
            num_others += 1
        elif spot.is_inherently_weak_scc(si, scc) and si.is_accepting_scc(scc):
            if pariwc:
                other_aut =  spot.decompose_scc(si, str(scc))
                small_auts.append(other_aut)
                num_iwcs += 1
            else:
                if len(weak_count) == 0:
                    weak_count = str(scc)
                else:
                    weak_count += "," + str(scc)
    if weak_count:
        weak_aut = spot.decompose_scc(si, weak_count)
        small_auts.append(weak_aut)
        num_iwcs += 1
    
    if verbose > 0:
        print("#IWCS, #OTHERS: " + str(num_iwcs) + ", " + str(num_others))
        
    if verbose > 1:
        for other_aut in small_auts:
            print(other_aut.to_str('hoa'))
        print ("#smallnbas = " + str(len(small_auts)))
    
    # in case the language is empty
    if len(small_auts) == 0:
        small_auts.append(make_empty_nba(aut.get_dict()))
    
    return small_auts
    # now do postprocessing on each of them, this will be done in CPP code in cola
#    res_auts = []
#    for sub_aut in small_auts:
#        sub_aut = sub_aut.postprocess('low', 'buchi')
#        res_auts.append(sub_aut)
    
#    return res_auts
    

def compose_dpas2(aut_names):

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
    
def clean():
    if os.path.exists(input_bas) and os.path.isdir(input_bas):
        shutil.rmtree(input_bas)
    if os.path.exists(output_bas) and os.path.isdir(output_bas):
        shutil.rmtree(output_bas)    

def main():
    setup()
    
    if not os.path.isdir(input_bas):
        os.mkdir(input_bas)
    if not os.path.isdir(output_bas):
        os.mkdir(output_bas)
    
    file_name = input_file
    
    if verbose > 0:
        print("Input file name: " + file_name)
    
    if not os.path.exists(file_name):
        print(file_name + " not exists")
        exit(1)
    
    arg_list.append(file_name)
    #print(arg_list)
    small_auts = decompose_nba(file_name)
    aut_names = write_aut_to_file(small_auts, file_name)
    res_aut = run_command_all(aut_names)
    # obtain parity output
    if parity:
        res_aut = spot.acd_transform(res_aut)
        res_aut = res_aut.postprocess('parity', 'deterministic', 'low')
    # output complement automaton    
    if compl:
        res_aut = spot.dualize(res_aut)
        res_aut = res_aut.postprocess('buchi', 'low')
    # res_aut = compose_dpas(aut_names)
    print(res_aut.to_str('hoa'))
    
    if not verbose:
        clean()
    
if __name__ == "__main__":
    main()
