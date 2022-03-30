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
# replace all ap in f_str with ap_map[ap]
import re

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

arg_list = [] ## the 
output_bas = "cola-outputs/"
input_bas = "cola-inputs/"
suffix = ".hoa"
cola_exe = "./cola" # please use exact path
input_file = ""

owl_exe = "../../CAV/COLA/owl"



header="""
---------------------------------------------------------------
COLA -- A library for Büchi automata and LTL
---------------------------------------------------------------
  
  Reads a file with linear temporal logic and transforms it to 
  deterministic Emerson-Lei automaton
  
  Copyright (c) 2022 - Present  COLA authors
  
  Please report bugs via email (liyong@ios.ac.cn) or on 
  github (https://github.com/liyong31/COLA)	
---------------------------------------------------------------
"""

short_header="""COLA -- A library for Büchi automata and LTL
Copyright (c) 2022 - Present  COLA authors"""

def getopts(header):
    p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('input',    help='file name or the formula string', type=str)
#    p.add_argument('--acd',             help='Use Alternating Cycle Decompostion for obtaining Parity automata', action="count", default=0)
    p.add_argument('--comp',             help='compare with complement and output', action="count", default=0)
    p.add_argument('--owlexe',           help='cpecify where the OWL executable is', type=str, default=0)
#    p.add_argument('--merge',           help='Use state-merging after determinization', action="count", default=0)
#    p.add_argument('--stutter',         help='Use stutter-invarince in determinization', action="count", default=0)
#    p.add_argument('--sim',             help='Use simulation relation in determinization', action="count", default=0)
#    p.add_argument('--pariwc',          help='Handle IWC separately in determinization', action="count", default=0)
    p.add_argument('--parity',          help='output deterministic Parity automaton', action="count", default=0)
    p.add_argument('--verbose',         help='verbose level (default: %s)' % ARG_VERB_LEVEL, type=int, default=ARG_VERB_LEVEL)
    args, leftovers = p.parse_known_args()
    return args, p.parse_args()
    
    
def make_empty_nba():
    bdict = spot.make_bdd_dict();
    aut = spot.make_twa_graph(bdict)
    aut.set_acceptance(1, "Inf(0)");
    aut.new_states(1)
    aut.set_init_state(0)
    aut.new_edge(0, 0, buddy.bddtrue)
    return aut
    
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
    global owl_exe
    
    
    known, opts = getopts(header)
    
    #if not os.path.isfile(opts.input):
    #    raise Exception("Unable to find file: %s" % opts.file)
    input_file = opts.input

    #print(opts.acd)
    #if (opts.acd > 0):
    #    acd_str = ARG_ACD_STR
    
    #if (opts.sim > 0):
    #    sim_str = ARG_SIM_STR
    
    #if (opts.merge > 0):
    #    mgr_str = ARG_MGR_STR
        
    #if (opts.stutter > 0):
    #    stu_str = ARG_STU_STR
        
    if (opts.verbose > 0):
        verbose = opts.verbose
    
    if (opts.parity > 0):
        parity = True
    
    if (opts.comp > 0):
        compl = True
        
    if (opts.owlexe):
        owl_exe = opts.owlexe
        
    #if (opts.pariwc > 0):
    #    pariwc = True
        
    if verbose > 0:
        print("setting: " + sim_str + ", " + mgr_str + ", " + stu_str + ", " + str(parity) + ", " + str(compl) + ", " + str(pariwc))

setattr(spot.twa_graph, "__lt__", lambda self, other: self.num_states() <= other.num_states())

# make an NBA with empty language
def make_empty_nba():
    bdict = spot.make_bdd_dict();
    aut = spot.make_twa_graph(bdict)
    aut.set_acceptance(1, "Inf(0)");
    aut.new_states(1)
    aut.set_init_state(0)
    aut.new_edge(0, 0, buddy.bddtrue)
    return aut
    
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
        
def construct_from_ltl(f, filename):
    #command = [cola_exe, '--determinize=ba', arg, '-o', output_bas + file_name, '--acd', '--parity']
    aut = child.translate('deterministic', 'generic')
    aut = aut.postprocess('deterministic', 'generic', 'low')
    return aut
    
# given the list of automaton names
def run_translation(f_list):
    pool = multiprocessing.Pool(processes = len(f_list))
    pool_results = []
    for child in f_list:
        pool_results.append(pool.apply_async(construct_from_ltl, args=(child)))
    pool.close()
    
    res_aut = None
    p_queue = queue.PriorityQueue()
    
    while len(pool_results) > 0:
        to_remove = [] #avoid removing objects during for_loop
        for r in pool_results:
            # check if process is finished
            if r.ready(): 
                # print result (or do any operation with result)
                aut = r.get()
                #print(filename)
                to_remove.append(r)
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




#lambda-based implementation
def multiple_replace(adict, text):
  # Create a regular expression from all of the dictionary keys
  regex = re.compile("|".join(map(re.escape, adict.keys(  ))))
  # For each match, look up the corresponding value in the dictionary
  return regex.sub(lambda match: adict[match.group(0)], text)


def translate_ltl_to_dela(f_str):

    f_str = f_str.replace('!', '! ')
    f = spot.formula(f_str)
    
    if f == spot.formula.ff():
        return make_empty_nba()
    if verbose > 0:
        print('Input formula: ' + f.to_str('spot'))
    
    ap_set = spot.atomic_prop_collect(f)
    ap_str_list = []
    for ap in ap_set:
        ap_str_list.append(str(ap))
    ap_str_list.sort()
    ap_map = {}
    ap_rmap = {}
    count = 0
    new_f_str = spot.str_psl(f, True)
    prefix = '_xxx_a_XXX_Y'
    for ap in ap_str_list:
        to_str = '(' + prefix + str(count) + ')'
        from_str = '(' + ap + ')'
        ap_map[from_str] = to_str
        ap_rmap[to_str] = from_str
        if verbose > 0: print(from_str + ' -> ' + to_str)
        #new_f_str = new_f_str.replace(str(ap), to_str)
        count += 1
    
    new_f_str = multiple_replace(ap_map, new_f_str)
    if verbose > 0: print("replaced: " + new_f_str)
    
    command = [owl_exe, 'ltl2delta2', '-f', new_f_str]
    if verbose > 0: print(command)
    
    ret_formula = None
    try:
        ret_formula = subprocess.check_output(command)
    except OSError as e:
        print >> sys.stderr, "Execution failed:", e
    ret_formula = str(ret_formula.decode("utf-8")).strip().replace('!', '! ')
    #if verbose > 0 and ret_formula:
    #    print(ret_formula)
    if not ret_formula:
        print('error output from owl')
        exit(1)
        
    if len(ret_formula) < 10 * len(f_str):
        #return make_empty_nba()
        # change atomic propositions back
        new_f = spot.formula(ret_formula)
        new_f_str = spot.str_psl(new_f, True)
        ret_formula = multiple_replace(ap_rmap, new_f_str)
        f = spot.formula(ret_formula)
    
    if verbose > 0 : print(f)
    if f == spot.formula.ff():
        return make_empty_nba()
    ## the formula should be big disjunction
    #if (f.kind() == spot.op_Or):
    #    print >> sys.stderr, "Execution failed:", e
    ## obtain the children
    
    
    f_list = []
    if f.kind() == spot.op_Or:
        for child in f:
            f_list.append(f)
    else:
        f_list.append(f)
    
    #return run_translation(f_list)
    
    p_queue = queue.PriorityQueue()
    for child in f_list:
        if verbose > 0: print(child)        
        aut = child.translate('deterministic', 'generic')
        aut = aut.postprocess('deterministic', 'generic', 'low')
        #aut = spot.acd_transform(aut).postprocess('deterministic', 'parity')
        #print(aut.to_str('HOA'))
        p_queue.put((aut.num_states(), aut))
        
    ## now we compose into one
    compose_dpas(p_queue)
    num_states, res_aut = p_queue.get() #heapq.heappop(hq)#
    
    return res_aut

def main():
    setup()
    # relies on owl to obtain the delta2 form
    f_list = []
    if not os.path.exists(input_file):
        f_list.append(input_file)
    else:
        f_file = open(input_file, 'r')
        f_list = f_file.readlines()
    for line in f_list:
        res_aut = translate_ltl_to_dela(line)
        if parity:
            res_aut = spot.acd_transform(res_aut)
        print(res_aut.to_str('HOA'))
    
if __name__ == "__main__":
    main()
