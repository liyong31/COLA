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

arg_list = [] ## the 
output_bas = "cola-outputs/"
input_bas = "cola-inputs/"
suffix = ".hoa"
cola_exe = "./cola" # please use exact path
input_file = ""

owl_exe = "../../CAV/COLA/owl"



header="""
---------------------------------------------------------------
COLA -- A library for Büchi automata and for LTL
---------------------------------------------------------------
  
  Reads a file with linear temporal logic and transforms it to 
  deterministic Emerson-Lei automaton
  
  Copyright (c) 2022 - Present  COLA authors
  
  Please report bugs via email (liyong@ios.ac.cn) or on 
  github (https://github.com/liyong31/COLA)	
---------------------------------------------------------------
"""

short_header="""COLA -- A determinization library for nondeterministic Büchi automata
Copyright (c) 2022 - Present  COLA authors"""

def getopts(header):
    p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('file', help='file name for the input automaton in HOA format', type=str)
#    p.add_argument('--acd',             help='Use Alternating Cycle Decompostion for obtaining Parity automata', action="count", default=0)
    p.add_argument('--comp',            help='Compare with complement and output', action="count", default=0)
    p.add_argument('--owlexe',         help='Specify where the OWL executable is', type=str, default=0)
#    p.add_argument('--merge',           help='Use state-merging after determinization', action="count", default=0)
#    p.add_argument('--stutter',         help='Use stutter-invarince in determinization', action="count", default=0)
#    p.add_argument('--sim',             help='Use simulation relation in determinization', action="count", default=0)
#    p.add_argument('--pariwc',          help='Handle IWC separately in determinization', action="count", default=0)
    p.add_argument('--parity',          help='Output deterministic Parity automaton', action="count", default=0)
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
    global owl_exe
    
    
    known, opts = getopts(header)
    
    if not os.path.isfile(opts.file):
        raise Exception("Unable to find file: %s" % opts.file)
    input_file = opts.file

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
def make_empty_nba(bdict):
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



def main():
    setup()
    # relies on owl to obtain the delta2 form
    command = [owl_exe, 'ltl2delta2', '-i', input_file]
    if verbose > 0: print(command)
    ret_formula = None
    try:
        ret_formula = subprocess.check_output(command)
    except OSError as e:
        print >> sys.stderr, "Execution failed:", e
    ret_formula = str(ret_formula.decode("utf-8")).strip().replace('!', '! ')
    if verbose > 0 and ret_formula:
        print(ret_formula)
    if not ret_formula:
        print('error')
    f = spot.formula(ret_formula)
    if verbose > 0 : print(f)
    ## the formula should be big disjunction
    #if (f.kind() == spot.op_Or):
    #    print >> sys.stderr, "Execution failed:", e
    ## obtain the children
    p_queue = queue.PriorityQueue()
    for child in f:
        if verbose > 0: print(child)        
        aut = child.translate('deterministic', 'generic')
        aut = spot.acd_transform(aut)
        #print(aut.to_str('HOA'))
        p_queue.put((aut.num_states(), aut))
        
    ## now we compose into one
    compose_dpas(p_queue)
    num_states, res_aut = p_queue.get() #heapq.heappop(hq)#
    if parity:
        res_aut = spot.acd_transform(res_aut)
    print(res_aut.to_str('HOA'))
    
if __name__ == "__main__":
    main()
