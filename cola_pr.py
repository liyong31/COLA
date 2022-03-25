import spot
from spot import buddy


import multiprocessing
import os
import subprocess
import getopt, sys
import queue # import PriorityQueue
import heapq


filename_list = []
arg_list = [] ## the 

output_bas = "outputs/"
input_bas = "inputs/"
input_name = "nba"
output_name = "dpa"
suffix = ".hoa"

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

def custom_print(aut):
    bdict = aut.get_dict()
    print("Initial states: ", aut.get_init_state_number())
    print("AP:", end='')
    for ap in aut.ap():
        print(' ', ap, ' (=', bdict.varnum(ap), ')', sep='', end='')
    print()
    # Templated methods are not available in Python, so we cannot
    # retrieve/attach arbitrary objects from/to the automaton.  However the
    # Python bindings have get_name() and set_name() to access the
    # "automaton-name" property.
    name = aut.get_name()
    if name:
        print("Name: ", name)
    print("Deterministic:", aut.prop_universal() and aut.is_existential())
    print("Unambiguous:", aut.prop_unambiguous())
    print("State-Based Acc:", aut.prop_state_acc())
    print("Terminal:", aut.prop_terminal())
    print("Weak:", aut.prop_weak())
    print("Inherently Weak:", aut.prop_inherently_weak())
    print("Stutter Invariant:", aut.prop_stutter_invariant())

    for s in range(0, aut.num_states()):
        print("State {}:".format(s))
        for t in aut.out(s):
            print("  edge({} -> {})".format(t.src, t.dst))
            # bdd_print_formula() is designed to print on a std::ostream, and
            # is inconvenient to use in Python.  Instead we use
            # bdd_format_formula() as this simply returns a string.
            print("    label =", spot.bdd_format_formula(bdict, t.cond))
            print("    acc sets =", t.acc)

def get_all_files(path, file = ""):
    tmpList = os.listdir(path)
    
    for tmp in tmpList:
        arg_list.append(path + tmp)
    #print(arg_list)

def run_command(arg, file_name):
    # subprocess.call(['./cola', '--determinize=cola', 'multiRun/inputs/' + filename, '-o', 'multiRun/outputs/' + filename + '_dpa', '--parity', '--acd', '--simulation', '--stutter', '--use-scc'])
    command = ['./cola', '--determinize=ba', arg, '-o', output_bas + file_name, '--parity', '--simulation', '--stutter', '--use-scc']
    subprocess.call(command)
    # print(command)

def run_command_all(aut_name_list):
    # print(len(filename_list))
    pool = multiprocessing.Pool(processes = len(aut_name_list))
    for aut_name in aut_name_list:
        filepath, filename = os.path.split(aut_name)
        pool.apply_async(run_command, args=(aut_name, filename))
    pool.close()

    # waiting for all sub-processes finishing
    pool.join()
    
def write_aut_to_file(sub_auts):
    aut_name = None
    for file_name in arg_list:
        filepath, filename = os.path.split(file_name)
        aut_name = filename
        break
    num_count = 0
    aut_name_list = []
    for sub_aut in sub_auts:
        sub_aut_name = input_bas + aut_name + str(num_count) + suffix
        aut_name_list.append(sub_aut_name)
        #print (sub_aut_name + " num= " + str(sub_aut.num_states()))
        text_file = open(sub_aut_name, "w")
        n = text_file.write(sub_aut.to_str('hoa'))
        text_file.close()
        num_count += 1   
    return aut_name_list
    
def decompose_nba():
    # print(arg_list)
    aut = None
    for file_name in arg_list:
        aut = spot.automaton(file_name)
        break
    # now prepare to decompose this NBA
    #print("Number of states in automaton: " + str(aut.num_states()))
    si = spot.scc_info(aut)
    #print("original:")
    #custom_print(aut)
    
    # now decompose for DACs and NACs
    sub_auts = []
    
    weak_count = ""
    for scc in range(si.scc_count()):
        if not spot.is_inherently_weak_scc(si, scc) and si.is_accepting_scc(scc):
            other_aut =  spot.decompose_scc(si, str(scc))
            sub_auts.append(other_aut)
        elif spot.is_inherently_weak_scc(si, scc) and si.is_accepting_scc(scc):
            if len(weak_count) == 0:
                weak_count = str(scc)
            else:
                weak_count += "," + str(scc)
    if len(weak_count) > 0:
        weak_aut = spot.decompose_scc(si, weak_count)
        
        sub_auts.append(weak_aut)
        #print("SCC #{} contains states {}, weak = {}, det = {}, acc = {}".format(scc, list(si.states_of(scc)), spot.is_inherently_weak_scc(si, scc), is_deterministic_scc(si, scc), si.is_accepting_scc(scc)))
    #print ("HasAccweak? " + weak_count)
    #custom_print(weak_aut)
    #print(weak_aut.to_str('hoa'))
    #for other_aut in sub_auts:
    #    print(other_aut.to_str('hoa'))
    #print ("#nbas = " + str(len(sub_auts)))
    return sub_auts
    

def compose_dpas(aut_name_list):
    #print(aut_name_list)

    p_queue = queue.PriorityQueue()
    hq = []
    setattr(spot.twa_graph, "__lt__", lambda self, other: self.num_states() <= other.num_states())
    for aut_name in aut_name_list:
        filepath, filename = os.path.split(aut_name)
        # print (output_bas + filename)
        aut = spot.automaton(output_bas + filename)
        aut = aut.postprocess('parity', 'deterministic', 'low')
        #print ('current aut: ' + str(aut.num_states()))
        p_queue.put((aut.num_states(), aut))
        #heapq.heappush(hq, (aut.num_states(), aut))

    while p_queue.qsize() > 1:
        fst_num_states, fst_aut = p_queue.get() #heapq.heappop(hq)#
        #print ("get num = " + str(fst_num_states))
        snd_num_states, snd_aut = p_queue.get() # heapq.heappop(hq)#
        #print ("get num = " + str(snd_num_states))
        res_aut = spot.product_or(fst_aut, snd_aut)
        #print ("get res = " + str(res_aut.num_states()))
        spot.simplify_acceptance_here(res_aut)
        res_aut = res_aut.postprocess('generic', 'deterministic', 'low')
        p_queue.put((res_aut.num_states(), res_aut))
        #heapq.heappush(hq, (res_aut.num_states(), res_aut))
    num_states, res_aut = p_queue.get() #heapq.heappop(hq)#
    return res_aut
    # only one left

def main():
    opts, args = getopt.getopt(sys.argv[1:], 'f:d', )
    # print(opts)
    # print(args)
    if not os.path.isdir(input_bas):
        os.mkdir(input_bas)
    if not os.path.isdir(output_bas):
        os.mkdir(output_bas)
    
    count = 0
    for prefix, arg in opts:
        if prefix == '-f':
            #print(arg)
            if not os.path.exists(arg):
                continue
            arg_list.append(arg)
            #print(arg_list)
            sub_auts = decompose_nba()
            aut_name_list = write_aut_to_file(sub_auts)
            run_command_all(aut_name_list)
            res_aut = compose_dpas(aut_name_list)
            print(res_aut.to_str('hoa'))
            count += 1
            #run_command_all([])
        
    #    if op == ('-d', ''):
    #        arg_list.clear()
    #        for arg in args:
    #            get_all_files(arg)
    #        run_command_all()
    if count <= 0:
        print("File may not exist")
    #print("finished")
    # setup()
    # run_command_all()

if __name__ == "__main__":
    main()
