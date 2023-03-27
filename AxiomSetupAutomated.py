import itertools
from copy import deepcopy
import timeit
import re
import collections
import getopt
import sys
import numpy as np


# Wirting up: results of Skolem, examples with lattices and semilattices
# Normal Theory extensions
#
# Presenting the code:
# Have a flow diagram for the data
#

def getBasefile(file):
    important_lines = []
    with open(file, "r") as f:
        lines = f.readlines()
        for line in lines:
            if("Instantiate" in line):
                important_lines.append(line.strip("\n"))
    return important_lines

def extractArgs(lines):
    args = []
    for line in lines:
        inst = line.split("Instantiate(")[1].split(")")[0]
        args.append([line.split("%"), inst.split(",")])
    return args

def getQuery(file):
    res = []
    ignore = True
    with open(file, "r") as f:
        lines = f.readlines()
        for line in lines:
            if line.startswith("Query"):
                ignore = False
            if not ignore: 
                res.append(line.strip())
    return res[1:]

def getOccurencesOfFunction(clause, func):
    clause.split(func)
    matches = re.findall(f"{func}\(([^\)]+)\)", clause)
    args = [func + "(" + elem + ")" for elem in matches]
    return args

def getConstantsFromTerms(terms, func):
    res = []
    for term in terms:
        if func in term:
            res += term.split(func)[1][1:-1].split(",")
    return res

def getListOfFunctionCalls(axioms, args):
    res = []
    for arg in args:
        for axiom in axioms:
            for func in arg[1]:
                if func in axiom:
                    occurences = getOccurencesOfFunction(axiom, func)
                    res += occurences
    return list(set(res))

def getListOfConstants(terms, functions):
    res = []
    for function in functions:
        listOfConstants = getConstantsFromTerms(terms, function)
        res += listOfConstants
    return list(set(res))
        
def generate_tuples(inset, n):
    return list(itertools.product(inset, repeat=n))

def getInstancesOfAxiom(axiom, vars, constants):
    tuples = generate_tuples(constants, len(vars))
    var_counter = 1
    tmp_axiom = deepcopy(axiom)
    for var in vars:
        tmp_axiom = tmp_axiom.replace(var.strip(), f"{var_counter}")
        var_counter = var_counter + 1
    instances = []
    for tuple in tuples:
        counter = 1
        instance = deepcopy(tmp_axiom)
        for const in tuple:
            instance = instance.replace(f"{counter}", const)
            counter = counter + 1
        instances.append(instance)
    return instances

def deleteAxioms(file):
    res = ""
    with open(file, "r") as f:
        lines = f.readlines()
        for line in lines:
            if("Instantiate" in line):
                line = ""
            res = res + line
    return res

def addInstances(file, instances):
    #print(instances)
    file += "\n"
    for instance in instances:
        instance += "\n"
        file += instance
    return file

def instantiatePipeline(file):
    base = getBasefile(file)
    args = extractArgs(base)
    query = getQuery(file)
    tmp_axioms = [elem[0][0].lstrip() for elem in args]
    vars = []
    axioms = []
    for axiom in tmp_axioms:
        if axiom.startswith("(FORALL"):
            vars.append(axiom.split("(FORALL ")[1].split(")")[0].split(","))
            axioms.append(axiom.split(". ")[1].lstrip())
    functionCalls = getListOfFunctionCalls(query, args)
    functions = []
    for arg in args:
        functions += arg[1]
    res = [list(zip(vars, axioms))]
    res += [functionCalls] + [functions]
    return res

def get_function(instance, func):
    instance_seperated = re.findall('\w+(?=\s*\([^/])', instance)
    #instance_seperated = re.findall('\[.*?\]',instance)
    #instance_seperated = [instance.split(",")[1][:-1] for instance in instance_seperated]
    for entry in instance_seperated:
        if func in entry:
            instance_seperated.remove(entry)
            return instance_seperated
    print(f"Function{func} not found in {instance}")
    return []

def update_functionCalls(axiom, functionCalls, functions):
    tmp = []
    for call in functionCalls:
        argument = re.findall('\(.*?\)', call)[0][1:-1]
        called_func = str(re.findall("^[^\(]+", call)[0])
        other_functions = [func for func in functions if func != called_func]
        other_functioncalls = [getOccurencesOfFunction(axiom, function) for function in other_functions]
        other_functioncalls = [functioncall[0] for functioncall in other_functioncalls if functioncall]
        other_functioncalls = [functioncall for functioncall in other_functioncalls if functioncall in axiom]
        #replace_this = [re.findall('\(.*?\)', functioncall)[0][1:-1] for functioncall in other_functioncalls]
        functions_to_add = [function.replace(re.findall('\(.*?\)', function)[0][1:-1], argument) for function in other_functioncalls]
        tmp += functions_to_add
    functionCalls += tmp
    functionCalls = [call.strip() for call in functionCalls]
    functionCalls = list(set(functionCalls))
    return functionCalls

def main(file):
    preprocessedFile = instantiatePipeline(file)
    vars_and_axioms = preprocessedFile[0]
    functionCalls = preprocessedFile[1]
    functions = preprocessedFile[2]
    functions = [function.strip() for function in functions]
    newFuncCalls = []
    for entry in vars_and_axioms:
        if "-->" in entry[1]:
            tmp = update_functionCalls(entry[1], functionCalls, functions)
            while True:
                tmp = list(set(update_functionCalls(entry[1], tmp, functions)))
                if collections.Counter(tmp) == collections.Counter(update_functionCalls(entry[1], tmp, functions)):
                    break
            newFuncCalls.append(list(set(tmp)))
    #print("New Function Calls: ", newFuncCalls)
    functionCalls.append(newFuncCalls)
    constants = getListOfConstants(functionCalls, functions)

    instances = []
    for entry in vars_and_axioms:
        instances.append(getInstancesOfAxiom(entry[1], entry[0], constants))
    tmp_file = deleteAxioms(file)
    for entry in instances:
        tmp_file = addInstances(tmp_file, entry)
    with open(file.replace(".txt", "_new.txt"), 'w') as f:
        f.write(tmp_file)
    return tmp_file

main("distances_2.txt")
#Vars and axioms:  (['x', ' y'], 'R[x, po(y)] --> R[hl(x), hl(y)];')
#Function calls:  ['po(RV)', 'po(LV)', ' hl(H)', ' hl(Em)', 'po(H)', 'po(HW)']
#Functions:  ['po', ' hl']

#print("\n", main(sys.argv[1]))

#times = []
#for i in range(0, 100):
#    start = timeit.default_timer()
#    main("EL1_basic_v2.txt")
#    stop = timeit.default_timer()
#    times.append(stop-start)

#print(times)
#print(np.mean(times))


def write_base_file(content, name):
    with open(name, "w") as f:
        f.write('\n'.join(content))

#TODO: Check if all instances generated are correct or if any are missing