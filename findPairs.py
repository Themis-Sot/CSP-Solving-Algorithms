"""Find correct pair of radio frequencies"""

import itertools
import random
import re
import string
from collections import defaultdict, Counter
from functools import reduce
from operator import eq, neg

from sortedcontainers import SortedSet

import search
from utils import argmin_random_tie, count, first, extend

import time




def OpenVar(filename):
    f = open(filename, "r")                     #open the file
    lines = f.readlines()

    variableDomains = []

    for i in range(len(lines)):
        if i != 0:
            line = lines[i].split()             #split the line to elements
            variable = int(line[0])             #first element is the variable
            domain = int(line[1])               #second is the domain
            variableDomains.append((variable, domain))              #put them into a list as tuple
        else:
            numVars = int(lines[i])             #number of variables is the first number of the file

    f.close()
    return variableDomains                      #return list

def OpenDom(filename, variableDomains):
    f = open(filename, "r")
    lines = f.readlines()

    domains = {}
    for x, y in variableDomains:
        for i in range(len(lines)):
            if i != 0:
                line = lines[i].split()
                numOfDom = int(line[0])         #first element of line is the number of the domain
                if y == numOfDom:
                    domainList = []
                    numValues = int(line[1])    #second is the number of values
                    for j in range(numValues):
                        domainList.append(int(line[2 + j]))         #add the values to the domain list
                    domains[x] = domainList                         #add the list to the value of the dictionary where key is the variable
                    domainList = []
                    break
            else:
                numDoms = int(lines[i])         #number of domains is the first number of the file

    f.close()
    return domains                              #return dictionary of domain


def OpenCtr(filename):
        
    f = open(filename, "r")
    lines = f.readlines()

    neighbors = {}
    constraints = {}

    for j in range(len(lines)):
        if j != 0:
            line = lines[j].split()
            var1 = int(line[0])             #first element of line is the first variable of the constraint
            var2 = int(line[1])             #second element is the second variable
            line.pop(0)                     #pop out the variables
            line.pop(0)
            constraints[(var1, var2)] = line        #add the constraint to the value of the dictionary where key is the tuple containing the variables
            var1neigh = []
            var2neigh = []
            if var1 in neighbors:                   #if first variable has already neighbors
                var1neigh = neighbors.get(var1)     #get the list of neighbors

            var1neigh.append(var2)                  #append the new neighbor to its list
            neighbors[var1] = var1neigh             #make the value of the dictionary where key is the first variable equal to new list of neighbors

            if var2 in neighbors:                   #if second variable has already neighbors
                var2neigh = neighbors.get(var2)     #get the list of neighbors

            var2neigh.append(var1)                  #append the new neighbor to its list
            neighbors[var2] = var2neigh             #make the value of the dictionary where key is the second variable equal to new list of neighbors
        else:
            numConstr = int(lines[j])

    f.close()
    return neighbors, constraints                   #return both dictionaries
                    


class CSP(search.Problem):
    """This class describes finite-domain Constraint Satisfaction Problems.
    A CSP is specified by the following inputs:
        variables   A list of variables; each is atomic (e.g. int or string).
        domains     A dict of {var:[possible_value, ...]} entries.
        neighbors   A dict of {var:[var,...]} that for each variable lists
                    the other variables that participate in constraints.
        constraints A function f(A, a, B, b) that returns true if neighbors
                    A, B satisfy the constraint when they have values A=a, B=b
    In the textbook and in most mathematical definitions, the
    constraints are specified as explicit pairs of allowable values,
    but the formulation here is easier to express and more compact for
    most cases (for example, the n-Queens problem can be represented
    in O(n) space using this notation, instead of O(n^4) for the
    explicit representation). In terms of describing the CSP as a
    problem, that's all there is.
    However, the class also supports data structures and methods that help you
    solve CSPs by calling a search function on the CSP. Methods and slots are
    as follows, where the argument 'a' represents an assignment, which is a
    dict of {var:val} entries:
        assign(var, val, a)     Assign a[var] = val; do other bookkeeping
        unassign(var, a)        Do del a[var], plus other bookkeeping
        nconflicts(var, val, a) Return the number of other variables that
                                conflict with var=val
        curr_domains[var]       Slot: remaining consistent values for var
                                Used by constraint propagation routines.
    The following methods are used only by graph_search and tree_search:
        actions(state)          Return a list of actions
        result(state, action)   Return a successor of state
        goal_test(state)        Return true if all constraints satisfied
    The following are just for debugging purposes:
        nassigns                Slot: tracks the number of assignments made
        display(a)              Print a human-readable representation
    """

    def __init__(self, variables, domains, neighbors, constraints):
        """Construct a CSP problem. If variables is empty, it becomes domains.keys()."""
        super().__init__(())
        variables = variables or list(domains.keys())
        self.variables = variables
        self.domains = domains
        self.neighbors = neighbors
        self.constraints = constraints
        self.curr_domains = None
        self.nassigns = 0
        self.weights = {}
        
        for n1 in self.neighbors:               #for every neighboring variables
            for n2 in self.neighbors[n1]:
                nTuple = (n1, n2)
                self.weights[nTuple] = 1        #initialize their wheight of constraint to 1

    def assign(self, var, val, assignment):
        """Add {var: val} to assignment; Discard the old value if any."""
        assignment[var] = val
        self.nassigns += 1

    def unassign(self, var, assignment):
        """Remove {var: val} from assignment.
        DO NOT call this if you are changing a variable to a new value;
        just call assign for that."""
        if var in assignment:
            del assignment[var]

    def nconflicts(self, var, val, assignment):
        """Return the number of conflicts var=val has with other variables."""

        # Subclasses may implement this more efficiently
        def conflict(var2):
            
            return var2 in assignment and not self.constraints(var, val, var2, assignment[var2])

        return count(conflict(v) for v in self.neighbors[var])

    def display(self, assignment):
        """Show a human-readable representation of the CSP."""
        # Subclasses can print in a prettier way, or display with a GUI
        print(assignment)

    # These methods are for the tree and graph-search interface:

    def actions(self, state):
        """Return a list of applicable actions: non conflicting
        assignments to an unassigned variable."""
        if len(state) == len(self.variables):
            return []
        else:
            assignment = dict(state)
            var = first([v for v in self.variables if v not in assignment])
            return [(var, val) for val in self.domains[var]
                    if self.nconflicts(var, val, assignment) == 0]

    def result(self, state, action):
        """Perform an action and return the new state."""
        (var, val) = action
        return state + ((var, val),)

    def goal_test(self, state):
        """The goal is to assign all variables, with all constraints satisfied."""
        assignment = dict(state)
        return (len(assignment) == len(self.variables)
                and all(self.nconflicts(variables, assignment[variables], assignment) == 0
                        for variables in self.variables))

    # These are for constraint propagation

    def support_pruning(self):
        """Make sure we can prune values from domains. (We want to pay
        for this only if we use it.)"""
        if self.curr_domains is None:
            self.curr_domains = {v: list(self.domains[v]) for v in self.variables}

    def suppose(self, var, value):
        """Start accumulating inferences from assuming var=value."""
        self.support_pruning()
        removals = [(var, a) for a in self.curr_domains[var] if a != value]
        self.curr_domains[var] = [value]
        return removals

    def prune(self, var, value, removals):
        """Rule out var=value."""
        self.curr_domains[var].remove(value)
        if removals is not None:
            removals.append((var, value))

    def choices(self, var):
        """Return all values for var that aren't currently ruled out."""
        return (self.curr_domains or self.domains)[var]

    def infer_assignment(self):
        """Return the partial assignment implied by the current inferences."""
        self.support_pruning()
        return {v: self.curr_domains[v][0]
                for v in self.variables if 1 == len(self.curr_domains[v])}

    def restore(self, removals):
        """Undo a supposition and all inferences from it."""
        for B, b in removals:
            self.curr_domains[B].append(b)

    # This is for min_conflicts search

    def conflicted_vars(self, current):
        """Return a list of variables in current assignment that are in conflict"""
        return [var for var in self.variables
                if self.nconflicts(var, current[var], current) > 0]


def no_arc_heuristic(csp, queue):
    return queue


def dom_j_up(csp, queue):
    return SortedSet(queue, key=lambda t: neg(len(csp.curr_domains[t[1]])))


def AC3(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    """[Figure 6.3]"""
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()
        revised, checks = revise(csp, Xi, Xj, removals, checks)
        if revised:
            if not csp.curr_domains[Xi]:
                return False, checks  # CSP is inconsistent
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
    return True, checks  # CSP is satisfiable


def revise(csp, Xi, Xj, removals, checks=0):
    """Return true if we remove a value."""
    revised = False
    for x in csp.curr_domains[Xi][:]:
        # If Xi=x conflicts with Xj=y for every possible y, eliminate Xi=x
        # if all(not csp.constraints(Xi, x, Xj, y) for y in csp.curr_domains[Xj]):
        conflict = True
        for y in csp.curr_domains[Xj]:
            if csp.constraints(Xi, x, Xj, y):
                conflict = False
            checks += 1
            if not conflict:
                break
        if conflict:
            csp.prune(Xi, x, removals)
            if len(csp.curr_domains[Xi]) == 0:          #if domain wipe out occurs for Xi
                csp.weights[(Xi, Xj)] += 1              #increment weight of constraint of Xi with Xj by 1
            revised = True
    return revised, checks

# Variable ordering

def first_unassigned_variable(assignment, csp):
    """The default variable order."""
    return first([var for var in csp.variables if var not in assignment])


def mrv(assignment, csp):
    """Minimum-remaining-values heuristic."""
    return argmin_random_tie([v for v in csp.variables if v not in assignment],
                             key=lambda var: num_legal_values(csp, var, assignment))


def num_legal_values(csp, var, assignment):
    if csp.curr_domains:
        return len(csp.curr_domains[var])
    else:
        return count(csp.nconflicts(var, val, assignment) == 0 for val in csp.domains[var])


def dom_wdeg(assignment, csp):
    minDom_WdegRatio = float('inf')
    best_var = -1
    for var in csp.variables:
        if var not in assignment:               #we need to pick a new uninstantiated value

            #dom value of var equals to size of its current domain
            if csp.curr_domains is None:
                dom = len(csp.domains[var])           
            else:
                dom = len(csp.curr_domains[var])
            
            wdeg = 0
            for n in csp.neighbors[var]:
                if n not in assignment:
                    wdeg += csp.weights[(var, n)]      #weight degree value of var equals to sum of weights of constraints of var with its uninstantiated neighbors

            #calculate dom / wdeg ratio
            if wdeg != 0:
                dom_wdegRatio = dom / wdeg
            else:
                dom_wdegRatio = dom         

            #find the minimum ratio of all variables
            if dom_wdegRatio < minDom_WdegRatio:
                minDom_WdegRatio = dom_wdegRatio
                best_var = var    

    return best_var


def maxConflicts(csp, conflicted, assignment):
    maxConfs = -float('inf')
    worse_var = -1

    for var in conflicted:
        numConfs = csp.nconflicts(var, assignment[var], assignment)
        if numConfs > maxConfs:
            maxConfs = numConfs
            worse_var = var

    return worse_var


# Value ordering


def unordered_domain_values(var, assignment, csp):
    """The default value order."""
    return csp.choices(var)


def lcv(var, assignment, csp):
    """Least-constraining-values heuristic."""
    return sorted(csp.choices(var), key=lambda val: csp.nconflicts(var, val, assignment))


# Inference


def no_inference(csp, var, value, assignment, removals):
    return True


def forward_checking(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    csp.support_pruning()
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
            if not csp.curr_domains[B]:            #if domain wipe out occurs for B
                csp.weights[(B, var)] += 1         #increment weight of constraint of B with var by 1
                return False
    return True

def FCforCBJ(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    csp.support_pruning()
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
            if not csp.curr_domains[B]:            #if domain wipe out occurs for B
                csp.weights[(B, var)] += 1         #increment weight of constraint of B with var by 1
                return False, B                    #return False and the variable B which is the variable with domain wipe out
    return True, None


def mac(csp, var, value, assignment, removals, constraint_propagation=AC3):
    """Maintain arc consistency."""
    return constraint_propagation(csp, {(X, var) for X in csp.neighbors[var]}, removals)


# The search, proper


def backtracking_search(csp, select_unassigned_variable=first_unassigned_variable,
                        order_domain_values=unordered_domain_values, inference=no_inference):
    """[Figure 6.5]"""

    def backtrack(assignment):
        if len(assignment) == len(csp.variables):
            return assignment
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    result = backtrack(assignment)
                    if result is not None:
                        return result
                csp.restore(removals)
            
        csp.unassign(var, assignment)
        return None

    result = backtrack({})
    assert result is None or csp.goal_test(result)
    return result

def backjumping_search(csp, select_unassigned_variable=first_unassigned_variable,
                        order_domain_values=unordered_domain_values, inference=no_inference):
    """[Figure 6.5]"""

    varSelectOrder = []                         #a list containing the variables in the order they are checked by the algorithm
    
    #add the variable 'a' to the correct position in the conflict set
    #of variable 'var' according to the order that the variables
    #are checked by the search algorithm
    def addToCS(CS, var, a):                                            
        if len(CS[var]) != 0:
            for x in CS[var]:
                if varSelectOrder.index(a) < varSelectOrder.index(x):
                    pos = CS[var].index(x)
                    CS[var].insert(pos, a)
                    return
                else:
                    continue
        
        CS[var].append(a)
    
    
    def backjump(assignment, CS, backjumpNeeded, backjumpVar):
        if len(assignment) == len(csp.variables):
            return assignment, backjumpNeeded, backjumpVar
        var = select_unassigned_variable(assignment, csp)
        if var not in CS:                                       #if variable has no conflict set
            CS[var] = []                                        #create it
        varSelectOrder.append(var)
        for value in order_domain_values(var, assignment, csp):
            csp.assign(var, value, assignment)
            removals = csp.suppose(var, value)
            check, confVar = inference(csp, var, value, assignment, removals) #call the inference function. Here: FC for CBJ. Returns false and the variable if domain wipe out occurs, if not it returns true and none
            if check:
                result, backjumpNeeded, backjumpVar = backjump(assignment, CS, backjumpNeeded, backjumpVar) #go to next variable
                if result is not None:                              #if everything went good return to previous variable
                    return result, backjumpNeeded, backjumpVar
                else: 
                        #print(var)  
                        #if we found a problem, check if we need to jump back to a certain variable
                    if backjumpNeeded:
                            #print(var)
                        if backjumpVar != var:              #if the current variable is not the variable where the jump must land
                            csp.restore(removals)           
                            break
                        else:
                            backjumpNeeded = False          #if it is the correct one then no more back jump is needed and we continue to next value of that variable
            else:
                for a in assignment:
                    for c in csp.domains[confVar]:                              #for every value of future conflicting variable
                        if not csp.constraints(a, assignment[a], confVar, c):   #if conflict with previously assigned variables is found
                            if a not in CS[var] and a != var:                   #add those variables in the right position of the conflict set of the variable we are currently checking
                                addToCS(CS, var, a)             
                                break

            #check if current value of current variable has conflicts with previously assigned variables
            #if there's conflict add those variables to the conflict set of current variable                        
            for a in assignment:
                if not csp.constraints(var, value, a, assignment[a]):
                    if a not in CS[var] and a != var:
                        addToCS(CS, var, a)
            csp.restore(removals)
        

        csp.unassign(var, assignment)
        varSelectOrder.remove(var)
        

        if not backjumpNeeded:
            backjumpNeeded = True
            #we must jump back to latest searched variable
            if len(CS[var]) != 0:
                backjumpVar = CS[var].pop(-1)        #pop out that variable from current variable's conflict set
            else:
                if len(varSelectOrder) != 0:
                    backjumpVar = varSelectOrder[-1]
                else:
                    return None, False, None               
            
            for v in CS[var]:                                   #for every variable in current variable's conflict set
                if v not in CS[backjumpVar]:                    #if it's not already in the conflict set of the variable we want to jump back
                    addToCS(CS, backjumpVar, v)                 #add it to the set so that we don't lose the info for conflicts
        
        CS[var].clear()                                         #empty current variable's conflict set
        return None, backjumpNeeded, backjumpVar

    result, backjumpNeeded, backjumpVar = backjump({}, {}, False, None)
    assert result is None or csp.goal_test(result)
    return result
# ______________________________________________________________________________
# Min-conflicts Hill Climbing search for CSPs


def min_conflicts(csp, max_steps=100000):
    """Solve a CSP by stochastic Hill Climbing on the number of conflicts."""
    # Generate a complete assignment for all variables (probably with conflicts)
    csp.current = current = {}
    for var in csp.variables:
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    # Now repeatedly choose a random conflicted variable and change it
    for i in range(max_steps):
        conflicted = csp.conflicted_vars(current)
        if not conflicted:
            return current
        var = random.choice(conflicted)
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    return None


def min_conflicts_value(csp, var, current):
    """Return the value that will give var the least number of conflicts.
    If there is a tie, choose at random."""
    return argmin_random_tie(csp.domains[var], key=lambda val: csp.nconflicts(var, val, current))


constraintchecks = 0

def runFiles(varName, domName, ctrName):
    varDomains = OpenVar(varName)                           #open var file and get the structs

    domains = OpenDom(domName, varDomains)                  #open dom file and get the structs

    neighbors, constr = OpenCtr(ctrName)                    #open ctr file and get the structs

    variables = []

    for i in varDomains:
        variables.append(i[0])

    global constraintchecks

    def constraints(A, a, B, b):                            #create the constraint function
        
        global constraintchecks
        constraintchecks += 1
        #for every pair of neighboring variables
        #read the sign of the constraint ('>', '=')
        #find the difference between the values of the
        #two variables and if the condition is true return True
        #else return False
        if (A, B) in constr:
            ctr = constr[(A, B)]

            sign = ctr[0]
            k = int(ctr[1])

            if sign == '>':
                if abs(a - b) > k:
                    return True
                else:
                    return False
            elif sign == '=':
                if abs(a - b) == k:
                    return True
                else:
                    return False
        elif (B, A) in constr:
            ctr = constr[(B, A)]

            sign = ctr[0]
            k = int(ctr[1])

            if sign == '>':
                if abs(a - b) > k:
                    return True
                else:
                    return False
            elif sign == '=':
                if abs(a - b) == k:
                    return True
                else:
                    return False

        return True

    measure = {}

    csp1 = CSP(variables, domains, neighbors, constraints)

    csp2 = CSP(variables, domains, neighbors, constraints)

    csp3 = CSP(variables, domains, neighbors, constraints)

    # csp4 = CSP(variables, domains, neighbors, constraints)

    start1 = time.time()

    result1 = backtracking_search(csp1, select_unassigned_variable=dom_wdeg, order_domain_values=lcv, inference=mac)

    end1 = time.time()

    print(varName, "mac , dom_wdeg", csp1.nassigns, constraintchecks)
    measure[('mac', 'dom_wdeg')] = end1 - start1
    constraintchecks = 0

    start2 = time.time()

    result2 = backtracking_search(csp2, select_unassigned_variable=dom_wdeg, order_domain_values=lcv, inference=forward_checking)

    end2 = time.time()

    print(varName, "fc , dom_wdeg", csp2.nassigns, constraintchecks)
    measure[('fc', 'dom_wdeg')] = end2 - start2
    constraintchecks = 0

    start3 = time.time()

    result3 = backjumping_search(csp3, select_unassigned_variable=dom_wdeg, order_domain_values=lcv, inference=FCforCBJ)

    end3 = time.time()

    print(varName, "fc-cbj , dom_wdeg", csp3.nassigns, constraintchecks)
    measure[('fc-cbj', 'dom_wdeg')] = end3 - start3
    constraintchecks = 0

    # start4 = time.time()

    # result4 = min_conflicts(csp4, 1000)

    # end4 = time.time()

    # measure['min_conflicts'] = end4 - start4



    def ResultOK(assignment, constraints):
        if assignment is None:
            return False

        for ctr in constraints:
            value1 = assignment[ctr[0]]
            value2 = assignment[ctr[1]]
            sign = constraints[ctr][0]
            k = int(constraints[ctr][1])
            if sign == '>':
                if abs(value1 - value2) <= k:
                    return False
            elif sign == '=':
                if abs(value1 - value2) != k:
                    return False

        return True


    return ResultOK(result1, constr), ResultOK(result2, constr), ResultOK(result3, constr), measure


