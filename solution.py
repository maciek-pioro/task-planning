#!/usr/bin/env python3

from frozendict import frozendict


def create_operator(name, pre, delete, add):
    whole_text = name
    for i in pre + delete + add:
        whole_text += i
    variables = [c for c in VARIABLES if c in whole_text]
    results = []
    if len(variables) == 1:
        var = variables[0]
        for val in BLOCKS:
            result = dict()
            def replace(s): return s.replace(var, val)
            replaced_name = replace(name)
            possible_result = [
                r for r in results if r['name'] == replace(name)]
            if(len(possible_result) > 0):
                result = possible_result[0]
            else:
                result = dict()
                result['name'] = replaced_name
                result['pre'] = []
                result['delete'] = []
                result['add'] = []
                results += [result]
            for condition in pre:
                result['pre'] += [replace(condition)]
            for condition in delete:
                result['delete'] += [replace(condition)]
            for condition in add:
                result['add'] += [replace(condition)]
    elif len(variables) == 2:
        for val1 in BLOCKS:
            for val2 in BLOCKS:
                if val1 == val2:
                    continue
                def replace(s): return s.replace(
                    variables[0], val1).replace(variables[1], val2)
                replaced_name = replace(name)
                possible_result = [
                    r for r in results if r['name'] == replaced_name]
                if(len(possible_result) > 0):
                    result = possible_result[0]
                else:
                    result = dict()
                    result['name'] = replaced_name
                    result['pre'] = []
                    result['delete'] = []
                    result['add'] = []
                    results += [result]
                for condition in pre:
                    result['pre'] += [replace(condition)]
                for condition in delete:
                    result['delete'] += [replace(condition)]
                for condition in add:
                    result['add'] += [replace(condition)]
    return {result['name']: frozendict(result) for result in results}


def create_predicate(name, conflict):
    whole_text = name
    for i in conflict:
        whole_text += i
    variables = [c for c in VARIABLES if c in whole_text]
    results = []
    if len(variables) == 1:
        var = variables[0]
        for val in BLOCKS:
            def replace(s): return s.replace(var, val)
            replaced_name = replace(name)
            possible_result = [
                r for r in results if r['name'] == replace(name)]
            if(len(possible_result) > 0):
                result = possible_result[0]
            else:
                result = dict()
                result['name'] = replaced_name
                result['conflict'] = []
                results += [result]
            for condition in conflict:
                result['conflict'] += [replace(condition)]
    elif len(variables) == 2:
        for val1 in BLOCKS:
            for val2 in BLOCKS:
                if val1 == val2:
                    continue
                def replace(s): return s.replace(
                    variables[0], val1).replace(variables[1], val2)
                replaced_name = replace(name)
                possible_result = [
                    r for r in results if r['name'] == replaced_name]
                if(len(possible_result) > 0):
                    result = possible_result[0]
                else:
                    result = dict()
                    result['name'] = replaced_name
                    result['conflict'] = []
                    results += [result]
                for condition in conflict:
                    result['conflict'] += [replace(condition)]
    return {result['name']: frozendict(result) for result in results}


def get_names_of_predicates(state):
    return {predicate['name'] for predicate in state}

def progressive(start, goal, seen_states = None):

    if seen_states is None:
        seen_states = set()

    if str(start) in seen_states:
        return False

    seen_states.add(str(start))

    for predicate in goal:
        for conflict in PREDICATES[predicate]['conflict']:
            if conflict in goal:
                return False

    if (goal & start) == goal:
        return []

    admissible_operators = []
    for operator_name, operator in OPERATORS.items():
        pre = set(operator['pre'])
        if (pre & start) == pre:
            admissible_operators += [operator]

    #TODO: Heurystyka
    for operator in admissible_operators:
        result = progressive((start | set(operator['add'])) - set(operator['delete']), goal, seen_states)
        if result == False:
            continue
        else: 
            return [operator['name']] + result

    return False

def regression(start, goal, seen_states=None):
    if seen_states is None:
        seen_states = set()
    if str(goal) in seen_states:
        return False
    for predicate in goal:
        for conflict in PREDICATES[predicate]['conflict']:
            if conflict in goal:
                return False
    seen_states.add(str(goal))
    if start == goal:
        return []
    admissible_operators = []
    for operator_name, operator in OPERATORS.items():
        intersection = set(operator['add']) & goal
        if len(intersection) > 0:
            admissible_operators += [operator]
    #TODO: Heurystyka
    for operator in admissible_operators:
        result = regression(start, (goal | set(operator['pre']) | set(
            operator['delete'])) - set(operator['add']), seen_states)
        if result == False:
            continue
        else: 
            return  result + [operator['name']]
    return False

BLOCKS = ['A', 'B', 'C']

VARIABLES = ['x', 'y']

PREDICATES = {**create_predicate('ON(x,y)', conflict=['ONTABLE(x)', 'HOLDING(x)', 'HOLDING(y)']) ,
    **create_predicate('ONTABLE(x)', conflict=['ON(x,y)', 'HOLDING(x)']) ,
    **create_predicate('CLEAR(x)', conflict=['ON(y,x)']) ,
    **create_predicate('HOLDING(x)', conflict=['ON(x,y)', 'ON(y,x)', 'ONTABLE(x)']) ,
    **create_predicate('ARMEMPTY', conflict=['HOLDING(x)'])}

OPERATORS = {**create_operator('PICKUP(x)', pre=['CLEAR(x)', 'ONTABLE(x)', 'ARMEMPTY'], delete=['ONTABLE(x)', 'ARMEMPTY'], add=['HOLDING(x)']) ,
    **create_operator('PUTDOWN(x)', pre=['HOLDING(x)'], delete=['HOLDING(x)'], add=['ONTABLE(x)', 'ARMEMPTY']) ,
    **create_operator('STACK(x,y)', pre=['CLEAR(y)', 'HOLDING(x)'], delete=['CLEAR(y)', 'HOLDING(x)'], add=['ARMEMPTY', 'ON(x,y)']) ,
    **create_operator('UNSTACK(x,y)', pre=['ON(x,y)', 'CLEAR(x)', 'ARMEMPTY'], delete=[
                    'ON(x,y)', 'ARMEMPTY'], add=['HOLDING(x)', 'CLEAR(y)'])}

print("Regression")
result = regression(start={'ON(C,B)', 'ON(B,A)', 'ONTABLE(A)', 'CLEAR(C)', 'ARMEMPTY'}, 
                    goal={'ON(A,B)', 'ON(B,C)', 'ONTABLE(C)', 'CLEAR(A)', 'ARMEMPTY'})
print(result)

print("Progressive")
result2 = progressive(start={'ON(C,B)', 'ON(B,A)', 'ONTABLE(A)', 'CLEAR(C)', 'ARMEMPTY'}, 
                    goal={'ON(A,B)', 'ON(B,C)', 'ONTABLE(C)', 'CLEAR(A)', 'ARMEMPTY'})
print(result2)