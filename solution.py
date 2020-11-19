#!/usr/bin/env python3

from frozendict import frozendict
import random
import time
import copy
import itertools

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


def strips(start_, goal_):
    goals_stack = []
    result = []
    current_state = copy.deepcopy(start_)
    goal = copy.deepcopy(goal_)
    goals_stack.append(goal)
    for one_goal in goal:
        if one_goal not in current_state:
            goals_stack.append(one_goal)

    while len(goals_stack) > 0:
        stack_top = goals_stack.pop()
        if isinstance(stack_top, str) and stack_top in PREDICATES.keys():
            if check_if_predicate_true_in_curent_state(stack_top, current_state):
                continue
            operator = choose_operator(goals_stack, result, stack_top, current_state)
            if operator is None:
                return []
            goals_stack.append(operator['name'])
            goals_stack.append(operator['pre'])
            continue
        if isinstance(stack_top, list):
            is_every_condition_met = True
            for pre in stack_top:
                if not check_if_predicate_true_in_curent_state(pre, current_state):
                    is_every_condition_met = False
                    break
            if not is_every_condition_met:
                goals_stack.append(stack_top)
                for pre in stack_top:
                    goals_stack.append(pre)
            continue

        if isinstance(stack_top, str) and stack_top in OPERATORS.keys():
            operator = OPERATORS[stack_top]
            do_operator_on_current_state(operator, current_state)
            result.append(operator['name'])
    return result

def strips_rek(start_, goal_, current_state_, goals_stack_, result_, first):
    start = copy.deepcopy(start_)
    goal = copy.deepcopy(goal_)

    if first:
        goals_stack = []
        current_state = copy.deepcopy(start_)
        goals_stack.append(goal)
        result = []

        for one_goal in goal:
            if one_goal not in current_state:
                goals_stack.append(one_goal)
    else:
        goals_stack = copy.deepcopy(goals_stack_)
        current_state = copy.deepcopy(current_state_)
        result = copy.deepcopy(result_)



    while len(goals_stack) > 0:
        stack_top = goals_stack.pop()
        if isinstance(stack_top, str) and stack_top in PREDICATES.keys():
            if check_if_predicate_true_in_curent_state(stack_top, current_state):
                continue
            operator = choose_operator_rek(goals_stack, result, stack_top, current_state)
            if len(operator) == 0:
                return []

            for op in operator:
                goals_stack_cp = copy.deepcopy(goals_stack)
                goals_stack_cp.append(op['name'])
                goals_stack_cp.append(op['pre'])
                rt = strips_rek(copy.deepcopy(start), copy.deepcopy(goal), current_state, goals_stack_cp, result, False)
                if len(rt) > 0:
                    return rt
            return []

        if isinstance(stack_top, list):
            is_every_condition_met = True
            for pre in stack_top:
                if not check_if_predicate_true_in_curent_state(pre, current_state):
                    is_every_condition_met = False
                    break
            if not is_every_condition_met:
                goals_stack.append(stack_top)
                for pre in stack_top:
                    goals_stack.append(pre)
            continue

        if isinstance(stack_top, str) and stack_top in OPERATORS.keys():
            operator = OPERATORS[stack_top]
            do_operator_on_current_state(operator, current_state)
            result.append(operator['name'])
    return result


def choose_operator(goals_stack, result, stack_top, current_state):
    candidates = []
    for operator in OPERATORS.values():
        if stack_top in operator['add'] and operator['name'] not in result and operator['name'] not in goals_stack:
            candidates.append(operator)

    # for candidate in candidates:
    #     for pre in candidate['pre']:
    #         for goal in goals_stack:
    #             if pre in goal:
    #                 candidates.remove(candidate)
    #
    # maximum = 0
    # operator = []
    # for op in candidates:
    #     count = 0
    #     for pre in op['pre']:
    #         if check_if_predicate_true_in_curent_state(pre, current_state):
    #             count += 1
    #     if count > maximum:
    #         maximum = count
    #         operator = [op]
    #     if count == maximum:
    #         operator.append(op)

    operator = candidates
    if len(operator) == 1:
        return operator[0]
    if len(operator) == 0:
        return None
    if len(operator) > 1:
        return operator[random.randint(0, len(operator)-1)]


def choose_operator_rek(goals_stack, result, stack_top, current_state):
    candidates = []
    for operator in OPERATORS.values():
        if stack_top in operator['add'] and operator['name'] not in result and operator['name'] not in goals_stack:
            candidates.append(operator)

    # for candidate in candidates:
    #     for pre in candidate['pre']:
    #         for goal in goals_stack:
    #             if pre in goal:
    #                 if candidate in candidates:
    #                     candidates.remove(candidate)

    # maximum = 0
    # operator = []
    # for op in candidates:
    #     count = 0
    #     for pre in op['pre']:
    #         if check_if_predicate_true_in_curent_state(pre, current_state):
    #             count += 1
    #     if count > maximum:
    #         maximum = count
    #         operator = [op]
    #     if count == maximum:
    #         operator.append(op)

    operator = candidates

    return operator


def do_operator_on_current_state(operator, current_state):
    for pre in operator['delete']:
        current_state.remove(pre)
    for add in operator['add']:
        current_state.append(add)


def check_if_predicate_true_in_curent_state(predicate,current_state):
    for axiom in AXIOMS.values():
        if axiom['name'] in current_state:
            continue
        is_state_from_axioms = False
        for conflict in axiom['conflict']:
            if conflict in current_state:
                is_state_from_axioms = True
                break
        if not is_state_from_axioms:
            current_state.add(axiom['name'])
    if predicate in current_state:
        return True
    return False

def compute_task(start,goal):
    print("Start:")
    print(start)
    print("Goal:")
    print(goal)

    print("Regression:")
    begin = time.perf_counter()
    result = regression(start, goal)
    end = time.perf_counter()
    print(result)
    print("Time: {0:02f}s".format(end - begin))
    print("Result length: " + str(len(result)))

    print("Strips rekurencja:")
    result = []
    s = list(start)
    g = list(goal)
    begin = time.perf_counter()

    result = strips_rek(s, g, [], [], [], True)
    end = time.perf_counter()
    print(result)
    print("Time: {0:02f}s".format(end - begin))
    print("Result length: " + str(len(result)))

    print("Strips losowe wybieranie operatora:")
    result = []
    s = list(start)
    g = list(goal)
    begin = time.perf_counter()
    result = []
    counter = 0
    while len(result) == 0 and counter < 200000:
        result = strips(s, g)
        counter += 1
    end = time.perf_counter()
    print(result)
    print("Time: {0:02f}s".format(end - begin))
    print("Result length: " + str(len(result)))

    print("Progressive:")
    begin = time.perf_counter()
    result = progressive(start, goal)
    end = time.perf_counter()
    print(result)
    print("Time: {0:02f}s".format(end - begin))
    print("Result length: " + str(len(result)))

BLOCKS = ['A', 'B', 'C']

VARIABLES = ['x', 'y']

AXIOMS = {**create_predicate('CLEAR(x)', conflict=['ON(y,x)']),
          **create_predicate('ARMEMPTY', conflict=['HOLDING(x)'])}

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

compute_task(start={'ON(C,B)', 'ON(B,A)', 'ONTABLE(A)', 'CLEAR(C)', 'ARMEMPTY'},
            goal={'ON(A,B)', 'ON(B,C)', 'ONTABLE(C)', 'CLEAR(A)', 'ARMEMPTY'})