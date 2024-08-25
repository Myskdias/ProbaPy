import math

from pgmpy.base import DAG
from pgmpy.models import BayesianNetwork
import daft
from pgmpy.factors.discrete.CPD import TabularCPD
from pgmpy.inference import VariableElimination
import random
from problog.program import PrologString
from problog.core import ProbLog
from problog import get_evaluatable
import re
import sys
import threading
from time import sleep
from sympy import *
from math import log10, floor
from pgmpy.base import DAG
import random
import z3 as z
import pycosat
from scipy.stats import binom
from abc import abstractmethod, ABCMeta
from pgmpy.factors.discrete import TabularCPD
from itertools import combinations
import numpy as np
import pandas as pd
import os

try:
    import thread
except ImportError:
    import _thread as thread


class EquationHalfTerm:

    def __init__(self, expr_a, expr_b=None, mode=0, neg_a=False, neg_b=False):
        self.expr_a = expr_a
        self.expr_b = expr_b
        self.mode = mode
        self.neg_a = False
        self.neg_b = False

    def is_basic(self):
        return self.mode == 0

    def is_and(self):
        return self.mode == 1

    def is_or(self):
        return self.mode == 2

    def get_variables(self):
        if self.expr_b is not None:
            return [self.expr_a, self.expr_b]
        else:
            return [self.expr_a]

    def replace_vars(self, replace_tab, expr):
        if self.mode == 0:
            if self.neg_a:
                replace_tab[self.expr_a] = simplify(Not(expr))
            else:
                replace_tab[self.expr_a] = expr
        elif self.mode == 1:
            expr_cnf = to_cnf(expr)
            expr_list = list(expr_cnf.args)
            arg0 = random.choice(expr_list)
            expr_list.remove(arg0)
            arg1 = And(*expr_list)
            if random.random() > 0.5:
                arg0, arg1 = arg1, arg0
            if self.neg_a:
                replace_tab[self.expr_a] = simplify(Not(arg0))
            else:
                replace_tab[self.expr_a] = arg0
            if self.neg_b:
                replace_tab[self.expr_b] = simplify(Not(arg1))
            else:
                replace_tab[self.expr_b] = arg1
        else:
            expr_dnf = to_dnf(expr)
            expr_list = list(expr_dnf.args)
            arg0 = random.choice(expr_list)
            expr_list.remove(arg0)
            arg1 = Or(*expr_list)
            if random.random() > 0.5:
                arg0, arg1 = arg1, arg0
            if self.neg_a:
                replace_tab[self.expr_a] = simplify(Not(arg0))
            else:
                replace_tab[self.expr_a] = arg0
            if self.neg_b:
                replace_tab[self.expr_b] = simplify(Not(arg1))
            else:
                replace_tab[self.expr_b] = arg1

    def gen_expr(self, replace_tab):
        if self.mode == 0:
            if self.neg_a:
                return simplify(Not(replace_tab[self.expr_a]))
            return replace_tab[self.expr_a]
        else:
            a = replace_tab[self.expr_a]
            if self.neg_a:
                a = simplify(Not(a))
            b = replace_tab[self.expr_b]
            if self.neg_b:
                b = simplify(Not(b))
            if self.mode == 1:
                return And(a, b)
            else:
                return Or(a, b)

    def __str__(self):
        return f'expr_a: {'-' if self.neg_a else ''}{self.expr_a}, expr_b: {'-' if self.neg_b else ''}{self.expr_b}, mode: {self.mode}'


class EquationTerm:

    def __init__(self, eht_a, eht_b=None):
        self.eht_a = eht_a
        self.eht_b = eht_b

    def is_conditional(self):
        return self.eht_b is not None

    def get_mod_a(self):
        return self.eht_a.mode

    def get_mod_b(self):
        return self.eht_b.mode

    def get_variables(self):
        if self.eht_b is None:
            return self.eht_a.get_variables()
        return self.eht_a.get_variables() + self.eht_b.get_variables()

    def gen_finders(self, replace_tab):
        expr_a = self.eht_a.gen_expr(replace_tab)
        if self.is_conditional():
            expr_b = self.eht_b.gen_expr(replace_tab)
            return [EquationFinder(expr_a, expr_b)]
        return [EquationFinder(expr_a)]

    def __str__(self):
        return f'[{str(self.eht_a)} {', '+str(self.eht_b) if self.is_conditional() else ''}]'


class Equation:

    def __init__(self, *equation_terms):
        self.equation_tab = [[[] for j in range(4)] for i in range(3)]
        self.variables = []
        for et in equation_terms:
            self.__iadd__(et)

    def __add_variable(self, *vars):
        for v in vars:
            if v not in self.variables:
                self.variables += [v]

    def __iadd__(self, equation_term):
        self.__add_variable(equation_term.get_variables())
        if equation_term.is_conditional():
            self.equation_tab[equation_term.get_mod_a()][equation_term.get_mod_b()] += [equation_term]
        else:
            self.equation_tab[equation_term.get_mod_a()][3] += [equation_term]
        return self

    def get_term(self, equation_finder):
        for index_a in equation_finder.possible_index_a:
            for index_b in equation_finder.possible_index_b:
                if len(self.equation_tab[index_a][index_b]) != 0:
                    return random.choice(self.equation_tab[index_a][index_b])
        return None

    def get_variables(self):
        return self.variables

    def gen_finders(self, replace_tab, a):
        finders = []
        for e_i in self.equation_tab:
            for e_j in e_i:
                for equation_term in e_j:
                    if equation_term != a:
                        tabi = equation_term.gen_finders(replace_tab)
                        if len(tabi) == 0:
                            print("errrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrooooooooooooooooooooooooorrrrrr")
                        finders += equation_term.gen_finders(replace_tab)
        return finders

    def __str__(self):
        return self.equation_tab


def to_eng(expr):
    s = ""
    if isinstance(expr, Or):
        s += " or ".join([to_eng(a) for a in expr.args])
    elif isinstance(expr, And):
        s += " and ".join([to_eng(a) for a in expr.args])
    elif isinstance(expr, Symbol):
        key = str(expr)
        if key in alphabet_conversion:
            s += lf[alphabet_conversion[str(expr)]]
        else:
            print('error ' + key + ' is not in the dico')
            s += key
    elif isinstance(expr, Not):
            s += f'not {to_eng(expr.args[0])}'
    else:
        print('unexpected ' + str(type(expr)))

    return s


class EquationFinder:

    def __str__(self):
        return f'{str(self.expr_a)}{'; '+str(self.expr_b) if self.expr_b is not None else ''}'

    def __repr__(self):
        return self.__str__()

    def __init__(self, expr_a, expr_b=None):
        self.expr_a = expr_a
        self.expr_b = expr_b

        expr_a_cnf = to_cnf(self.expr_a)
        expr_a_dnf = to_dnf(self.expr_a)

        self.possible_index_a = [0]

        if isinstance(expr_a_cnf, And):
            self.possible_index_a += [1]

        if isinstance(expr_a_dnf, Or):
            self.possible_index_a += [2]

        self.possible_index_b = []
        if expr_b is not None:
            expr_b_cnf = to_cnf(self.expr_b)
            expr_b_dnf = to_dnf(self.expr_b)
            self.possible_index_b = [0]

            if isinstance(expr_b_cnf, And):
                self.possible_index_b += [1]

            if isinstance(expr_b_dnf, Or):
                self.possible_index_b += [2]

        else:
            self.possible_index_b += [3]

    def shuffle(self):
        random.shuffle(self.possible_index_a)
        random.shuffle(self.possible_index_b)

    def replace_vars(self, replace_tab, a):
        a.eht_a.replace_vars(replace_tab, self.expr_a)
        if a.is_conditional():
            a.eht_b.replace_vars(replace_tab, self.expr_b)

    def to_eng(self, infer):
        if self.expr_b is not None:
            return (f'If someone is {to_eng(self.expr_b)}, then the probability that they are {to_eng(self.expr_a)} is '
                    f'{find_proba(self.expr_a, infer, self.expr_b)}')
        return f'There is a probability of {find_proba(self.expr_a, infer)} that Neimad is {to_eng(self.expr_a)} today.'


E = EquationHalfTerm
ET = EquationTerm


#il faut faire une table de correspondance


def cdquit(fn_name):
    # print to stderr, unbuffered in Python 2.
    print('{0} took too long'.format(fn_name), file=sys.stderr)
    sys.stderr.flush() # Python 3 stderr is likely buffered.
    thread.interrupt_main() # raises KeyboardInterrupt

def exit_after(s):
    '''
    use as decorator to exit process if
    function takes longer than s seconds
    '''
    def outer(fn):
        def inner(*args, **kwargs):
            timer = threading.Timer(s, cdquit, args=[fn.__name__])
            timer.start()
            try:
                result = fn(*args, **kwargs)
            finally:
                timer.cancel()
            return result
        return inner
    return outer


#l1 = ['blue', 'red', 'white', 'green', 'black', 'orange']
l1 = ['blue', 'red', 'white']
l2 = ['happy', 'sad', 'angry']
l3 = ['wearing_glasses', 'wearing_shoes', 'wearing_a_shirt']

#lf = l1 + l2 + l3 + ['wearing_color', 'emotional', 'wearing_cloth']

#lf = l1 + ['wearing_color', 'emotional', 'wearing_cloth']
lf = l1 + ['wearing_color']

#dic = {'wearing_color': l1, 'emotional': l2, 'wearing_cloth': l3}
dic = {'wearing_color': l1}

alphabet_bis = ['A', 'B', 'C', 'D', 'F', 'G', 'H', 'J', 'K', 'L', 'M', 'o', 'q', 'r', 's', 't', 'u', 'V', 'W', 'X', 'Y', 'Z']
alphabet = [f'x_{i}' for i in range(len(lf))]
alphabet_conversion = {}

for i in range(len(alphabet)):
    alphabet_conversion[alphabet[i]] = i


def convert_from_s_to_e(e):
    return lf[alphabet_conversion[e]]


length = 0
for (a,b) in dic.items():
    length += len(b)



def get_value(cpd, dic):

    for variable in dic.keys():
        if variable not in cpd.variables:
            raise ValueError(f"Factor doesn't have the variable: {variable}")

    index = []
    for var in cpd.variables:
        if var not in dic.keys():
            raise ValueError(f"Variable: {var} not found in arguments")
        else:
            try:
                index.append(cpd.name_to_no[var][dic[var]])
            except KeyError:
                index.append(dic[var])
    return cpd.values[tuple(index)]


# transcribe in problog
def gen_problog(model):
    result = []
    result_eng = []
    result_exp = []
    for node in model:
        cpd = model.get_cpds(node)
        v = cpd.variable

        el = cpd.get_evidence()
        factor = cpd.to_factor()
        size = 2**len(el)
        le = len(el)
        result += '\n'
        if size == 1:
            pass
            result += [f"{get_value(cpd, {v:True})}::{lf[v]}.\n"]

            if random.random() > 0.5:
                result_exp += [EquationFinder(parse_expr(alphabet[v]))]
                result_eng += [f"There is a probability of {get_value(cpd, {v:True})} that Neimad is  {lf[v]} today.\n"]
            else:
                result_exp += [EquationFinder(simplify(Not(parse_expr(alphabet[v]))))]
                result_eng += [f"There is a probability of {get_value(cpd, {v:False})} that Neimad is not {lf[v]} today.\n"]
            #result += fr"{get_value(cpd, {v:False})}:: \+{lf[v]}"+'\n'
        else:
            for i in range(size):
                l = []
                expr_list = []
                d = {v: True}
                for j in range(le-1, -1, -1):
                    prefix = (i // (2**j)) % 2
                    if prefix == 0:
                        l += [r'\+' + f"{lf[el[le - j - 1]]}"]
                        expr_list += [Not(parse_expr(alphabet[el[le - j - 1]]))]
                        d[el[le - j - 1]] = False
                    else:
                        l += [f"{lf[el[le - j - 1]]}"]
                        expr_list += [parse_expr(alphabet[el[le - j - 1]])]
                        d[el[le - j - 1]] = True

                result += [f"{get_value(cpd, d)}:: {lf[v]} :- " + ", ".join(l)+".\n"]
                if random.random() > 0.5:
                    result_eng += ["If someone is " + ' and '.join([lf[el[k]] if d[el[k]] else 'not ' + lf[el[k]] for k in range(le)])
                             + ', then the probability that they are ' + lf[v] + f' is {get_value(cpd, d)}.\n']

                    result_exp += [EquationFinder(parse_expr(f'{alphabet[v]}'), simplify(And(*expr_list)))]
                else:
                    d[v] = False
                    result_eng += ["If someone is " + ' and '.join([lf[el[k]] if d[el[k]] else 'not ' + lf[el[k]] for k in range(le)])
                                   + ', then the probability that they are not ' + lf[v] + f' is {get_value(cpd, d)}.\n']
                    result_exp += [EquationFinder(simplify(Not(parse_expr(f'{alphabet[v]}'))), simplify(And(*expr_list)))]

    return result, result_eng, result_exp


def gen_question(model, n, i):
    if n == i:
        return f"evidence({lf[n]}, true).\nquery({lf[i]}).", f'What is the probability that Neimad is {lf[i]} ?'
    return f"evidence({lf[n]}, true).\nquery({lf[i]}).", f'What is the probability that Neimad is {lf[i]} given he is {lf[n]} ?'


@exit_after(3)
def ask_problog(s):
    p = PrologString(s)
    return get_evaluatable().create_from(p).evaluate()


def to_input(result, question):
    return ''.join(result) + question


def hypothesis_elimination(result, question, answer, depth):
    #r_index = random.randint(len(result))
    #result.remove(r_index)
    if(depth > 2):
        return 0, None
    input = to_input(result, question)
    print(depth)
    try:
        problog_answer = ask_problog(input)
        print(list(problog_answer.values())[0])
        if round(list(problog_answer.values())[0], 6) != answer:
            return 0, None
    except KeyboardInterrupt:
        return 0, None
    except:
        return 0, None
    maxi = 0
    r = None
    for i in range(len(result)):
        n_result = result.copy()
        del n_result[i]
        print(f"len:{len(n_result)}")
        v = hypothesis_elimination(n_result, question, answer, depth + 1)
        if maxi < v[0] + 1:
            maxi = v[0] + 1
            if v[0] == 0:
                r = n_result
            else:
                r = v[1]


    return maxi, r


def eat_sympy(expr, atoms):

    atoms_dict = {}
    for i in range(len(atoms)):
        atoms_dict[atoms[i]] = i

    expr = to_cnf(expr, simplify=True)

    def convert(child):
        if isinstance(child, Not):
            return -(int(atoms_dict[child.args[0]])+1)
        return int(atoms_dict[child]) + 1

    def parse(e):
        if isinstance(e, Or):
            return [convert(sub_child) for sub_child in e.args]
        return [convert(e)]

    if isinstance(expr, And):
        return [parse(child) for child in expr.args]
    return [parse(expr)]


def find_all_valuation(cl_list):
    solutions = []
    for solution in pycosat.itersolve(cl_list):
        solutions.append(solution)
    return solutions


#Il manque les sachant que
def find_proba(expr, inf, obs=None):
    atoms = list(expr.atoms())
    tab = eat_sympy(expr, atoms)
    valuations = find_all_valuation(tab)
    variables = [alphabet_conversion[str(a)] for a in atoms]
    proba = 0
    if obs is not None:
        obs = to_cnf(obs, simplify=True)
        if not obs:
            return 0
    if obs is None or obs:
        phi_query = inf.query(variables)
        for valuation in valuations:
            b_values = [1 if j > 0 else 0 for j in valuation]
            r = phi_query.values[tuple(b_values)]

            proba += r

        return proba
    ats = list(obs.atoms())

    sol_list = find_all_valuation(eat_sympy(obs, ats))
    obs_query = inf.query([alphabet_conversion[str(a)] for a in ats])
    for sol in sol_list:

        observations = {}
        for i in sol:
            if i > 0:
                try:
                    observations[alphabet_conversion[str(ats[i-1])]] = True
                except:
                    print('eeeeeeeeeeerrrrrrrrrrrrrrrrrorrrrrrrrrrr')
                    print(str(ats[i-1]))
                    pass

            else:
                observations[alphabet_conversion[str(ats[abs(i) -1])]] = False
        phi_query = inf.query(variables, observations)
        #print(variables)
        #print(observations)
        #print(phi_query)
        for valuation in valuations:
            b_values = [1 if j > 0 else 0 for j in valuation]
            p = phi_query.values[tuple(b_values)]*obs_query.values[tuple([1 if j > 0 else 0 for j in sol])]
            #print(p)
            proba += p

    if proba > 1:

        raise Exception(f'proba > 1: {proba}: \nexpr:{str(expr)}\nobs:{str(obs)}\ntab:{tab}\nvaluation{valuations}\nsol_list{sol_list}\nats{str(ats)}')
    return proba


# we define a proba object by three things (a, b) or just (a)
# a and b are boolean expressions
# if we have just (a) then (a) means P(A)
# if we have (a, b) this means P(A | B)
# [(a, b), (b, a), (a,), (b,)]
# [(1, 2), (2, 1), (1,) (2,)]
# [(12,), (112,), (1,), (2,)]
# l = [
#  [
#    [(1,), (2,)], [(12,], [(112,)], [normal give ]
#i htink it s a better idea to do a matrix de taille 3x4 un quatriemme collone pour les cas ou y a pas de sachnat que
#All the relation that I have # normale et ou
l = [
    [[[(1,), (2,)], [], []],
     [[[(12,)], [], []],],
     [[[(112,)], [], []],],
     ]
]


eq = Equation(ET(E(0)), ET(E(1)), ET(E(0, 1, 1)), ET(E(0, 1, 0)))
eq1 = Equation(ET(E(0), E(1)), ET(E(1), E(0)), ET(E(0)), ET(E(1)))

equation_list = [

    eq, eq1

]


def gen_do(graph, n, i):
    nl = list(graph.nodes())
    node = random.choice(nl)
    while node == i or node == n:
        node = random.choice(nl)
    g2 = graph.do(node)
    action = lf[node]
    #Remplacer par an external factor
    s = f'Let\'s suppose that Neimad\'s boss forced him to be {action}'
    return s, g2


def fae(equation_finder):
    random.shuffle(equation_list)
    for equation in equation_list:
        a = equation.get_term(equation_finder)
        if a is not None:
            return a, equation

    return None, None


def replace(result_finder, tracker):
    equation_finder = random.choice(result_finder)
    result_finder.remove(equation_finder)
    equation_finder.shuffle()
    a, equation = fae(equation_finder)
    if a is None:
        print("errrrrrrrrrrrrror")
        #this should not happen
        return 0

    #we need to replace the variables
    replace_tab = [0]*len(equation.get_variables())
    equation_finder.replace_vars(replace_tab, a)
    #we need to replace the other variables that do not appear in a
    #lf copy
    alphabet_copy = alphabet.copy()

    for i in range(len(replace_tab)):
        while replace_tab[i] == 0:
            letter = random.choice(alphabet_copy)
            alphabet_copy.remove(letter)
            ex = parse_expr(letter)
            if ex not in replace_tab:
                replace_tab[i] = ex


    zrzrzz = equation.gen_finders(replace_tab, a)
    """
    print(len(zrzrzz))
    print("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz")"""
    result_finder += equation.gen_finders(replace_tab, a)
    tracker.add_equation(a, equation, replace_tab)
    return result_finder


def from_finder(result_finder, infer):
    l_eng = []
    for equation_finder in result_finder:
        l_eng += [equation_finder.to_eng(infer)]
    return l_eng


def generate_random_sat_formula(num_vars, num_clauses):
    """Generate a random SAT formula."""
    formula = []
    for _ in range(num_clauses):
        clause = []
        for _ in range(random.randint(1, 3)):  # Random clause length between 1 and 3
            var = random.randint(1, num_vars)
            sign = random.choice([-1, 1])
            clause.append(sign * var)
        formula.append(clause)
    return formula


def select_vars(li, number):
    li_copy = li.copy()
    result = [0]*number
    for i in range(number):
        element = random.choice(li_copy)
        li_copy.remove(element)
        result[i] = element
    return result


def eat_pycosat(variables, cl_list):
    return And(*[eat_pycosat_clause(variables, cl) for cl in cl_list])


def eat_pycosat_clause(variables, cl):
    return Or(*[parse_expr(variables[i-1]) if i > 0 else Not(parse_expr(variables[-i-1])) for i in cl])


class EquationsTracker:

    def __init__(self):
        self.equations = []

    def add_equation(self, a, equation, replace_tab):
        self.equations.append((a, equation, replace_tab))

    def __str__(self):
        return ""


class Event(metaclass=ABCMeta):

    def __init__(self, number):
        self.number = number
        self.involved = self.get_a_number()

    @abstractmethod
    def get_a_number(self):
        raise NotImplementedError

    @abstractmethod
    def calc_proba(self, proba):
        raise NotImplementedError


class Exactly(Event):

    def __init__(self, number):
        super().__init__(number)

    def get_a_number(self):
        return random.randint(0, self.number)

    def calc_proba(self, proba):
        return (proba**self.involved)*(1-proba)**(self.number-self.involved)*math.comb(self.involved, self.number)

    def __str__(self):
        return 'exactly'

    def __repr__(self):
        return self.__str__()


class MoreThan(Event):

    def __init__(self, number):
        super().__init__(number)

    def get_a_number(self):
        return random.randint(0, self.number)

    def calc_proba(self, proba):
        aa = sum(binom.pmf(i, self.number, proba) for i in range(self.involved, self.number+1))
        if math.isnan(aa):
            print(f"proba:{proba}, number:{self.number}, involved:{self.involved}")
        return aa

    def __str__(self):
        return 'more than'

    def __repr__(self):
        return self.__str__()


class LessThan(Event):

    def __init__(self, number):
        super().__init__(number)

    def get_a_number(self):
        return random.randint(0, self.number)

    def calc_proba(self, proba):
        aa = 1 - sum(binom.pmf(i, self.number, 1-proba) for i in range(self.number - self.involved, self.number+1))
        if math.isnan(aa):
            print(f"proba:{proba}, number:{self.number}, involved:{self.involved}")

        return aa

    def __str__(self):
        return 'less than'

    def __repr__(self):
        return self.__str__()


def gen_event_str(event, expr_group):
    return f"We consider {event.number} {'people' if event.number > 1 else 'person'} at Neimad's work that {'are' if event.number > 1 else 'is'} {from_sympy_to_english(expr_group)}."


def gen_question_event(n, i, event):
    if n == i:
        return f'What is the probability that {str(event)} {event.involved} {'people are' if event.involved > 1 else 'person is'} {lf[i]} ?'
    return f'What is the probability that {str(event)} {event.involved} {'people are' if event.involved > 1 else 'person is'} {lf[i]} given {'they are' if event.number > 1 else 'he is'} {lf[n]} ?'


def gen_sub_group(vars, clauses, googl):
    formula = generate_random_sat_formula(vars, clauses)
    while type(pycosat.solve(formula)) == str:
        formula = generate_random_sat_formula(vars, clauses)

    variables = select_vars(googl, vars)
    expr = eat_pycosat(variables, formula)

    return expr


def gen_event(vars_number, clauses_number, googl):
    i = random.randint(1, 5) #number of person
    expr_grp = gen_sub_group(vars_number, clauses_number, googl)
    #event_list = ['less than', 'more than', 'exactly', 'at least', 'at most']
    event_list = [MoreThan(i), LessThan(i)]
    event = random.choice(event_list)
    return event, expr_grp


def calc_proba(graph, expr_group, fact, observations=None):
    """print("expr_grp")
    print(expr_group)
    print("expr_grp")
    print(expr_group)
    print("obs")
    print(observations)"""

    if observations is None:
        observations = simplify(expr_group)
    else:
        observations = simplify(And(expr_group, observations))
    observations = remove_common_literals(fact, observations)
    return find_proba(fact, VariableElimination(graph), simplify(observations))


def remove_common_literals(observations, exp_grp):
    exp_grp = simplify(exp_grp)
    atoms_obs = list(observations.atoms())
    atoms_grp = list(exp_grp.atoms())
    to_remove_list = []
    for atom in atoms_grp:
        if atom in atoms_obs:
            to_remove_list += [atom]
    #print(to_remove_list)
    exp_cnf = to_cnf(exp_grp)

    def value(lite):
        if isinstance(lite,Not):
            return list(lite.args)[0]
        return lite
    cl_list = []
    ite = [exp_cnf]
    if isinstance(exp_cnf, And):
        ite = exp_cnf.args
    for exp_child in ite:
        kept = []
        if isinstance(exp_child, Or):
            for lit in exp_child.args:
                if value(lit) not in to_remove_list:
                    kept += [lit]
        else:
            if value(exp_child) not in to_remove_list:
                kept = [exp_child]

        if len(kept) == 1:
            cl_list += kept
        elif len(kept) > 1:
            cl_list += [Or(*kept)]
    if len(cl_list) == 1:
        return cl_list[0]
    elif len(cl_list) > 1:
        return And(*cl_list)
    return True


def from_sympy_to_english(expression):
    # Helper function to convert SymPy expression to English string
    def expr_to_english(expr):
        if isinstance(expr, Symbol):
            # If the expression is an atom (variable or constant), convert it using the dictionary
            return convert_from_s_to_e(str(expr))
        elif isinstance(expr, Not):
            # If the expression is a Not operation, convert it accordingly
            return f"not {expr_to_english(expr.args[0])}"
        elif isinstance(expr, And):
            # If the expression is an And operation, convert it accordingly
            return ' and '.join(expr_to_english(ar) for ar in expr.args)
        elif isinstance(expr, Or):
            # If the expression is an Or operation, convert it accordingly
            return ' or '.join(expr_to_english(ar) for ar in expr.args)
        else:
            # If the expression is not recognized, return it as a string
            return str(expr)

    # Convert the entire expression to English
    return expr_to_english(expression)


def add_arc_preserve_acyclic(bn):
    nodes = list(bn.nodes())
    for A, B in combinations(nodes, 2):
        if not bn.has_edge(A, B) and not bn.has_edge(B, A):
            try:
                bn.add_edge(A, B)
                update_cpd(bn, B)
                #update_cpd_random(bn, B)
                return A, B
            finally:
                pass
    return None


def update_cpd(graph, node):
    cpd = graph.get_cpds(node)
    old_values = cpd.values
    resu = []
    rand = random.random()
    for idx, x in np.ndenumerate(old_values):
        resu += [rand*x, x - rand*x]
    res_array = np.array(resu).reshape((2, len(resu)//2))
    evidence_copy = cpd.get_evidence()
    evidence_copy.append('ne')
    new_cpd = TabularCPD(variable=node, variable_card=2, values=res_array,evidence=evidence_copy, evidence_card=[2]*(len(cpd.get_evidence())+1))
    return new_cpd


def round_all_cpds(model, decimals=2):
    for cpd in model.get_cpds():
        rounded_values = np.round(cpd.values, decimals)
        cpd.values = rounded_values


def run():
    try:
        G = BayesianNetwork.get_random(n_nodes=length, n_states=2)

        G.add_node(length)
        #G.add_node(length+1)
        #G.add_node(length+2)
        G.add_edges_from([(length, i) for i in range(len(l1))])
        #G.add_edges_from([(length+1, i) for i in range(len(l1), len(l1) + len(l2))])
        #G.add_edges_from([(length+2, i) for i in range(len(l1) + len(l2), length)])

        G.get_random_cpds(n_states=2, inplace=True)
        #round_all_cpds(G)
        i = random.randint(0, length - 1)

        H = G.get_ancestral_graph(i)
        print(type(H))

        ns = list(H.nodes())
        n = random.choice(ns)
        print(length)
        print(str(n) + '->' + str(i))
        infer = VariableElimination(G)
        # on fait juste pas de proba conditionnelles si i == n
        """
        if not i == n:
            print(infer.query(variables=[i], evidence={n: 0})) #my question
        else:
            print(infer.query(variables=[i]))
        """
        K = H.do(n, inplace=False)
        #ce qui m'interesse c'est pas K mais G
        #print(type(Hp))
        # mieux
        #K = BayesianNetwork(Hp.edges())
        K.get_random_cpds(n_states=2, inplace=True)

        infer2 = VariableElimination(K)
        """
        if i == n:
            print(infer2.query(variables=[i]))
        else:
            print(infer2.query(variables=[i], evidence={n: 0}))
        
        """


        r, r_eng, r_exp = gen_problog(G)
        qu, qu_eng = gen_question(G, n, i)
        s = ''.join(r) + qu
        s_eng = ''.join(r_eng) + qu_eng

        problog_answer = ask_problog(s)
        """
        print(list(problog_answer.values())[0])
        print(s)
        print(s_eng)
        print(r_exp)
        print(len(r_exp))
        """
        copy_exp = r_exp.copy()
        equations_tracker = EquationsTracker()
        replace(copy_exp, equations_tracker)
        #print(copy_exp)
        #print(len(copy_exp))

        #ex1 = parse_expr('x_1')
        #ex2 = parse_expr('x_2')
        #print(G.nodes)
        #t = find_proba(ex1, VariableElimination(G), ex2)
        #print(t)
        G_do = G.copy()
        act, gr = gen_do(G_do, n, i)
        facts = parse_expr(alphabet[i])
        obs = parse_expr(alphabet[n])
        resu = None
        resu_do = None
        if n == i:
            resu = find_proba(facts, VariableElimination(G))
            resu_do = find_proba(facts, VariableElimination(G_do))
        else:
            resu = find_proba(facts, VariableElimination(G), obs)
            resu_do = find_proba(facts, VariableElimination(G_do), obs)


        evt, expr_grp = gen_event(3, 2, alphabet)
        #print(evt)
        proba_sub_group = None
        if n == i:
            proba_sub_group = calc_proba(G, expr_grp, facts)
        else:
            proba_sub_group = calc_proba(G, expr_grp, facts, obs)

        #print(expr_grp)
        #print(from_sympy_to_english(expr_grp))
        #j_final, r_final = hypothesis_elimination(r, gen_question(K, n, i), round(list(problog_answer.values())[0],6), 0)
        #print(s)


        #print(j_final)
        #print(''.join(r_final) + gen_question(K, n, i))

        #### Print propre

        print(''.join(r))
        print(qu)


        print('#################[Problème simple]#################')
        st1 = ""
        premises = '\n'.join(from_finder(copy_exp, VariableElimination(G)))
        st1 += premises
        print(premises)

        print(qu_eng)
        print(f'Answer: {resu}')

        print()

        print('###################[Problème do]###################')
        st2 = ''
        premises2 = '\n'.join(from_finder(copy_exp, VariableElimination(G)))
        print(premises2)
        st2 += premises2
        st2 += '\n'
        st2 += act
        print(act)
        print(qu_eng)
        print(f'Answer: {resu_do}')

        print()

        print('############[Problème avec sous-groupe]############')
        st3 = ''
        premises3 = '\n'.join(from_finder(copy_exp, VariableElimination(G)))
        st3 += premises3
        st3 += '\n'

        print('\n'.join(from_finder(copy_exp, VariableElimination(G))))
        event_str = gen_event_str(evt, expr_grp)
        st3 += event_str
        print(event_str)
        event_qu = gen_question_event(n, i, evt)
        print(st3)
        print(event_qu)
        print(f"Answer: {evt.calc_proba(proba_sub_group)}")
        G_copy = G.copy()
        add_arc_preserve_acyclic(G_copy)
        return st1 + "\n" + qu_eng, resu, st2 + "\n" + qu_eng, resu_do, st3 + "\n" + event_qu, evt.calc_proba(proba_sub_group)
    except:
        return None


def run2():
    G = BayesianNetwork.get_random(n_nodes=length, n_states=2)

    G.add_node(length)
    #G.add_node(length+1)
    #G.add_node(length+2)
    G.add_edges_from([(length, i) for i in range(len(l1))])
    #G.add_edges_from([(length+1, i) for i in range(len(l1), len(l1) + len(l2))])
    #G.add_edges_from([(length+2, i) for i in range(len(l1) + len(l2), length)])

    G.get_random_cpds(n_states=2, inplace=True)
    #round_all_cpds(G)
    i = random.randint(0, length - 1)

    H = G.get_ancestral_graph(i)
    print(type(H))

    ns = list(H.nodes())
    n = random.choice(ns)
    print(length)
    print(str(n) + '->' + str(i))
    infer = VariableElimination(G)
    # on fait juste pas de proba conditionnelles si i == n
    """
    if not i == n:
        print(infer.query(variables=[i], evidence={n: 0})) #my question
    else:
        print(infer.query(variables=[i]))
    """
    K = H.do(n, inplace=False)
    #ce qui m'interesse c'est pas K mais G
    #print(type(Hp))
    # mieux
    #K = BayesianNetwork(Hp.edges())
    K.get_random_cpds(n_states=2, inplace=True)

    infer2 = VariableElimination(K)
    """
    if i == n:
        print(infer2.query(variables=[i]))
    else:
        print(infer2.query(variables=[i], evidence={n: 0}))
    
    """


    r, r_eng, r_exp = gen_problog(G)
    qu, qu_eng = gen_question(G, n, i)
    s = ''.join(r) + qu
    s_eng = ''.join(r_eng) + qu_eng

    problog_answer = ask_problog(s)
    """
    print(list(problog_answer.values())[0])
    print(s)
    print(s_eng)
    print(r_exp)
    print(len(r_exp))
    """
    copy_exp = r_exp.copy()
    equations_tracker = EquationsTracker()
    replace(copy_exp, equations_tracker)
    #print(copy_exp)
    #print(len(copy_exp))

    #ex1 = parse_expr('x_1')
    #ex2 = parse_expr('x_2')
    #print(G.nodes)
    #t = find_proba(ex1, VariableElimination(G), ex2)
    #print(t)
    G_do = G.copy()
    act, gr = gen_do(G_do, n, i)
    facts = parse_expr(alphabet[i])
    obs = parse_expr(alphabet[n])
    resu = None
    resu_do = None
    if n == i:
        resu = find_proba(facts, VariableElimination(G))
        resu_do = find_proba(facts, VariableElimination(G_do))
    else:
        resu = find_proba(facts, VariableElimination(G), obs)
        resu_do = find_proba(facts, VariableElimination(G_do), obs)


    evt, expr_grp = gen_event(3, 2, alphabet)
    print(evt)
    proba_sub_group = None
    if n == i:
        proba_sub_group = calc_proba(G, expr_grp, facts)
    else:
        proba_sub_group = calc_proba(G, expr_grp, facts, obs)

    #print(expr_grp)
    #print(from_sympy_to_english(expr_grp))
    #j_final, r_final = hypothesis_elimination(r, gen_question(K, n, i), round(list(problog_answer.values())[0],6), 0)
    #print(s)


    #print(j_final)
    #print(''.join(r_final) + gen_question(K, n, i))

    #### Print propre

    print(''.join(r))
    print(qu)


    print('#################[Problème simple]#################')
    st1 = ""
    premises = '\n'.join(from_finder(copy_exp, VariableElimination(G)))
    st1 += premises
    print(premises)

    print(qu_eng)
    print(f'Answer: {resu}')

    print()

    print('###################[Problème do]###################')
    st2 = ''
    premises2 = '\n'.join(from_finder(copy_exp, VariableElimination(G)))
    print(premises2)
    st2 += premises2
    st2 += '\n'
    st2 += act
    print(act)
    print(qu_eng)
    print(f'Answer: {resu_do}')

    print()

    print('############[Problème avec sous-groupe]############')
    st3 = ''
    premises3 = '\n'.join(from_finder(copy_exp, VariableElimination(G)))
    st3 += premises3
    st3 += '\n'

    print('\n'.join(from_finder(copy_exp, VariableElimination(G))))
    event_str = gen_event_str(evt, expr_grp)
    st3 += event_str
    print(event_str)
    st3 += '\n'
    event_qu = gen_question_event(n, i, evt)
    print(st3)
    print(event_qu)
    print(f"Answer: {evt.calc_proba(proba_sub_group)}")
    G_copy = G.copy()
    add_arc_preserve_acyclic(G_copy)
    return st1 + "\n" + qu_eng, resu, st2 + "\n" + qu_eng, resu_do, st3 + "\n" + event_qu, evt.calc_proba(proba_sub_group)


# Disable
def block_print():
    sys.stdout = open(os.devnull, 'w')


# Restore
def enable_print():
    sys.stdout = sys.__stdout__


def __main__():
    number = 100
    data = []
    while len(data) < number:
        result = run()
        if result is not None:
            data.append(list(result))
    df = pd.DataFrame(data, columns=['Simple', 'AnswerSimple', 'Do',  'AnswerDo', 'Group',  'AnswerGroup'])
    df.to_csv('out.csv', index=False)


__main__()
