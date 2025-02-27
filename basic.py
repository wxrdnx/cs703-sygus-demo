#!/usr/bin/env python

import copy
import cvc5
from cvc5 import Kind

def define_fun_to_string(f, params, body):
    sort = f.getSort()
    if sort.isFunction():
        sort = f.getSort().getFunctionCodomainSort()
    result = "(define-fun " + str(f) + " ("
    for i in range(0, len(params)):
        if i > 0:
            result += " "
        result += "(" + str(params[i]) + " " + str(params[i].getSort()) + ")"
    result += ") " + str(sort) + " " + str(body) + ")"
    return result

def print_synth_solutions(terms, sols):
    result = "(\n"
    for i in range(0, len(terms)):
        params = []
        body = sols[i]
        if sols[i].getKind() == Kind.LAMBDA:
            params += sols[i][0]
            body = sols[i][1]
        result += "  " + define_fun_to_string(terms[i], params, body) + "\n"
    result += ")"
    print(result)

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver()

    slv.setOption("sygus", "true")

    # (set-logic LIA)
    slv.setLogic("LIA")

    integer = tm.getIntegerSort()
    boolean = tm.getBooleanSort()

    # (x Int)
    x = tm.mkVar(integer, "x")
    # (y Int)
    y = tm.mkVar(integer, "y")

    # I
    I = tm.mkVar(integer, "I")

    # 0
    zero = tm.mkInteger(0)
    # 1
    one = tm.mkInteger(1)

    # (+ I I)
    plus = tm.mkTerm(Kind.ADD, I, I)
    # (- I I)
    minus = tm.mkTerm(Kind.SUB, I, I)

    # Create grammar
    g = slv.mkGrammar([x, y], [I])
    g.addRules(I, [zero, one, x, y, plus, minus])

    # Declare the functions and provide the grammar constraints
    f = slv.synthFun("f", [x, y], integer, g)

    # (check-synth)
    if (slv.checkSynth().hasSolution()):
        print_synth_solutions([f], slv.getSynthSolutions([f]))
