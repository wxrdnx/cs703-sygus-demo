#!/usr/bin/env python

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
    # B
    B = tm.mkVar(boolean, "B")

    # 0
    zero = tm.mkInteger(0)
    # 1
    one = tm.mkInteger(1)

    # (+ I I)
    plus = tm.mkTerm(Kind.ADD, I, I)
    # (- I I)
    minus = tm.mkTerm(Kind.SUB, I, I)
    # (ite B I I)
    ite = tm.mkTerm(Kind.ITE, B, I, I)

    # (and B B)
    And = tm.mkTerm(Kind.AND, B, B)
    # (not B)
    Not = tm.mkTerm(Kind.NOT, B)
    # (<= I I)
    leq = tm.mkTerm(Kind.LEQ, I, I)

    # Create grammar
    g = slv.mkGrammar([x, y], [I, B])
    g.addRules(I, [zero, one, x, y, plus, minus, ite])
    g.addRules(B, [And, Not, leq])

    # Declare the functions and provide the grammar constraints
    Max = slv.synthFun("max", [x, y], integer, g)

    # (declare-var x Int)
    varX = slv.declareSygusVar("x", integer)
    # (declare-var y Int)
    varY = slv.declareSygusVar("y", integer)

    max_x_y = tm.mkTerm(Kind.APPLY_UF, Max, varX, varY)

    # (constraint (>= (max x y) x))
    slv.addSygusConstraint(tm.mkTerm(Kind.GEQ, max_x_y, varX))
    # (constraint (>= (max x y) y))
    slv.addSygusConstraint(tm.mkTerm(Kind.GEQ, max_x_y, varY))

    # (check-synth)
    if (slv.checkSynth().hasSolution()):
        print_synth_solutions([Max], slv.getSynthSolutions([Max]))
