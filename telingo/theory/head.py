"""
This module exports functions to translate (ground) theory atoms occuring in
rule heads to rules via clingo's backend.
"""

import clingo as _clingo
from telingo.transformers import transformer as _tf
from collections import namedtuple as _namedtuple
from . import body as _bd
from .formula import *

def new_tuple(name, fields, keys, tostring=None):
    ret = _namedtuple(name, fields)
    ret.child_keys = keys
    ret.type = name
    if tostring is not None:
        ret.__str__ = tostring
    ret._rep = property(ret.__str__, "get string representation of tuple")
    return ret

class FormulaToStr(_tf.Transformer):
    """
    Converts head formuals to string.
    """
    def visit_TelAtom(self, x):
        args = "" if len(x.arguments) == 0 else "({})".format(",".join(map(self, x.arguments)))
        sign = "" if x.positive else "-"
        return "{}{}{}".format(sign, x.name, args)

    def visit_TelNext(self, x):
        op = ">:" if x.weak else ">"
        return "({}{}{})".format(x.lhs, op, self(x.rhs))

    def visit_TelUntil(self, x):
        op = ">?" if x.until else ">*"
        lhs = "" if x.lhs is None else self(x.lhs)
        return "({}{}{})".format(lhs, op, self(x.rhs))

    def visit_TelClause(self, x):
        if len(x.elements) == 1:
            return self(x.elements[0])
        op = "&" if x.conjunctive else "|"
        return "({})".format(op.join(map(self, x.elements)))

    def visit_TelNegation(self, x):
        return "(~{})".format(self(x.rhs))

    def visit_TelConstant(self, x):
        return "&true" if x.value else "&false"

def formula_to_str(x):
    return FormulaToStr()(x)

# TODO: more sharing is possible here between body and head formulas
TelNext = new_tuple("TelNext", ["lhs", "rhs", "weak"], ["rhs"], formula_to_str)
TelUntil = new_tuple("TelUntil", ["lhs", "rhs", "until"], ["lhs", "rhs"], formula_to_str)
TelAtom = new_tuple("TelAtom", ["positive", "name", "arguments"], ["arguments"], formula_to_str)
TelClause = new_tuple("TelClause", ["elements", "conjunctive"], ["elements"], formula_to_str)
TelNegation = new_tuple("TelNegation", ["rhs"], ["rhs"], formula_to_str)
TelConstant = new_tuple("TelConstant", ["value"], [], formula_to_str)

def create_atom(rep, add_formula, positive):
    """
    Returns the atom corresponding the given theory term.

    Throws an error if rep it is not a valid atom.

    Arguments:
    rep         -- Theory term to translate.
    add_formula -- Callback to add resulting formulas.
    positive    -- Boolean indicating the classical sign.
    """
    if rep.type == _clingo.TheoryTermType.Symbol:
        return add_formula(TelAtom(positive, rep.name, []))
    elif rep.type == _clingo.TheoryTermType.Function:
        if rep.name == "-" and len(rep.arguments) == 1:
            return create_atom(rep.arguments[0], add_formula, not positive)
        elif rep.name not in g_binary_operators and rep.name not in g_unary_operators and rep.name not in g_tel_operators and rep.name not in g_arithmetic_operators:
            return add_formula(TelAtom(positive, rep.name, [create_symbol(arg) for arg in rep.arguments]))
    raise RuntimeError("invalid atom: ".format(rep))

def create_formula(rep, add_formula):
    """
    Returns the temporal formula corresponding the given theory term.

    Throws an error if rep it is not a valid formula.

    Arguments:
    rep         -- Theory term to translate.
    add_formula -- Callback to add resulting formuals.
    """
    if rep.type == _clingo.TheoryTermType.Symbol:
        return create_atom(rep, add_formula, True)
    elif rep.type == _clingo.TheoryTermType.Function:
        args = rep.arguments
        if rep.name in g_binary_operators and len(args) == 2:
            if rep.name in ("|", "&"):
                lhs = create_formula(args[0], add_formula)
                rhs = create_formula(args[1], add_formula)
                return add_formula(TelClause([lhs, rhs], rep.name == "&"))
            else:
                raise RuntimeError("invalid temporal formula: {}".format(rep))
        elif rep.name in g_unary_operators and len(args) == 1:
            arg = create_formula(args[0], add_formula)
            return add_formula(TelNegation(arg))
        elif rep.name in g_tel_operators:
            if rep.name in ("<", "<:", "<;", "<:;", "<*", "<?", "<<"):
                raise RuntimeError("invalid temporal formula: {}".format(rep))
            rhs = create_formula(args[-1], add_formula)
            if rep.name == ">" or rep.name == ">:":
                lhs = 1 if len(args) == 1 else create_number(args[0])
                return rhs if lhs == 0 else add_formula(TelNext(lhs, rhs, rep.name == ">:"))
            lhs = None if len(args) == 1 else create_formula(args[0], add_formula)
            if rep.name in (";>", ";>:"):
                return add_formula(TelClause([lhs, TelNext(1, rhs, rep.name == ";>:")], True))
            elif rep.name in (">*", ">?"):
                return add_formula(TelUntil(lhs, rhs, rep.name == ">?"))
            else:
                assert(rep.name == ">>")
                final = add_formula(TelAtom(True, "__final", []))
                rhs = add_formula(TelClause([add_formula(TelNegation(final)), rhs], False))
                return add_formula(TelUntil(None, rhs, False))
        elif rep.name == "&":
            arg = rep.arguments[0]
            if arg.type == _clingo.TheoryTermType.Symbol:
                if arg.name == "initial" or arg.name == "final":
                    name = "__{}".format(arg.name)
                    return add_formula(TelNegation(TelNegation(TelAtom(True, name, []))))
                elif arg.name == "true" or arg.name == "false":
                    return add_formula(TelConstant(arg.name == "true"))
                else:
                    raise RuntimeError("unknown identifier: ".format(rep))
            else:
                raise RuntimeError("invalid temporal formula: ".format(rep))
        else:
            return create_atom(rep, add_formula, True)
    else:
        raise RuntimeError("invalid temporal formula: ".format(rep))

def translate_formula(atom, add_formula):
    '''
    - add the formula to the above variants
    - print the variants

    - a named tuple might work here too..
    '''

    clause = []
    for x in atom.elements:
        if x.condition:
            raise RuntimeError('implement me: translate formula')
        elif len(x.terms) != 1:
            raise RuntimeError('implement me: translate formula')
        clause.append(create_formula(x.terms[0], add_formula))
    formula = clause[0] if len(clause) == 1 else TelClause(atom.location, clause, False)
    print (formula)
    raise RuntimeError('implement me: translate formula')
