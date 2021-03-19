"""
This module exports functions to translate (ground) theory atoms occuring in
rule heads to rules via clingo's backend.
"""

import clingo as _clingo
from telingo.transformers import transformer as _tf
from collections import namedtuple as _namedtuple
from . import body as _bd
from .formula import *
import itertools as _it
import functools as _ft
from clingo import ast as _ast


def new_tuple(name, fields, keys, tostring=None):
    ret = _namedtuple(name, fields)
    ret.child_keys = keys
    ret.ast_type = name
    ret.keys = fields
    if tostring is not None:
        ret.__str__ = tostring
    ret._rep = property(ret.__str__, "get string representation of tuple")
    return ret


class FormulaToStr(_tf.TelTransformer):
    """
    Converts head formuals to string.
    """
    def visit_TelAtom(self, x):
        args = "" if len(x.arguments) == 0 else "({})".format(",".join(map(str, x.arguments)))
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

    def visit_TelShift(self, x):
        if x.lhs == 0:
            return "(~(~{})".format(x.rhs)
        elif x.lhs < 0:
            return "(~(~({}<{}))".format(-x.lhs, x.rhs)
        elif x.lhs > 0:
            return "(~(~({}>{}))".format(x.lhs, x.rhs)

def formula_to_str(x):
    return FormulaToStr()(x)

TelNext = new_tuple("TelNext", ["lhs", "rhs", "weak"], ["rhs"], formula_to_str)
TelUntil = new_tuple("TelUntil", ["lhs", "rhs", "until"], ["lhs", "rhs"], formula_to_str)
TelAtom = new_tuple("TelAtom", ["positive", "name", "arguments"], ["arguments"], formula_to_str)
TelClause = new_tuple("TelClause", ["elements", "conjunctive"], ["elements"], formula_to_str)
TelNegation = new_tuple("TelNegation", ["rhs"], ["rhs"], formula_to_str)
TelConstant = new_tuple("TelConstant", ["value"], [], formula_to_str)
TelShift = new_tuple("TelShift", ["lhs", "rhs"], [], formula_to_str)


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
    raise RuntimeError("invalid atom: {}".format(rep))

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
                    raise RuntimeError("unknown identifier: {}".format(rep))
            else:
                raise RuntimeError("invalid temporal formula: {}".format(rep))
        else:
            return create_atom(rep, add_formula, True)
    else:
        raise RuntimeError("invalid temporal formula: {}".format(rep))

class ShiftFormula(_tf.TelTransformer):
    """
    Shifts the given formula.
    """
    def __init__(self, shift):
        self.__shift = shift

    def visit_TelAtom(self, x):
        return x if self.__shift == 0 else TelShift(-self.__shift, x)

    def visit_TelNext(self, x):
        if x.lhs <= self.__shift:
            return shift_formula(x.rhs, self.__shift - x.lhs)
        else:
            return TelShift(0, TelNext(x.lhs - self.__shift, x.rhs, x.weak))

    def visit_TelUntil(self, x):
        inner = TelNext(1, x, not x.until)
        if x.lhs is not None:
            inner = TelClause([x.lhs, inner], x.until)
        return shift_formula(TelClause([x.rhs, inner], not x.until), self.__shift)

    def visit_TelClause(self, x):
        return TelClause(self(x.elements), x.conjunctive)

    def visit_TelNegation(self, x):
        return TelShift(-self.__shift, x)

    def visit_TelConstant(self, x):
        return TelShift(-self.__shift, x)

def shift_formula(x, shift):
    return ShiftFormula(shift)(x)

class UnfoldFormula(_tf.TelTransformer):
    """
    Unfolds the given formula into normal rules.
    """
    def visit_TelAtom(self, x):
        return [[x]]

    def visit_TelShift(self, x):
        return [[x]]

    def visit_TelClause(self, x):
        elements = map(self, x.elements)
        # NOTE: list is mapped over the elements to make sure that iterators are consumed only once
        return map(list, _it.chain(*elements) if x.conjunctive else _it.starmap(_it.chain, _it.product(*elements)))

def unfold_formula(x):
    return UnfoldFormula()(x)

class HeadFormulaToBodyFormula(_tf.TelTransformer):
    def __init__(self, add_formula):
        self.__add_formula = add_formula

    def visit_TelAtom(self, x):
        return self.__add_formula(_bd.Atom(x.name, x.arguments, x.positive))

    def visit_TelNext(self, x):
        return self.__add_formula(_bd.Next(self(x.rhs), x.lhs, x.weak))

    def visit_TelUntil(self, x):
        formula = self.__add_formula(_bd.TelFormulaN(">?", None if x.lhs is None else self(x.lhs), self(x.rhs)))
        formula.set_future(self.__add_formula(_bd.Next(formula, 1, False)))
        return formula

    def visit_TelClause(self, x):
        op = "&" if x.conjunctive else "|"
        elements = map(self, x.elements)
        return _ft.reduce(lambda l, r: _bd.BooleanFormula(op, l, r), elements)

    def visit_TelNegation(self, x):
        return self.__add_formula(_bd.Negation(self(x.rhs)))

    def visit_TelConstant(self, x):
        return self.__add_formula(_bd.BooleanConstant(x.value))

def head_formula_to_body_formula(x, add_formula):
    return HeadFormulaToBodyFormula(add_formula)(x)

class ClauseToRule(_tf.TelTransformer):
    def __init__(self, head, body):
        self.__head = head
        self.__body = body

    def visit_TelAtom(self, x, ctx, step):
        sym  = _clingo.Function(x.name, x.arguments + [_clingo.Number(step)], x.positive)
        atom = ctx.symbols[sym]
        if atom is not None:
            self.__head.append(atom.literal)

    def visit_TelShift(self, x, ctx, step):
        stp = lambda x, n, w: x
        if x.lhs != 0:
            stp = _bd.Next if x.lhs > 0 else _bd.Previous
        neg = lambda x: ctx.add_formula(_bd.Negation(x))
        nxt = lambda l, r: ctx.add_formula(stp(r, abs(l), False))
        rhs = head_formula_to_body_formula(x.rhs, ctx.add_formula)
        frm = neg(nxt(x.lhs, rhs))
        self.__body.append(frm.translate(ctx, step))

def translate_clause(clause, ctx, step, body_literal):
    head = []
    body = [body_literal]
    for lit in clause:
        ClauseToRule(head, body)(lit, ctx, step)
    ctx.backend.add_rule(head, body)

class HeadFormula(Formula):
    """
    Class for temporal and Boolean formulas in rule heads.
    """
    def __init__(self, timestep, formula):
        self.__formula = formula
        self.__timestep = timestep
        self.__literals = []

    @property
    def _rep(self):
        """
        Return the unique string representaiton of the formula.
        """
        return ("head", self.__timestep, self.__formula._rep)

    def translate(self, ctx, step):
        """
        Translates a formula at a given step.

        The formula is first shifted (everything not referring to the current
        time step is double negated).  Then the formula can be converted to
        normal rules. This brings it into clausal form, where every negated
        occurrence of a formula is shifted into a rule body.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.

        Possible Future Optimizations:
        - There can be no more derivations if all next operators have been
          unpacked and no inductive temporal operator has been unpacked.
        - Subformulas not referring to a positive atom can be preceded by
          double negation and do not have to be unpacked at all.
        - To make the translations practical, formulas should be factored in a
          way so that become more compact. The current proof-of-concept
          translation does not pay much mind to this.
        """
        shifted = shift_formula(self.__formula, step - self.__timestep)
        undfolded = unfold_formula(shifted)

        if len(self.__literals) > 1:
            body = backend.atom()
            for x in self.__literals:
                backend.add_rule(body, [x])
            self.__literals = [body]

        for clause in undfolded:
            translate_clause(clause, ctx, step, self.__literals[0])

        ctx.add_todo(self, step+1)

    def add_literal(self, literal):
        self.__literals.append(literal)

    def __str__(self):
        return "{}@{}".format(self.__formula, self.__timestep)

    def __repr__(self):
        return "HeadFormula({!r},{!r})".format(self.__timestep, self.__formula)

def translate_formula(atom, add_formula):
    '''
    - add the formula to the above variants
    - print the variants
    '''
    clause = []
    for x in atom.elements:
        if x.condition or len(x.terms) != 1:
            raise RuntimeError('invalid temporal formula: {}'.format(atom))
        clause.append(create_formula(x.terms[0], add_formula))
    formula = HeadFormula(atom.term.arguments[0].number, clause[0] if len(clause) == 1 else TelClause(clause, False))
    formula.add_literal(atom.literal)
    return formula
