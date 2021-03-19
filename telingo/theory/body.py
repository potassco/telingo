"""
This module exports functions to translate (ground) theory atoms occuring in
rule bodies to rules via clingo's backend.
"""

import clingo as _clingo
from telingo.util import getattr_

from .formula import *
from .path import *

# Base for Body Formulas {{{1

class StepData:
    """
    Stores step specific inforation of theory atoms, like the set of literals
    it is eqivalent to or whether it's translation is already complete.

    Members:
    literal  -- The literal representing the theory atom.
    literals -- All literals equivalent to the theory atom.
    todo     -- Literals that have not yet been made equivalent to the
                representative literal.
    done     -- Whether translation of the theory atom is done.
    """
    def __init__(self):
        """
        Initialize the step information.
        """
        self.literal  = None
        self.literals = set()
        self.todo     = []
        self.done     = True

    def add_literal(self, backend):
        """
        Set the representative of the literal.

        Must only be called once. If there are already equivalent literals one
        of them is chosen as a representative.  Otherwise, a literal and a
        choice rule is added.

        Arguments:
        backend -- Backend to add the choice rule and literal to.
        """
        assert(self.literal is None)
        if len(self.literals) > 0:
            self.literal = min(self.literals)
            self.literals.remove(self.literal)
        else:
            self.literal = backend.add_atom()
            backend.add_rule([self.literal], [], True)
        return self.literal


class BodyFormula(Formula):
    """
    Base class of all temporal and Boolean formulas occurring in rule bodies.

    Members:
    __rep  -- unique string representation of the formula
    __data -- map from time points to StepData objects
    """
    def __init__(self, rep):
        """
        Initializes a formula with the given string representation.
        """
        self.__rep  = rep
        self.__data = {}

    @property
    def _rep(self):
        """
        Return the unique string representaiton of the formula.
        """
        return self.__rep

    def translate(self, ctx, step):
        """
        Translates a formula at a given step.

        Adds a new StepData object to the __data map (if it does not exist
        yet). Calls do_translate, which has to be implemented by base classes.
        And makes sure that the theory atom has a representative literal and
        all literals associated with the theory atom are made equivalent by
        rules.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        """
        data = self.__data.setdefault(step, StepData())
        self.do_translate(ctx, step, data)
        if len(data.todo) > 0:
            for atom in data.todo:
                make_equal(ctx.backend, atom, data.literal)
            del data.todo[:]
        return data.literal

    def add_atom(self, atom, step):
        """
        Adds the given atom to the equivalent literals of the theory atom at
        the given step.

        Arguments:
        atom -- ASP atom to add to the theory atom.
        step -- Step at which to add.
        """
        data = self.__data.setdefault(step, StepData())
        if atom not in data.literals:
            data.literals.add(atom)
            data.todo.append(atom)

# Boolean Formulas {{{1

class Atom(BodyFormula):
    """
    An atomic formula.

    Members:
    __name      -- Predicate name.
    __arguments -- Arguments of the atom (list of symbols).
    __positive  -- Classical negation sign.
    """
    def __init__(self, name, arguments=[], positive=True):
        """
        Initializes the atom.

        Arguments:
        name      -- Name of the atom.
        arguments -- Arguments of the atom.
        positive  -- Classical negation sign.
        """
        rep = "({}{}({}))".format("" if positive else "-", name, ",".join([str(a) for a in arguments]))
        if name.startswith("'"):
            raise RuntimeError("temporal formulas use < instead of leading primes: {}".format(rep))
        if name.endswith("'"):
            raise RuntimeError("temporal formulas use > instead of trailing primes: {}".format(rep))
        BodyFormula.__init__(self, rep)
        self.__name      = name
        self.__arguments = arguments
        self.__positive  = positive

    def do_translate(self, ctx, step, data):
        """
        Translates an atom.

        Requires that the step is within the horizon.

        This means looking the atom up in the symbolic atoms for the given step
        and setting the literal associated with the step accordingly. If the
        atom does not exist, it is set to false.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            sym = _clingo.Function(self.__name, self.__arguments + [_clingo.Number(step)], self.__positive)
            sym_atom = ctx.symbols[sym]
            data.literal = sym_atom.literal if sym_atom is not None else ctx.false_literal

class NumericLiteral(BodyFormula):
    """
    An formula over a numeric literal.

    Members:
    __literal -- The numeric literal.
    """
    def __init__(self, literal):
        """
        Initializes the literal.

        Arguments:
        literal -- The numeric literal.
        """
        BodyFormula.__init__(self, literal)
        self.__literal = literal

    def do_translate(self, ctx, step, data):
        """
        Translates the literal.

        Works the same as Atom.do_translate except that we already have a
        literal.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            data.literal = self.__literal


class BooleanConstant(BodyFormula):
    """
    Formula capturing a Boolean constant.

    Members:
    __value -- Truth value of the formula.
    """
    def __init__(self, value):
        """
        Initializes the formula with the given value.

        Members:
        __value -- Boolean value of the formula.
        """
        BodyFormula.__init__(self, "(&true)" if value else "(&false)")
        self.__value = value

    def do_translate(self, ctx, step, data):
        """
        Translates the formula.

        Requires that the step is within the horizon.

        Sets the literal of the data object to a true or false literal
        depending on the value of the formula.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            data.literal = -ctx.false_literal if self.__value else ctx.false_literal

class Negation(BodyFormula):
    """
    Formula capturing (default) negation.

    Members:
    __arg -- Formula to negate.
    """
    def __init__(self, arg):
        """
        Initializes the formula with the formula to negate.
        """
        BodyFormula.__init__(self, "(~{})".format(arg._rep))
        self.__arg = arg

    def do_translate(self, ctx, step, data):
        """
        Translates the formula.

        Requires that the step is within the horizon.

        Sets the literal to the negated literal of the subformula.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            data.literal = -self.__arg.translate(ctx, step)

class BooleanFormula(BodyFormula):
    """
    Formula capturing binary Boolean formulas.

    Members:
    __operator -- The Boolean connective.
    __lhs      -- The formula on the left-hand-side.
    __rhs      -- The formula on the left-hand-side.
    """

    def __init__(self, operator, lhs, rhs):
        """
        Initializes the formula.

        Arguments:
        operator -- Id of the connective.
        lhs      -- Formula on the left-hand-side.
        rhs      -- Formula on the right-hand-side.
        """
        rep = "({}{}{})".format(lhs._rep, operator, rhs._rep)
        BodyFormula.__init__(self, rep)
        self.__operator = operator
        self.__lhs      = lhs
        self.__rhs      = rhs

    def do_translate(self, ctx, step, data):
        """
        Translates the formula.

        Requires that the step is within the horizon.

        Sets a literal for the formula at the given step and adds clauses based
        on the type of the connective. Clauses are emulated with choices and
        integrity constraints.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            lhs = self.__lhs.translate(ctx, step)
            rhs = self.__rhs.translate(ctx, step)
            lit = data.add_literal(ctx.backend)
            if self.__operator != "<>":
                if self.__operator == "&":
                    lit, lhs, rhs = -lit, -lhs, -rhs
                elif self.__operator == "<-":
                    rhs = -rhs
                elif self.__operator == "->":
                    lhs = -lhs
                make_disjunction(ctx.backend, lit, lhs, rhs)
            elif self.__operator == "<>":
                ctx.backend.add_rule([], [-lit,  rhs,  lhs])
                ctx.backend.add_rule([], [-lit, -rhs, -lhs])
                ctx.backend.add_rule([], [ lit,  rhs, -lhs])
                ctx.backend.add_rule([], [ lit, -rhs,  lhs])

# Temporal Formulas {{{1

class Previous(BodyFormula):
    """
    Captures a formula referring to the previous state.

    Members:
    __arg  -- The argument of the previous operator.
    __weak -- Whether this is a weak previous operator.
    __n    -- How many steps to look back.
    """
    def __init__(self, arg, n, weak):
        """
        Initializes the formula.

        Arguments:
        arg  -- The argument of the previous operator.
        weak -- Whether this is a weak previous operator.
        n    -- How many steps to look back.
        """
        assert(n > 0)
        BodyFormula.__init__(self, "({}{}{})".format(n, "<:" if weak else "<", arg._rep))
        self.__arg  = arg
        self.__weak = weak
        self.__n = n

    def do_translate(self, ctx, step, data):
        """
        Translates an atom.

        Requires that the step is within the horizon.

        Translates the argument with respect to the previous step and sets the
        literal of the formula to the literal obtained thus. If the current
        step refers to the initial state, the literal is either set to the
        true or false literal depending on whether this is a weak previous
        operator or not.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step >= self.__n:
                data.literal = self.__arg.translate(ctx, step - self.__n)
            else:
                data.literal = ctx.false_literal
                if self.__weak and step < self.__n:
                    data.literal = -data.literal

class Initially(BodyFormula):
    """
    Captures a formula referring to the initial situation.

    Members:
    __arg  -- The argument of the previous operator.
    """
    def __init__(self, arg):
        """
        Initializes the formula.

        Arguments:
        arg  -- The argument of the initial operator.
        """
        BodyFormula.__init__(self, "(<<{})".format(arg._rep))
        self.__arg  = arg

    def do_translate(self, ctx, step, data):
        """
        Translates an atom.

        Requires that the step is within the horizon.

        Translates the argument with respect to the initial state and sets the
        literal accordingly.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            data.literal = self.__arg.translate(ctx, 0)

class Next(BodyFormula):
    """
    Captures a formula referring to the next state.

    Members:
    __arg  -- The argument of the next operator.
    __weak -- Whether this is a weak next operator.
    __n    -- How many steps to look ahead.
    """
    def __init__(self, arg, n, weak):
        """
        Initializes the formula.

        Arguments:
        arg  -- The argument of the next operator.
        weak -- Whether this is a weak next operator.
        n    -- How many steps to look ahead.
        """
        BodyFormula.__init__(self, "({}{}{})".format(n, ">:" if weak else ">", arg._rep))
        assert(n > 0)
        self.__arg  = arg
        self.__weak = weak
        self.__n    = n

    def do_translate(self, ctx, step, data):
        """
        Translates an atom.

        Requires that the step is within the horizon.

        Translates the argument with respect to the next step and sets the
        literal of the formula to the literal obtained thus. If the current
        step refers to the final state, a false external literal is created and
        the translation deferred until the next step.

        Note that the correctness of this translation requires that next
        operators are not used in rule heads, which is forbidden by the theory
        definition.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step + self.__n <= ctx.horizon:
                data.literal = self.__arg.translate(ctx, step + self.__n)
                data.done = True
            else:
                data.literal = ctx.backend.add_atom()
                true = getattr_(_clingo.TruthValue, "_True", "True_", "True")
                false = getattr_(_clingo.TruthValue, "_False", "False_", "False")
                ctx.backend.add_external(data.literal, true if self.__weak else false)
                ctx.add_todo(self, step)
                data.done = False
        elif not data.done:
            assert(step in range(0, ctx.horizon + 1))
            if step + self.__n <= ctx.horizon:
                arg = self.__arg.translate(ctx, step + self.__n)
                make_equal(ctx.backend, data.literal, arg)
                ctx.backend.add_external(data.literal, _clingo.TruthValue.Free)
                data.done = True
            else:
                ctx.add_todo(self, step)

class TelFormula(BodyFormula):
    """
    Captures a since, trigger, release, or until formula.

    This is an abstract class providing the basic translation for formulas
    referring to both the future and past.  Due to technical differences, the
    future and past versions are implemented in specialised classes.

    The left-hand-side of the operator can be None in which case either an
    eventually or an always operator is represented.

    Members:
    _op  -- The id of the operator.
    _lhs -- The left-hand-side of the temporal operator.
    _rhs -- The right-hand-side of the temporal operator.
    """

    def __init__(self, rep, op, lhs, rhs):
        """
        Initializes the formula.

        Arguments:
        rep -- Stringu representation of the formula.
        arg -- The id of the operator.
        lhs -- The left-hand-side of the operator.
        rhs -- The right-hand-side of the operator.
        """
        BodyFormula.__init__(self, rep)
        self._op  = op
        self._lhs = lhs
        self._rhs = rhs

    def _translate(self, ctx, step, data, pre):
        """
        Performs the translation of the temporal operator common to both future
        and past formulas.

        The translation works inductively. The literal pre is the literal
        obtained from the inductive step. Since since and trigger are dual, the
        same clauses are added but with the literals inverted in the trigger
        case.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        pre  -- The literal obtained from the inductive step.
        """
        lhs = None if self._lhs is None else self._lhs.translate(ctx, step)
        rhs = self._rhs.translate(ctx, step)
        lit = data.add_literal(ctx.backend)
        if self._op == "<*" or self._op == ">*":
            lit, rhs, pre = -lit, -rhs, -pre
            if lhs is not None:
                lhs = -lhs
        ctx.backend.add_rule([], [-lit, rhs])
        ctx.backend.add_rule([], [-rhs, -pre, lit])
        if lhs is not None:
            ctx.backend.add_rule([], [-lit,  lhs, pre])
            ctx.backend.add_rule([], [-rhs, -lhs, lit])
        else:
            ctx.backend.add_rule([], [-lit, pre])


class TelFormulaP(TelFormula):
    """
    Captures a since or trigger formulas.

    The left-hand-side of the operator can be None in which case either an
    eventually or an always operator is represented.
    """
    def __init__(self, op, lhs, rhs):
        """
        Initializes the formula.

        Arguments:
        arg -- The id of the operator.
        lhs -- The left-hand-side of the operator.
        rhs -- The right-hand-side of the operator.
        """
        rep = "({}{}{})".format("" if lhs is None else lhs._rep, op, rhs._rep)
        TelFormula.__init__(self, rep, op, lhs, rhs)

    def do_translate(self, ctx, step, data):
        """
        Translates the formula.

        Requires that the step is within the horizon.

        The formula is translated inductively using TelFormula._translate.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step == 0:
                data.literal = self._rhs.translate(ctx, step)
            else:
                pre = self.translate(ctx, step - 1)
                self._translate(ctx, step, data, pre)

class TelFormulaN(TelFormula):
    """
    Captures a release or until formulas.

    The left-hand-side of the operator can be None in which case either an
    eventually or an always operator is represented.

    Members:
    __future -- Next formula referring to the future to ease the translation.
    """
    def __init__(self, op, lhs, rhs):
        """
        Initializes the formula.

        Arguments:
        arg -- The id of the operator.
        lhs -- The left-hand-side of the operator.
        rhs -- The right-hand-side of the operator.
        """
        rep = "({}{}{})".format("" if lhs is None else lhs._rep, op, rhs._rep)
        TelFormula.__init__(self, rep, op, lhs, rhs)
        self.__future = None

    def set_future(self, future):
        """
        Set the future formula for the inductive translation.

        This is something like (> self).

        Arguments:
        future -- the formula
        """
        self.__future = future

    def do_translate(self, ctx, step, data):
        """
        Translates the formula.

        Requires that the step is within the horizon.

        The formula is translated inductively using TelFormula._translate.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        data -- Step data associated with the step.
        """
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            fut = self.__future.translate(ctx, step)
            self._translate(ctx, step, data, fut)

# Dynamic Formulas {{{1

class DelFormula(BodyFormula):
    """
    Captures a diamond or box formula.

    Members:
    _op   -- The id of the operator.
    _path -- The left-hand-side of the temporal operator.
    _rhs  -- The right-hand-side of the temporal operator.
    """

    def __init__(self, rep, op, path, rhs):
        """
        Initializes the formula.

        Arguments:
        rep -- String representation of the formula.
        op -- The id of the operator.
        lhs -- The left-hand-side of the operator.
        rhs -- The right-hand-side of the operator.
        """
        self._op   = op
        self._path = path 
        self._rhs  = rhs
        BodyFormula.__init__(self, rep)

class DiamondFormula(DelFormula):
    def __init__(self, path, rhs):
        rep ="({}{}{}{})".format("<", path._rep, ">", rhs._rep)
        DelFormula.__init__(self, rep, "<>", path, rhs)

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            attr = "translate_" + self._path.__class__.__name__
            data.add_literal(ctx.backend)
            getattr(self, attr)(ctx, step, data)

    def translate_ChoicePath(self,ctx, step, data):
        lhs = ctx.add_formula(DiamondFormula(self._path._lhs, self._rhs))
        rhs = ctx.add_formula(DiamondFormula(self._path._rhs, self._rhs))
        self.add_atom(ctx.add_formula(BooleanFormula("|", rhs, lhs)).translate(ctx, step), step)

    def translate_SequencePath(self, ctx, step, data):
        f = ctx.add_formula(DiamondFormula(self._path._rhs, self._rhs)) 
        self.add_atom(ctx.add_formula(DiamondFormula(self._path._lhs, f)).translate(ctx, step), step)
        
    def translate_CheckPath(self, ctx, step, data):
        self.add_atom(ctx.add_formula(BooleanFormula("&", self._path._arg, self._rhs)).translate(ctx, step), step)
        
    def translate_KleeneStarPath(self,ctx, step, data):
        final =  ctx.add_formula(Negation(ctx.add_formula(Next(ctx.add_formula(BooleanConstant(True)), 1, False))))
        a = ctx.add_formula(BooleanFormula("->", final, self._rhs))
        b = ctx.add_formula(BooleanFormula("|", self._rhs, ctx.add_formula(DiamondFormula(self._path._arg, self))))
        self.add_atom(ctx.add_formula(BooleanFormula("&", a, b)).translate(ctx, step), step)

    def translate_SkipPath(self,ctx, step, data):
        self.add_atom(ctx.add_formula(Next(self._rhs, 1, False)).translate(ctx, step), step)

class BoxFormula(DelFormula):
    def __init__(self, path, rhs):
        rep ="({}{}{}{})".format("[", path._rep,"]", rhs._rep)
        DelFormula.__init__(self, rep, "[]", path, rhs)

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            attr = "translate_" + self._path.__class__.__name__
            data.add_literal(ctx.backend)
            getattr(self, attr)(ctx, step, data)

    def translate_ChoicePath(self,ctx, step, data):
        lhs = ctx.add_formula(BoxFormula(self._path._lhs, self._rhs))
        rhs = ctx.add_formula(BoxFormula(self._path._rhs, self._rhs))
        self.add_atom(ctx.add_formula(BooleanFormula("&", rhs, lhs)).translate(ctx, step), step)

    def translate_SequencePath(self,ctx, step, data):
        f = ctx.add_formula(BoxFormula(self._path._rhs, self._rhs)) 
        self.add_atom(ctx.add_formula(BoxFormula(self._path._lhs, f)).translate(ctx, step), step)
        
    def translate_CheckPath(self,ctx, step, data):
        self.add_atom(ctx.add_formula(BooleanFormula("->", self._path._arg, self._rhs)).translate(ctx, step), step)
        
    def translate_KleeneStarPath(self,ctx, step, data):
        final =  ctx.add_formula(Negation(ctx.add_formula(Next(ctx.add_formula(BooleanConstant(True)), 1, False))))
        a = ctx.add_formula(BooleanFormula("->", final, self._rhs))
        b = ctx.add_formula(BooleanFormula("&", self._rhs, ctx.add_formula(BoxFormula(self._path._arg,self))))
        self.add_atom(ctx.add_formula(BooleanFormula("&", a, b)).translate(ctx, step), step)

    def translate_SkipPath(self,ctx, step, data):
        self.add_atom(ctx.add_formula(Next(self._rhs, 1, True)).translate(ctx, step), step)

# Theory of Formulas {{{1

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
        return add_formula(Atom(rep.name, [], positive))
    elif rep.type == _clingo.TheoryTermType.Function:
        if rep.name == "-" and len(rep.arguments) == 1:
            return create_atom(rep.arguments[0], add_formula, not positive)
        elif rep.name not in g_all_operators:
            return add_formula(Atom(rep.name, [create_symbol(arg) for arg in rep.arguments], positive))
    raise RuntimeError("invalid atom: {}".format(rep))

def create_path(rep, add_formula, check):
    """
    Returns the path formula corresponding the given path term.

    Throws an error if rep it is not a valid path formula.

    Arguments:
    rep         -- Term to translate.
    add_formula -- Callback to add resulting formuals.
    """
    if rep.type == _clingo.TheoryTermType.Symbol:
        if check:
            return create_atom(rep, add_formula, True)
        else:
            return add_formula(SequencePath(add_formula(CheckPath(create_atom(rep, add_formula, True))), add_formula(SkipPath())))
    elif rep.type == _clingo.TheoryTermType.Function:
        args = rep.arguments
        if rep.name in g_path_binary_operators:
            if check:
                raise RuntimeError("invalid dynamic formula: {}".format(rep))
            lhs = create_path(args[0], add_formula, False)
            rhs = create_path(args[1], add_formula, False)
            if rep.name == "+":
                return add_formula(ChoicePath(lhs,rhs))
            else:
                assert(rep.name == ";;")
                return add_formula(SequencePath(lhs, rhs))
        elif rep.name in g_path_unary_operators:
            if check:
                raise RuntimeError("invalid dynamic formula: {}".format(rep))
            if rep.name == "?":
                arg = create_path(args[0], add_formula, True)
                return add_formula(CheckPath(arg))
            else:
                assert(rep.name == "*")
                arg = create_path(args[0], add_formula, False)
                return add_formula(KleeneStarPath(arg))
        elif rep.name == "&":
            arg = rep.arguments[0]
            if arg.type == _clingo.TheoryTermType.Symbol:
                if not check and arg.name == "true":
                    return add_formula(SkipPath())
                if check and arg.name == "true" or arg.name == "false":
                    return add_formula(BooleanConstant(arg.name == "true"))
                else:
                    raise RuntimeError("unknown identifier: {}".format(rep))
            else:
                raise RuntimeError("invalid dynamic formula: {}".format(rep))
        #this case is probably impossible 
        else:
            return create_atom(rep, add_formula, True)
    else:
        raise RuntimeError("invalid dynamic formula: {}".format(rep))

def create_dynamic_formula(rep, add_formula):
    """
    Returns the dynamic formula corresponding the given theory term.

    Throws an error if rep it is not a valid formula.

    Arguments:
    rep         -- Theory term to translate.
    add_formula -- Callback to add resulting formuals.
    """
    if rep.type == _clingo.TheoryTermType.Symbol:
        return create_atom(rep, add_formula, True)
    elif rep.type == _clingo.TheoryTermType.Function:
        args = rep.arguments
        if rep.name in g_del_operators:
            lhs = create_path(args[0], add_formula, False)
            rhs = create_dynamic_formula(args[1], add_formula)
            if rep.name == ".>*":
                return add_formula(BoxFormula(lhs,rhs))
            else:
                assert(rep.name == ".>?")
                return add_formula(DiamondFormula(lhs, rhs))
        elif rep.name == "&":
            arg = rep.arguments[0]
            if arg.type == _clingo.TheoryTermType.Symbol:
                if arg.name == "true" or arg.name == "false":
                    return add_formula(BooleanConstant(arg.name == "true"))
                elif arg.name == "final":
                    return add_formula(BoxFormula(add_formula(SkipPath()), add_formula(BooleanConstant(False))))
                else:
                    raise RuntimeError("unknown identifier: {}".format(rep))
            else:
                raise RuntimeError("invalid dynamic formula: {}".format(rep))
        elif rep.name in g_all_operators:
            raise RuntimeError("invalid dynamic formula: {}".format(rep))
        else:
            return create_atom(rep, add_formula, True)
    else:
        raise RuntimeError("invalid dynamic formula: {}".format(rep))

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
            lhs = create_formula(args[0], add_formula)
            rhs = create_formula(args[1], add_formula)
            return add_formula(BooleanFormula(rep.name, lhs, rhs))
        elif rep.name in g_unary_operators and len(args) == 1:
            arg = create_formula(args[0], add_formula)
            return add_formula(Negation(arg))
        elif rep.name in g_tel_operators:
            rhs = create_formula(args[-1], add_formula)
            if rep.name == "<" or rep.name == "<:":
                lhs = 1 if len(args) == 1 else create_number(args[0])
                return rhs if lhs == 0 else add_formula(Previous(rhs, lhs, rep.name == "<:"))
            elif rep.name == ">" or rep.name == ">:":
                lhs = 1 if len(args) == 1 else create_number(args[0])
                return rhs if lhs == 0 else add_formula(Next(rhs, lhs, rep.name == ">:"))
            lhs = None if len(args) == 1 else create_formula(args[0], add_formula)
            if rep.name == "<;" or rep.name == "<:;":
                return add_formula(BooleanFormula("&", Previous(lhs, 1, rep.name == "<:;"), rhs))
            elif rep.name == "<*":
                return add_formula(TelFormulaP("<*", lhs, rhs))
            elif rep.name == "<?":
                return add_formula(TelFormulaP("<?", lhs, rhs))
            elif rep.name == "<<":
                return add_formula(Initially(rhs))
            elif rep.name == ";>" or rep.name == ";>:":
                return add_formula(BooleanFormula("&", lhs, Next(rhs, 1, rep.name == ";>:")))
            elif rep.name == ">*":
                formula = add_formula(TelFormulaN(">*", lhs, rhs))
                formula.set_future(add_formula(Next(formula, 1, True)))
                return formula
            elif rep.name == ">?":
                formula = add_formula(TelFormulaN(">?", lhs, rhs))
                formula.set_future(add_formula(Next(formula, 1, False)))
                return formula
            else:
                assert(rep.name == ">>")
                rhs = add_formula(BooleanFormula("|", add_formula(Negation(add_formula(Atom("__final", [], True)))), rhs))
                formula = add_formula(TelFormulaN(">*", None, rhs))
                formula.set_future(add_formula(Next(formula, 1, True)))
                return formula
        elif rep.name == "&":
            arg = rep.arguments[0]
            if arg.type == _clingo.TheoryTermType.Symbol:
                if arg.name == "initial" or arg.name == "final":
                    name = "__{}".format(arg.name)
                    return add_formula(Atom(name, [], True))
                elif arg.name == "true" or arg.name == "false":
                    return add_formula(BooleanConstant(arg.name == "true"))
                else:
                    raise RuntimeError("unknown identifier: {}".format(rep))
            else:
                raise RuntimeError("invalid temporal formula: {}".format(rep))
        else:
            return create_atom(rep, add_formula, True)
    else:
        raise RuntimeError("invalid temporal formula: {}".format(rep))

def translate_conjunction(formulas, add_formula):
    """
    Return a formula corresponding to the conjunction of the given
    formulas.

    Arguments:
    formulas    -- List of temporal formulas.
    add_formula -- Callback to add resulting formuals.
    """
    if len(formulas) == 0:
        return BooleanConstant(True)

    formulas.sort(key=lambda x: x._rep)
    formula = formulas[0]
    for x in formulas[1:]:
        formula = add_formula(BooleanFormula("&", formula, x))
    return formula


def translate_elements(elements, add_formula, dynamic):
    """
    Translate the given conjunction of elements and return a formula.

    This translation is corresponds to the handling of conditional literals
    in _clingo. The difference is that here only the classical case is
    supported.

    Arguments:
    elements    -- List of theory elements.
    add_formula -- Callback to add resulting formuals.
    """
    formulas = []

    for element in elements:
        if dynamic:
            formulas.append(create_dynamic_formula(element.terms[0], add_formula))
        else:
            formulas.append(create_formula(element.terms[0], add_formula))
        if len(element.condition) > 0:
            condition = translate_conjunction([add_formula(NumericLiteral(literal)) for literal in element.condition], add_formula)
            formulas[-1] = add_formula(BooleanFormula("->", condition, formulas[-1]))

    return translate_conjunction(formulas, add_formula)
