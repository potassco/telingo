"""
TODO: document
"""

import clingo
import clingo.ast as ast

# Base for Formulas {{{1

def make_equal(backend, a, b):
    backend.add_rule([], [ a, -b])
    backend.add_rule([], [-a,  b])

def make_disjunction(backend, e, a, b):
    backend.add_rule([], [ e, -a, -b])
    backend.add_rule([], [-e, a])
    backend.add_rule([], [-e, b])

class StepData:
    def __init__(self):
        self.literal  = None
        self.literals = set()
        self.todo     = []
        self.done     = True

    def add_literal(self, backend):
        assert(self.literal is None)
        if len(self.literals) > 0:
            self.literal = min(self.literals)
            self.literals.remove(self.literal)
        else:
            self.literal = backend.add_atom()
            backend.add_rule([self.literal], [], True)
        return self.literal

class Context:
    def __init__(self, backend, symbols, add_todo, false_literal, horizon):
        self.add_todo        = add_todo
        self.backend         = backend
        self.symbols         = symbols
        self.horizon         = horizon
        self.__false_literal = false_literal

    @property
    def false_literal(self):
        return self.__false_literal(self.backend)

class Formula:
    def __init__(self, rep):
        self.__rep  = rep
        self.__data = {}

    @property
    def _rep(self):
        return self.__rep

    def translate(self, ctx, step):
        data = self.__data.setdefault(step, StepData())
        self.do_translate(ctx, step, data)
        if len(data.todo) > 0:
            for atom in data.todo:
                make_equal(ctx.backend, atom, data.literal)
            del data.todo[:]
        return data.literal

    def add_atom(self, atom, step):
        data = self.__data.setdefault(step, StepData())
        if atom not in data.literals:
            data.literals.add(atom)
            data.todo.append(atom)

# Boolean Formulas {{{1

class Atom(Formula):
    def __init__(self, rep, name, arguments = []):
        if name.startswith("'"):
            raise RuntimeError("temporal formulas use < instead of leading primes: ".format(rep))
        if name.endswith("'"):
            raise RuntimeError("temporal formulas use > instead of trailing primes: ".format(rep))

        Formula.__init__(self, rep)
        self.__name      = name
        self.__arguments = arguments

    def do_translate(self, ctx, step, data):
        # TODO: does not support classical negation for now...
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            sym = clingo.Function(self.__name, self.__arguments + [step])
            sym_atom = ctx.symbols[sym]
            data.literal = sym_atom.literal if sym_atom is not None else ctx.false_literal

class BooleanBinary(Formula):
    And = 0
    Or  = 1
    Eq  = 2
    Li  = 3
    Ri  = 4
    def __init__(self, rep, operator, lhs, rhs):
        Formula.__init__(self, rep)
        self.__operator = operator
        self.__lhs      = lhs
        self.__rhs      = rhs

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            lhs = self.__lhs.translate(ctx, step)
            rhs = self.__rhs.translate(ctx, step)
            lit = data.add_literal(ctx.backend)
            if self.__operator != BooleanBinary.Eq:
                if self.__operator == BooleanBinary.And:
                    lit, lhs, rhs = -lit, -lhs, -rhs
                elif self.__operator == BooleanBinary.Li:
                    rhs = -rhs
                elif self.__operator == BooleanBinary.Ri:
                    lhs = -lhs
                make_disjunction(ctx.backend, lit, lhs, rhs)
            elif self.__operator == BooleanBinary.Eq:
                ctx.backend.add_rule([], [ lit,  rhs,  lhs])
                ctx.backend.add_rule([], [ lit, -rhs, -lhs])
                ctx.backend.add_rule([], [-lit,  rhs, -lhs])
                ctx.backend.add_rule([], [-lit, -rhs,  lhs])

class Negation(Formula):
    def __init__(self, rep, arg):
        Formula.__init__(self, rep)
        self.__arg = arg

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            data.literal = -self.__arg.translate(ctx, step)

# Past Formulas {{{1

class Previous(Formula):
    def __init__(self, rep, arg, weak):
        Formula.__init__(self, rep)
        self.__arg  = arg
        self.__weak = weak

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step > 0:
                data.literal = self.__arg.translate(ctx, step-1)
            else:
                data.literal = ctx.false_literal
                if self.__weak and step == 0:
                    data.literal = -data.literal

class TelP(Formula):
    Since   = 0
    Trigger = 1

    def __init__(self, rep, op, lhs, rhs):
        Formula.__init__(self, rep)
        self.__op  = op
        self.__lhs = lhs
        self.__rhs = rhs

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step == 0:
                data.literal = self.__rhs.translate(ctx, step)
            else:
                pre = self.translate(ctx, step - 1)
                lhs = None if self.__lhs is None else self.__lhs.translate(ctx, step)
                rhs = self.__rhs.translate(ctx, step)
                lit = data.add_literal(ctx.backend)
                if self.__op == TelP.Trigger:
                    lit, rhs, pre = -lit, -rhs, -pre
                    if lhs is not None:
                        lhs = - lhs
                ctx.backend.add_rule([], [-lit, rhs])
                ctx.backend.add_rule([], [-rhs, -pre, lit])
                if lhs is not None:
                    ctx.backend.add_rule([], [-lit,  lhs, pre])
                    ctx.backend.add_rule([], [-rhs, -lhs, lit])
                else:
                    ctx.backend.add_rule([], [-lit, pre])

# Future Formulas {{{1

class Next(Formula):
    def __init__(self, rep, arg, weak):
        Formula.__init__(self, rep)
        self.__arg  = arg
        self.__weak = weak

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            if step < ctx.horizon:
                data.literal = self.__arg.translate(ctx, step+1)
                data.done = True
            else:
                data.literal = ctx.backend.add_atom()
                ctx.backend.add_external(data.literal, clingo.TruthValue._True if self.__weak else clingo.TruthValue._False)
                ctx.add_todo(self._rep, self, step)
                data.done = False
        elif not data.done:
            assert(step in range(0, ctx.horizon))
            arg = self.__arg.translate(ctx, step+1)
            make_equal(ctx.backend, data.literal, arg)
            ctx.backend.add_external(data.literal, clingo.TruthValue.Free)
            data.done = True

class AlwaysN(Formula):
    def __init__(self, rep, rhs):
        Formula.__init__(self, rep)
        self.__rhs    = rhs
        self.__future = None

    def set_future(self, future):
        self.__future = future

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            lit = data.add_literal(ctx.backend)
            rhs = self.__rhs.translate(ctx, step)
            fut = self.__future.translate(ctx, step)
            make_disjunction(ctx.backend, -lit, -rhs, -fut)

class EventuallyN(Formula):
    def __init__(self, rep, rhs):
        Formula.__init__(self, rep)
        self.__rhs    = rhs
        self.__future = None

    def set_future(self, future):
        self.__future = future

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            assert(step in range(0, ctx.horizon + 1))
            lit = data.add_literal(ctx.backend)
            rhs = self.__rhs.translate(ctx, step)
            fut = self.__future.translate(ctx, step)
            make_disjunction(ctx.backend, lit, rhs, fut)

# Theory of Formulas {{{1

_binary_operators = {
    "&": BooleanBinary.And,
    "|": BooleanBinary.Or,
    "<>": BooleanBinary.Eq,
    "<-": BooleanBinary.Li,
    "->": BooleanBinary.Ri}

_unary_operators = {"~"}

_tel_operators = {"<", ">", "<:", ">:", "<*", ">*", ">?", "<?"}

def create_symbol(rep):
    if rep.type == clingo.TheoryTermType.Number:
        return clingo.Number(rep.number)
    elif rep.type in [clingo.TheoryTermType.List, clingo.TheoryTermType.Set]:
        raise RuntimeError("invalid symbol: {}".format(rep))
    else:
        name = "" if rep.type == clingo.TheoryTermType.Tuple else rep.name
        if name in _binary_operators or name in _unary_operators or name in _tel_operators:
            raise RuntimeError("invalid symbol: {}".format(rep))
        args = [] if rep.type == clingo.TheoryTermType.Symbol else rep.arguments
        if len(args) == 0:
            if name == "#inf":
                return clingo.Infimum
            elif name == "#sup":
                return clingo.Supremum
            elif len(name) > 1 and name.startswith('"') and name.endswith('"'):
                return clingo.String(name[1:-1])
        return clingo.Function(name, [create_symbol(arg) for arg in args])

def create_formula(rep, formulas):
    if rep.type == clingo.TheoryTermType.Symbol:
        formula = Atom(str(rep), rep.name, [])
    elif rep.type == clingo.TheoryTermType.Function:
        args = rep.arguments
        if rep.name in _binary_operators:
            lhs = create_formula(args[0], formulas)
            rhs = create_formula(args[1], formulas)
            formula = BooleanBinary(str(rep), _binary_operators[rep.name], lhs, rhs)
        elif rep.name in _unary_operators:
            arg = create_formula(args[0], formulas)
            formula = Negation(str(rep), arg)
        elif rep.name in _tel_operators:
            lhs = None if len(args) == 1 else create_formula(args[0], formulas)
            rhs = create_formula(args[-1], formulas)
            if rep.name == "<" or rep.name == "<:":
                formula = Previous(str(rep), rhs, rep.name == "<:")
            elif rep.name == "<*":
                formula = TelP(str(rep), TelP.Trigger, lhs, rhs)
            elif rep.name == "<?":
                formula = TelP(str(rep), TelP.Since, lhs, rhs)
            elif rep.name == ">" or rep.name == ">:":
                formula = Next(str(rep), rhs, rep.name == ">:")
            elif rep.name == ">*":
                formula = formulas.add_formula(AlwaysN(str(rep), rhs))
                formula.set_future(formulas.add_formula(Next("(>:{})".format(rep), formula, True)))
            elif rep.name == ">?":
                formula = formulas.add_formula(EventuallyN(str(rep), rhs))
                formula.set_future(formulas.add_formula(Next("(>:{})".format(rep), formula, False)))
            else:
                assert(False and "implement me!!!")
        else:
            formula = Atom(str(rep), rep.name, [create_symbol(arg) for arg in rep.arguments])
    else:
        raise RuntimeError("invalid temporal formula: ".format(rep))
    formula = formulas.add_formula(formula)
    return formula

class Theory:
    def __init__(self):
        self.__formulas = {}
        self.__todo_keys = set()
        self.__todo = []
        self.__false_literal = None

    def add_formula(self, formula):
        formula = self.__formulas.setdefault(formula._rep, formula)
        return formula

    def add_todo(self, key, formula, step):
        key = (step, key)
        if key not in self.__todo_keys:
            self.__todo_keys.add(key)
            self.__todo.append((step, formula))

    def false_literal(self, backend):
        if self.__false_literal is None:
            self.__false_literal = backend.add_atom()
        return self.__false_literal

    def translate(self, horizon, prg):
        for atom in prg.theory_atoms:
            time    = atom.term.arguments[0].number
            rep     = atom.elements[0].terms[0]
            formula = create_formula(rep, self)
            formula.add_atom(atom.literal, horizon)
            self.add_todo(str(rep), formula, horizon)

        if len(self.__todo) > 0:
            todo, self.__todo, self.__todo_keys = self.__todo, [], set()
            with prg.backend() as b:
                ctx = Context(b, prg.symbolic_atoms, self.add_todo, self.false_literal, horizon)
                for step, formula in todo:
                    formula.translate(ctx, step)
