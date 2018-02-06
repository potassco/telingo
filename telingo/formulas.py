"""
TODO: document
"""

import clingo

def make_equal(backend, a, b):
    backend.add_rule([], [ a, -b])
    backend.add_rule([], [-a,  b])

class StepData:
    def __init__(self):
        self.literal  = None
        self.literals = set()
        self.todo     = []

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

class Atom(Formula):
    def __init__(self, rep, name, arguments = []):
        Formula.__init__(self, rep)
        self.__name      = name
        self.__arguments = arguments

    def do_translate(self, ctx, step, data):
        assert(data.literal is None)
        assert(step in range(0, ctx.horizon + 1))
        # TODO: can be build so that step in [0, horizon]
        if step < 0:
            assert(False and "untested")
            if data.literal is None:
                data.literal = ctx.false_literal
            return

        sym = clingo.Function(self.__name, self.__arguments + [step])
        # the atom has not yet been translated
        if data.literal is None:
            # the atom refers to the future and is added as an external
            if step > ctx.horizon:
                assert(False and "untested")
                data.literal = ctx.backend.add_atom(sym, step)
                ctx.backend.add_external(data.literal, clingo.TruthValue._False)
                ctx.add_todo(self._rep, self, step)
            # the atom is already defined or won't be defined anymore
            else:
                sym_atom = ctx.symbols[sym]
                data.literal = sym_atom.literal if sym_atom is not None else ctx.false_literal
        # the atom has already been translated
        else:
            # the atom refers to the future and has to be released later
            if step > ctx.horizon:
                assert(False and "untested")
                ctx.add_todo(self._rep, self, step)
            # the atom has to be released because it was either defined or won't be defined anymore
            if data.literal != ctx.false_literal:
                assert(False and "untested")
                ctx.backend.add_external(data.literal, clingo.TruthValue.Release)

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
            lhs          = self.__lhs.translate(ctx, step)
            rhs          = self.__rhs.translate(ctx, step)
            data.literal = data.add_literal(ctx.backend)
            if self.__operator == BooleanBinary.And:
                ctx.backend.add_rule([], [-data.literal, rhs, lhs])
                ctx.backend.add_rule([], [ data.literal, -rhs])
                ctx.backend.add_rule([], [ data.literal, -lhs])
            elif self.__operator == BooleanBinary.Or:
                ctx.backend.add_rule([], [ data.literal, -rhs, -lhs])
                ctx.backend.add_rule([], [-data.literal, rhs])
                ctx.backend.add_rule([], [-data.literal, lhs])
            elif self.__operator == BooleanBinary.Li:
                ctx.backend.add_rule([], [ data.literal,  rhs, -lhs])
                ctx.backend.add_rule([], [-data.literal, -rhs])
                ctx.backend.add_rule([], [-data.literal,  lhs])
            elif self.__operator == BooleanBinary.Ri:
                ctx.backend.add_rule([], [ data.literal, -rhs, lhs])
                ctx.backend.add_rule([], [-data.literal,  rhs])
                ctx.backend.add_rule([], [-data.literal, -lhs])
            elif self.__operator == BooleanBinary.Eq:
                ctx.backend.add_rule([], [ data.literal,  rhs,  lhs])
                ctx.backend.add_rule([], [ data.literal, -rhs, -lhs])
                ctx.backend.add_rule([], [-data.literal,  rhs, -lhs])
                ctx.backend.add_rule([], [-data.literal, -rhs,  lhs])

class Negation(Formula):
    def __init__(self, rep, arg):
        Formula.__init__(self, rep)
        self.__arg = arg

    def do_translate(self, ctx, step, data):
        if data.literal is None:
            data.literal = -self.__arg.translate(ctx, step)

_binary_operators = {
    "&": BooleanBinary.And,
    "|": BooleanBinary.Or,
    "<>": BooleanBinary.Eq,
    "<-": BooleanBinary.Li,
    "->": BooleanBinary.Ri}

_unary_operators = set("~")

def create_symbol(rep):
    if rep.type == clingo.TheoryTermType.Number:
        return clingo.Number(rep.number)
    elif rep.type in [clingo.TheoryTermType.List, clingo.TheoryTermType.Set]:
        raise RuntimeError("invalid symbol: {}".format(rep))
    else:
        name = "" if rep.type == clingo.TheoryTermType.Tuple else rep.name
        if name in _binary_operators or name in _unary_operators:
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

def create_formula(rep, formulas, step):
    if rep.type == clingo.TheoryTermType.Symbol:
        formula = Atom(str(rep), rep.name, [])
    elif rep.type == clingo.TheoryTermType.Function:
        if rep.name in _binary_operators:
            lhs = create_formula(rep.arguments[0], formulas, step)
            rhs = create_formula(rep.arguments[1], formulas, step)
            formula = BooleanBinary(str(rep), _binary_operators[rep.name], lhs, rhs)
        elif rep.name in _unary_operators:
            arg = create_formula(rep.arguments[0], formulas, step)
            formula = Negation(str(rep), arg)
        else:
            formula = Atom(str(rep), rep.name, [create_symbol(arg) for arg in rep.arguments])
    else:
        raise RuntimeError("invalid temporal formula: ".format(rep))
    formula = formulas.add_formula(str(rep), formula, step)
    return formula

class Formulas:
    def __init__(self):
        self.__formulas = {}
        self.__todo_keys = set()
        self.__todo = []
        self.__false_literal = None

    def add_formula(self, key, formula, step):
        formula = self.__formulas.setdefault(key, formula)
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
            formula = create_formula(rep, self, horizon)
            formula.add_atom(atom.literal, horizon)
            self.add_todo(str(rep), formula, horizon)

        if len(self.__todo) > 0:
            todo, self.__todo, self.__todo_keys = self.__todo, [], set()
            with prg.backend() as b:
                ctx = Context(b, prg.symbolic_atoms, self.add_todo, self.false_literal, horizon)
                for step, formula in todo:
                    formula.translate(ctx, step)
