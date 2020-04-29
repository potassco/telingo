"""
Module holding basic functions and classes used in the translation temporal
formulas in rule heads and bodies.
"""

import abc as _abc
import clingo as _clingo

def make_equal(backend, a, b):
    """
    Generates clauses for a <-> b.

    Arguments:
    backend -- Backend to add clauses to.
    a       -- first literal
    b       -- second literal
    """
    backend.add_rule([], [ a, -b])
    backend.add_rule([], [-a,  b])

def make_disjunction(backend, e, a, b):
    """
    Generates clauses for e <-> a | b.

    Arguments:
    backend -- Backend to add clauses to.
    e       -- equivalent literal
    a       -- first literal of disjunction
    b       -- second literal of disjunction
    """
    backend.add_rule([], [ e, -a, -b])
    backend.add_rule([], [-e, a])
    backend.add_rule([], [-e, b])

class Context:
    """
    Class gathering arguments used throughout functions in this module.

    Members:
    add_todo        -- Function to add theory atoms that have to be translated
                       later.
    backend         -- Clingo Backend object.
    symbols         -- Clingo SymbolicAtoms object.
    horizon         -- Current search horizon.
    __false_literal -- Function to obtain a false literal.
    """
    def __init__(self, backend, symbols, add_todo, add_formula, false_literal, horizon):
        """
        Initializes the context.

        Arguments:
        backend       -- Backend object.
        symbols       -- SymbolicAtoms object.
        add_todo      -- Function to add theory atoms to the todo list.
        false_literal -- Function to obtain a false literal.
        """
        self.add_todo        = add_todo
        self.add_formula     = add_formula
        self.backend         = backend
        self.symbols         = symbols
        self.horizon         = horizon
        self.__false_literal = false_literal

    @property
    def false_literal(self):
        """
        Returns a literal that is always false.
        """
        return self.__false_literal(self.backend)

"""
Map from binary Boolean connective strings to their ids.
"""
g_binary_operators = {"&", "|", "<>", "<-", "->"}

"""
Set of unary Boolean operators.
"""
g_unary_operators = {"~"}

"""
Set of binary arithmetic operators.
"""
g_arithmetic_operators = {"+", "-"}

"""
Set of temporal connectives.
"""
g_tel_operators = {"<", ">", "<:", ">:", "<*", ">*", ">?", "<?", ">>", "<<", "<;", "<:;", ";>", ";>:"}

"""
Set of dynamic connectives.
"""
g_del_operators = {".>*", ".>?"}

"""
Set of unary Path operators.

"""
g_path_unary_operators  = {"*", "?"}

"""
Set of binary Path operators.

"""
g_path_binary_operators = {";;", "+"}

"""
Set of all tel, del and path operators.

"""
g_all_operators = g_binary_operators.union(g_unary_operators, g_arithmetic_operators, g_tel_operators, g_del_operators, g_path_unary_operators, g_path_binary_operators)

class Formula:
    """
    Base class of all temporal and Boolean formulas.
    """
    @_abc.abstractproperty
    def _rep(self):
        """
        Return the unique string representaiton of the formula.
        """
        pass

    @_abc.abstractmethod
    def translate(self, ctx, step):
        """
        Translates a formula at a given step.

        Arguments:
        ctx  -- Context object.
        step -- Step at which to translate.
        """
        pass

def create_number(rep):
    if rep.type == _clingo.TheoryTermType.Function:
        args = rep.arguments
        if rep.name == "-" and len(args) == 1:
            return -create_number(rep.arguments[0])
        if rep.name in g_arithmetic_operators and len(args) == 2:
            lhs = create_number(rep.arguments[0])
            rhs = create_number(rep.arguments[1])
            if rep.name == "+":
                return lhs + rhs
            elif rep.name == "-":
                return lhs - rhs
    elif rep.type == _clingo.TheoryTermType.Number and rep.number >= 0:
        return rep.number
    # TODO: this case should be handled as in AG
    #       the corresponding formula should evaluate to false
    raise RuntimeError("number expected: {}".format(rep))

def create_symbol(rep):
    """
    Returns the symbolic representation of the given theory term.

    Throws an error if rep it is not a valid symbol.

    Arguments:
    rep -- Theory term to translate.
    """
    if rep.type == _clingo.TheoryTermType.Number:
        return _clingo.Number(rep.number)
    elif rep.type in [_clingo.TheoryTermType.List, _clingo.TheoryTermType.Set]:
        raise RuntimeError("invalid symbol: {}".format(rep))
    elif rep.type == _clingo.TheoryTermType.Function and rep.name in g_arithmetic_operators:
        if len(rep.arguments) == 1:
            rhs = create_symbol(rep.arguments[0])
            if rep.name == "-":
                if rhs.type == _clingo.SymbolType.Number:
                    return _clingo.Number(-rhs.number)
                elif rhs.type == _clingo.SymbolType.Function and len(rep.name) > 0:
                    return _clingo.Function(rhs.name, rhs.arguments, not rhs.positive)
        elif len(rep.arguments) == 2:
            return _clingo.Number(create_number(rep))

        raise RuntimeError("invalid symbol: {}".format(rep))
    else:
        name = "" if rep.type == _clingo.TheoryTermType.Tuple else rep.name
        if name in g_binary_operators or name in g_unary_operators or name in g_tel_operators:
            raise RuntimeError("invalid symbol: {}".format(rep))
        args = [] if rep.type == _clingo.TheoryTermType.Symbol else rep.arguments
        if len(args) == 0:
            if name == "#inf":
                return _clingo.Infimum
            elif name == "#sup":
                return _clingo.Supremum
            elif len(name) > 1 and name.startswith('"') and name.endswith('"'):
                return _clingo.String(name[1:-1])
        return _clingo.Function(name, [create_symbol(arg) for arg in args])

