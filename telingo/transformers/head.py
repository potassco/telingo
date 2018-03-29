"""
Module with functions to transform heads referring to the future.
"""

import clingo
from .transformer import *
from collections import namedtuple

Next = namedtuple("Next", "location lhs rhs weak")
Until = namedtuple("Until", "location lhs rhs until")
Atom = namedtuple("Atom", "location positive name arguments")
Clause = namedtuple("Clause", "location elements conjunctive")
Negation = namedtuple("Negation", "location rhs")

class TheoryParser:
    """
    Parser for temporal formulas.

    Constants:
    unary  -- Boolean to mark unary operators.
    binary -- Boolean to mark unary operators.
    left   -- Boolean to mark left associativity.
    right  -- Boolean to mark right associativity.
    """
    unary, binary = True, False
    left,  right  = True, False
    table = {
        ("&"  , unary):  (5, None),
        ("-"  , unary):  (5, None),
        ("~"  , unary):  (5, None),
        (">"  , unary):  (5, None),
        (">"  , binary): (5, right),
        (">:" , unary):  (5, None),
        (">:" , binary): (5, right),
        (">?" , unary):  (5, None),
        (">*" , unary):  (5, None),
        (">>" , unary):  (5, None),
        (">*" , binary): (4, left),
        (">?" , binary): (4, left),
        ("&"  , binary): (3, left),
        ("|"  , binary): (2, left),
        (";>" , binary): (0, right),
        (";>:", binary): (0, right) }

    def __init__(self):
        """
        Initializes the parser.
        """
        self.__stack  = []

    def __priority_and_associativity(self, operator):
        """
        Get priority and associativity of the given binary operator.
        """
        return self.table[(operator, self.binary)]

    def __priority(self, operator, unary):
        """
        Get priority of the given unary or binary operator.
        """
        return self.table[(operator, unary)][0]

    def __check(self, operator):
        """
        Returns true if the stack has to be reduced because of the precedence
        of the given binary operator is lower than the preceeding operator on
        the stack.
        """
        if len(self.__stack) < 2:
            return False
        priority, associativity = self.__priority_and_associativity(operator)
        previous_priority       = self.__priority(*self.__stack[-2])
        return previous_priority > priority or (previous_priority == priority and associativity)

    def __reduce(self):
        """
        Combines the last unary or binary term on the stack.
        """
        b = self.__stack.pop()
        operator, unary = self.__stack.pop()
        if unary:
            self.__stack.append(ast.TheoryFunction(b.location, operator, [b]))
        else:
            a = self.__stack.pop()
            l = {"begin": a.location["begin"], "end": b.location["end"]}
            self.__stack.append(ast.TheoryFunction(l, operator, [a, b]))

    def parse(self, x):
        """
        Parses the given unparsed term, replacing it by nested theory
        functions.
        """
        del self.__stack[:]
        unary = True
        for element in x.elements:
            for operator in element.operators:
                if not (operator, unary) in self.table:
                    raise RuntimeError("invalid operator in temporal formula: {}".format(str_location(x.location)))
                while not unary and self.__check(operator):
                    self.__reduce()
                self.__stack.append((operator, unary))
                unary = True
            self.__stack.append(element.term)
            unary = False
        while len(self.__stack) > 1:
            self.__reduce()
        return self.__stack[0]

def parse_raw_formula(x):
    """
    Turns the given unparsed term into a term.
    """
    return TheoryParser().parse(x)

class HeadTermTransformer(Transformer):
    """
    This class transforms a given theory term into a plain term.
    """
    def visit_Symbol(self, x):
        """
        Symbols are equally represented in terms and theory terms.
        """
        return x

    def visit_Variable(self, x):
        """
        Variables are equally represented in terms and theory terms.
        """
        return x

    def visit_TheoryTermSequence(self, x):
        """
        Theory term tuples are mapped to term tuples.
        """
        if x.sequence_type == ast.TheorySequenceType.Tuple:
            return ast.Function(x.location, "", [self(a) for a in x.arguments], False)
        else:
            raise RuntimeError("invalid term: {}".format(str_location(x.location)))

    def visit_TheoryFunction(self, x):
        """
        Theory functions are mapped to functions.

        If the function name refers to a temporal operator, an exception is thrown.
        """
        if x.name == "-":
            return ast.UnaryOperation(x.location, ast.UnaryOperator.Minus, self(x.arguments[0]))
        elif (x.name, TheoryParser.binary) in TheoryParser.table or (x.name, TheoryParser.unary) in TheoryParser.table:
            raise RuntimeError("invalid term: {}".format(str_location(x.location)))
        else:
            return ast.Function(x.location, x.name, [self(a) for a in x.arguments], False)

    def visit_TheoryUnparsedTerm(self, x):
        """
        Unparsed term are first parsed and then handled by the transformer.
        """
        return self.visit(parse_raw_formula(x))

def theory_term_to_term(x):
    """
    Convert the given theory term into a term.
    """
    return HeadTermTransformer()(x)

class HeadAtomTransformer(Transformer):
    """
    Turns the given theory term into an atom.
    """

    def visit_Symbol(self, x, positive):
        """
        Maps functions to atoms.

        Every other symbol causes a runtime error.

        Arguments:
        x        -- The theory term to translate.
        positive -- The classical sign of the atom.
        """
        symbol = x.symbol
        if x.symbol.type == clingo.SymbolType.Function and len(symbol.name) > 0:
            return Atom(x.location, positive != symbol.positive, symbol.name, [ast.Symbol(x.location, a) for a in symbol.arguments])
        else:
            raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))

    def visit_Variable(self, x, positive):
        """
        Raises an error.
        """
        raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))


    def visit_TheoryTermSequence(self, x, positive):
        """
        Raises an error.
        """
        raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))

    def visit_TheoryFunction(self, x, positive):
        """
        Maps theory functions to atoms.

        If the function name refers to a temporal operator, an exception is thrown.
        """
        if x.name == "-":
            return self(x.arguments[0], not positive)
        elif (x.name, TheoryParser.binary) in TheoryParser.table or (x.name, TheoryParser.unary) in TheoryParser.table:
            raise RuntimeError("invalid term: {}".format(str_location(x.location)))
        else:
            return Atom(x.location, positive, x.name, [theory_term_to_term(a) for a in x.arguments])

    def visit_TheoryUnparsedTerm(self, x, positive):
        """
        Unparsed terms are first parsed and then handled by the transformer.
        """
        return self.visit(parse_raw_formula(x), positive)

def theory_term_to_atom(x, positive=True):
    """
    Convert the given theory term into an atom.
    """
    return HeadAtomTransformer()(x, positive)

class HeadFormulaTransformer(Transformer):
    """
    Transforms a theory atom into a temporal formula.
    """
    def visit_Symbol(self, x):
        return theory_term_to_atom(x, True)

    def visit_Variable(self, x, positive):
        """
        Raises an error.
        """
        raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))


    def visit_TheoryTermSequence(self, x, positive):
        """
        Raises an error.
        """
        raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))

    def visit_TheoryUnparsedTerm(self, x):
        """
        Unparsed terms are first parsed and then handled by the transformer.
        """
        return self.visit(parse_raw_formula(x))

    def visit_TheoryFunction(self, x):
        """
        Transforms the given theory function into a temporal formula.
        """
        is_binary = (x.name, TheoryParser.binary) in TheoryParser.table and len(x.arguments) == 2
        is_unary  = (x.name, TheoryParser.unary) in TheoryParser.table and len(x.arguments) == 1
        if is_unary or is_binary:
            if x.name == "-":
                return theory_term_to_atom(x, False)

            if is_unary:
                lhs = None
                rhs = self.visit(x.arguments[0])
            else:
                if x.name == ">" or x.name == ">:":
                    lhs = theory_term_to_term(x.arguments[0])
                else:
                    lhs = self.visit(x.arguments[0])
                rhs = self.visit(x.arguments[1])

            if x.name == ">" or x.name == ">:":
                return Next(x.location, lhs, rhs, x.name == ">:")
            elif x.name == "~":
                return Negation(x.location, rhs)
            elif x.name == "&" and lhs is None:
                raise RuntimeError("implement me: true, false, initial, final, ...")
            elif x.name == ">?" or x.name == ">*":
                return Until(x.location, lhs, rhs, x.name == ">?")
            elif x.name == ">>":
                raise RuntimeError("TODO: decide how to handle finally...")
            elif x.name == "&" or x.name == "|":
                return Clause(x.location, [lhs, rhs], x.name == "&")
            elif x.name == ";>" or x.name == ";>:":
                raise RuntimeError("TODO: decide how to handle sequence...")
            else:
                raise RuntimeError("cannot happen")
        else:
            return theory_term_to_atom(x)

    def visit_TheoryAtomElement(self, x):
        """
        Transforms one elementary theory elements without conditions into formulas.
        """
        if len(x.tuple) != 1 or len(x.condition) != 0:
            raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))
        return self.visit(x.tuple[0])

    def visit_TheoryAtom(self, x):
        """
        Transforms one elementary theory atoms into formulas.
        """
        if len(x.elements) != 1 or x.guard is not None:
            raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))
        return self.visit(x.elements[0])

def theory_atom_to_formula(x):
    """
    Transforms the given theory atom into a temporal formula.
    """
    return HeadFormulaTransformer()(x)

class HeadTransformer:
    def __init__(self):
        pass

    def transform(self, atom):
        formula = theory_atom_to_formula(atom)
        rules = []
        atom = None
        # next grab the variables in the formula to create an auxiliary atom, which can be returned from the function
        # then unpack the temporal operators in the formula
        # then factor out the formula into disjunctive rules
        # these rules have to be returned from the function too
        raise RuntimeError("implement me: transform")
        return atom, rules

