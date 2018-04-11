"""
Module with functions to transform heads referring to the future.
"""

import clingo
from .transformer import *

def new_variant(name, fields, keys, tostring=None):
    """
    Creates a new Variant type, which can be visited with a Transformer.

    Arguments:
    name     -- The name of the variant.
    fields   -- The fields of the variants.
    keys     -- The visitable fields of the variant.
    tostring -- Function or format string to convert the tuple into a string.
    """
    class Variant:
        __slots__  = fields
        type       = name
        child_keys = keys
        __tostring = tostring

        def __init__(self, *args, **kwargs):
            n = len(Variant.__slots__)
            if len(args) + len(kwargs) != n:
                raise TypeError("__init__ takes exactly {} arguments".format(n))
            for key, val, i in zip(self.__slots__, args, range(n)):
                setattr(self, key, val)
                if key in kwargs:
                    raise TypeError("argument given by name ({!r}) and position ({})".format(key, i+1))
            for key, val in kwargs:
                setattr(self, key, val)

        def __repr__(self):
            r = "{}({})".format(Variant.type, ", ".join((repr(getattr(self, key)) for key in Variant.__slots__)))
            return r

        def __str__(self):
            if Variant.__tostring is None:
                return self.__repr__()
            elif callable(Variant.__tostring):
                return Variant.__tostring(self)
            else:
                return Variant.__tostring.format(**{key: getattr(self, key) for key in Variant.__slots__})

    return Variant

def atom_str(x):
    """
    Converts a TelAtom to string.
    """
    args = "" if len(x.arguments) == 0 else "({})".format(",".join(map(str, x.arguments)))
    sign = "" if x.positive else "-"
    return "{}{}{}".format(sign, x.name, args)

def next_str(x):
    op = ">:" if x.weak else ">"
    lhs = "" if x.lhs is None else x.lhs
    return "({}{}{})".format(lhs, op, x.rhs)

def until_str(x):
    op = ">?" if x.until else ">*"
    lhs = "" if x.lhs is None else x.lhs
    return "({}{}{})".format(lhs, op, x.rhs)

def clause_str(x):
    op = "&" if x.conjunctive else "|"
    return "({})".format(op.join(map(str, x.elements)))

def constant_str(x):
    return "&true" if x.value else "&false"

TelNext = new_variant("TelNext", ["location", "lhs", "rhs", "weak"], ["lhs", "rhs"], next_str)
TelUntil = new_variant("TelUntil", ["location", "lhs", "rhs", "until"], ["lhs", "rhs"], until_str)
TelAtom = new_variant("TelAtom", ["location", "positive", "name", "arguments"], ["arguments"], atom_str)
TelClause = new_variant("TelClause", ["location", "elements", "conjunctive"], ["elements"], clause_str)
TelNegation = new_variant("TelNegation", ["location", "rhs"], ["rhs"], "(~{rhs})")
TelConstant = new_variant("TelConstant", ["location", "value"], [], constant_str)

g_tel_keywords = ["true", "false", "final"]

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
        ("&"  , unary):  (6, None),
        ("-"  , unary):  (6, None),
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
            return TelAtom(x.location, positive == symbol.positive, symbol.name, [ast.Symbol(x.location, a) for a in symbol.arguments])
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
            return TelAtom(x.location, positive, x.name, [theory_term_to_term(a) for a in x.arguments])

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
                return TelNext(x.location, lhs, rhs, x.name == ">:")
            elif x.name == "~":
                return TelNegation(x.location, rhs)
            elif x.name == "&" and lhs is None:
                if rhs.type != "TelAtom" or len(rhs.arguments) != 0 or rhs.name not in g_tel_keywords:
                    raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))
                elif rhs.name == "false" or rhs.name == "true":
                    return TelConstant(x.location, rhs.name == "true")
                else:
                    return TelAtom(x.location, True, "__final", [])
            elif x.name == ">?" or x.name == ">*":
                return TelUntil(x.location, lhs, rhs, x.name == ">?")
            elif x.name == ">>":
                # TODO: >* (~ &final | p))
                raise RuntimeError("TODO: decide how to handle finally...")
            elif x.name == "&" or x.name == "|":
                return TelClause(x.location, [lhs, rhs], x.name == "&")
            elif x.name == ";>" or x.name == ";>:":
                return TelClause(x.location, [lhs, TelNext(rhs.location, None, rhs, x.name == ";>:")], True)
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

class VariablesVisitor(Transformer):
    """
    Visitor to collect variables.

    Attributes:
    __variables -- reference to the resulting list of variables
    """
    def __init__(self, variables):
        """
        Initializes the visitor with a reference to a list for storing the
        visited variables.
        """
        self.__variables = variables

    def visit_Variable(self, x):
        """
        Stores the variable in the list.
        """
        self.__variables.append(x)
        return x

def get_variables(x):
    """
    Gets all variables in a formula.
    """
    v = []
    VariablesVisitor(v)(x)
    return v

class ShiftTransformer(Transformer):
    def __init__(self):
        pass

    def visit_TelNext(self, x):
        raise RuntimeError("visit_TelNext: implement me...")

    def visit_TelUntil(self, x):
        raise RuntimeError("visit_TelUntil: implement me...")

def shift_formula(x):
    # TODO: probably have to return more here...
    x = ShiftTransformer()(x)
    return x

class HeadTransformer:
    def __init__(self):
        self.__num_aux = 0

    def __aux_atom(self, location, variables):
        self.__num_aux += 1
        return ast.Literal(location, ast.Sign.NoSign, ast.SymbolicAtom(ast.Function(location, "__aux_{}".format(self.__num_aux - 1), variables, False)))

    def transform(self, atom):
        formula = theory_atom_to_formula(atom)
        rules = []
        # a time parameter has to be attached to the atom
        atom = self.__aux_atom(atom.location, get_variables(formula))
        # in the first part boolean formulas can stay as is
        shifted = shift_formula(formula)
        print (formula, atom)
        # then unpack the temporal operators in the formula
        #   this has to happen as in the translation notes
        #   introducing auxiliary rules in dynamic/always programs
        #   unpack works as follows
        #     the rule is unpacked into a negated and non-negated part
        #     the negated part is left as is
        #     the non-negated part is unpacked further
        # then factor out the formula into disjunctive rules
        #   these rules have to be returned from the function too
        raise RuntimeError("implement me: transform")
        return atom, rules

