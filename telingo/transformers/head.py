"""
Module with functions to transform heads referring to the future.
"""

from . import transformer as _tf

import clingo as _clingo
from clingo import ast as _ast
from numbers import Number as _Number
from operator import itemgetter as _itemgetter

# {{{ data structures

def new_variant(name, fields, keys, tostring=None):
    """
    Creates a new Variant type, which can be visited with a _tf.Transformer.

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
                # pylint: disable=line-too-long
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

    Variant.__name__ = name

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
    if len(x.elements) == 1:
        return str(x.elements[0])
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
TelComparison = new_variant("TelComparison", ["location", "lhs", "operator", "rhs"], [], "({lhs}{operator}{rhs})")
TelFormula = new_variant("TelFormula", ["location", "formula"], [], "{formula}")

g_tel_keywords = ["true", "false", "final"]
g_tel_shift_variable = "__S"

class Interval:
    def __init__(self, left, right):
        self.left  = left
        self.right = right

    def before(self, other):
        return self.right < other.left

    def union(self, other):
        self.left  = min(self.left, other.left)
        self.right = max(self.right, other.right)

    def empty(self):
        return self.left >= self.right

    def __repr__(self):
        return "({!r},{!r})".format(self.left, self.right)

    def __str__(self):
        return "[{},{})".format(self.left, self.right)

class IntervalSet:
    def __init__(self, elements = []):
        self.__elements = []
        for x in elements:
            self.add(x)

    def __len__(self):
        return len(self.__elements)

    def add(self, x):
        y = Interval(x[0], x[1])
        if not y.empty():
            i = 0
            while i < len(self) and self.__elements[i].before(y):
                i += 1

            j = i
            while j < len(self) and not y.before(self.__elements[j]):
                y.union(self.__elements[j])
                j += 1

            if i == j:
                self.__elements.insert(i, y)
            else:
                self.__elements[i:j] = (y,)

    def __iter__(self):
        for x in self.__elements:
            yield x.left, x.right

    def __contains__(self, x):
        y = Interval(x[0], x[1])
        if y.empty():
            return True

        i = 0
        while i < len(self) and self.__elements[i].before(y):
            i += 1

        return i < len(self) and self.__elements[i].left <= y.left and y.right <= self.__elements[i].right

    def __repr__(self):
        return "IntervalSet({!r})".format(self.__elements)

    def __str__(self):
        return "{{{}}}".format(",".join((str(x) for x in self.__elements)))

# {{{1 parse_raw_formula

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
        ("&"  , unary):  (7, None),
        ("-"  , unary):  (7, None),
        ("+"  , binary): (6, left),
        ("-"  , binary): (6, left),
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
            self.__stack.append(_ast.TheoryFunction(b.location, operator, [b]))
        else:
            a = self.__stack.pop()
            l = {"begin": a.location["begin"], "end": b.location["end"]}
            self.__stack.append(_ast.TheoryFunction(l, operator, [a, b]))

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
                    raise RuntimeError("invalid operator in temporal formula: {}".format(_tf.str_location(x.location)))
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

# {{{1 theory_term -> term

class TheoryTermToTermTransformer(_tf.Transformer):
    """
    This class transforms a given theory term into a plain term.
    """
    def visit_TheoryTermSequence(self, x):
        """
        Theory term tuples are mapped to term tuples.
        """
        if x.sequence_type == _ast.TheorySequenceType.Tuple:
            return _ast.Function(x.location, "", [self(a) for a in x.arguments], False)
        else:
            raise RuntimeError("invalid term: {}".format(_tf.str_location(x.location)))

    def visit_TheoryFunction(self, x):
        """
        Theory functions are mapped to functions.

        If the function name refers to a temporal operator, an exception is thrown.
        """
        isnum = lambda y: y.type == _ast.ASTType.Symbol and y.symbol.type == _clingo.SymbolType.Number
        if x.name == "-" and len(x.arguments) == 1:
            rhs = self(x.arguments[0])
            if isnum(rhs):
                return _ast.Symbol(x.location, _clingo.Number(-rhs.symbol.number))
            else:
                return _ast.UnaryOperation(x.location, _ast.UnaryOperator.Minus, rhs)
        elif (x.name == "+" or x.name == "-") and len(x.arguments) == 2:
            lhs = self(x.arguments[0])
            rhs = self(x.arguments[1])
            op  = _ast.BinaryOperator.Plus if x.name == "+" else _ast.BinaryOperator.Minus
            if isnum(lhs) and isnum(rhs):
                lhs = lhs.symbol.number
                rhs = rhs.symbol.number
                return _ast.Symbol(x.location, _clingo.Number(lhs + rhs if x.name == "+" else lhs - rhs))
            else:
                return _ast.BinaryOperation(x.location, op, lhs, rhs)
        elif x.name == "-" and len(x.arguments) == 2:
            return _ast.BinaryOperation(x.location, _ast.BinaryOperator.Minus, self(x.arguments[0]), self(x.arguments[1]))
        elif (x.name, TheoryParser.binary) in TheoryParser.table or (x.name, TheoryParser.unary) in TheoryParser.table:
            raise RuntimeError("invalid term: {}".format(_tf.str_location(x.location)))
        else:
            return _ast.Function(x.location, x.name, [self(a) for a in x.arguments], False)

    def visit_TheoryUnparsedTerm(self, x):
        """
        Unparsed term are first parsed and then handled by the transformer.
        """
        return self.visit(parse_raw_formula(x))

def theory_term_to_term(x):
    """
    Convert the given theory term into a term.
    """
    return TheoryTermToTermTransformer()(x)

# {{{1 theory_term -> symbolic_atom

class TheoryTermToAtomTransformer(_tf.Transformer):
    """
    Turns the given theory term into an atom.
    """

    def __atom(self, location, positive, name, arguments):
        """
        Helper function to create an atom.

        Arguments:
        location --  Location to use.
        positive --  Classical sign of the atom.
        name     --  The name of the atom.
        arguments -- The arguments of the atom.
        """
        ret = _ast.Function(location, name, arguments, False)
        if not positive:
            ret = _ast.UnaryOperation(location, _ast.UnaryOperator.Minus, ret)
        return _ast.SymbolicAtom(ret)

    def visit_Symbol(self, x, positive):
        """
        Maps functions to atoms.

        Every other symbol causes a runtime error.

        Arguments:
        x        -- The theory term to translate.
        positive -- The classical sign of the atom.
        """
        symbol = x.symbol
        if x.symbol.type == _clingo.SymbolType.Function and len(symbol.name) > 0:
            return self.__atom(x.location, positive == symbol.positive, symbol.name, [_ast.Symbol(x.location, a) for a in symbol.arguments])
        else:
            raise RuntimeError("invalid temporal formula in rule head: {}".format(_tf.str_location(x.location)))

    def visit_Variable(self, x, positive):
        """
        Raises an error.
        """
        raise RuntimeError("invalid temporal formula in rule head: {}".format(_tf.str_location(x.location)))


    def visit_TheoryTermSequence(self, x, positive):
        """
        Raises an error.
        """
        raise RuntimeError("invalid temporal formula in rule head: {}".format(_tf.str_location(x.location)))

    def visit_TheoryFunction(self, x, positive):
        """
        Maps theory functions to atoms.

        If the function name refers to a temporal operator, an exception is thrown.
        """
        if x.name == "-":
            return self(x.arguments[0], not positive)
        elif (x.name, TheoryParser.binary) in TheoryParser.table or (x.name, TheoryParser.unary) in TheoryParser.table:
            raise RuntimeError("invalid term: {}".format(_tf.str_location(x.location)))
        else:
            return self.__atom(x.location, positive, x.name, [theory_term_to_term(a) for a in x.arguments])

    def visit_TheoryUnparsedTerm(self, x, positive):
        """
        Unparsed terms are first parsed and then handled by the transformer.
        """
        return self.visit(parse_raw_formula(x), positive)

def theory_term_to_atom(x, positive=True):
    """
    Convert the given theory term into an atom.
    """
    return TheoryTermToAtomTransformer()(x, positive)

# {{{1 theory transformers

class TheoryAtomTransformer(_tf.Transformer):
    """
    Transforms the given theory atom to be processed further.
    """

    def __init__(self, atoms):
        self.__atoms = atoms

    def __add_atom(self, x, rng):
        self.__atoms.append((theory_term_to_atom(x), rng))

    def __add_range(self, location, rng, left, right):
        def add(a, b):
            if a == 0:
                return b
            elif b == 0:
                return a
            elif a == float("inf") or b == float("inf"):
                return float("inf")
            elif isinstance(a, _Number) and isinstance(b, _Number):
                return a + b
            else:
                lhs = _ast.Symbol(location, _clingo.Number(a)) if isinstance(a, _Number) else a
                rhs = _ast.Symbol(location, _clingo.Number(b)) if isinstance(b, _Number) else b
                return _clingo.ast.BinaryOperation(location, _ast.BinaryOperator.Plus, lhs, rhs)

        return add(left, rng[0]), add(right, rng[1])

    def visit_Symbol(self, x, rng):
        self.__add_atom(x, rng)
        return x

    def visit_Variable(self, x, rng):
        """
        Raises an error.
        """
        raise RuntimeError("invalid temporal formula in rule head: {}".format(_tf.str_location(x.location)))

    def visit_TheoryTermSequence(self, x, rng):
        """
        Raises an error.
        """
        raise RuntimeError("invalid temporal formula in rule head: {}".format(_tf.str_location(x.location)))

    def visit_TheoryUnparsedTerm(self, x, rng):
        """
        Unparsed terms are first parsed and then handled by the transformer.
        """
        return self.visit(parse_raw_formula(x), rng)

    def visit_TheoryFunction(self, x, rng):
        """
        Transforms the given theory function into a temporal formula.
        """
        is_binary = (x.name, TheoryParser.binary) in TheoryParser.table and len(x.arguments) == 2
        is_unary  = (x.name, TheoryParser.unary) in TheoryParser.table and len(x.arguments) == 1
        if is_unary or is_binary:
            if x.name == "-":
                self.__add_atom(x, rng)
                return x
            elif x.name == "~":
                return x

            lhs = None if is_unary else x.arguments[0]
            rhs = x.arguments[0 if is_unary else 1]

            if x.name == ">" or x.name == ">:":
                if lhs is None:
                    lhs = 1
                else:
                    lhs = theory_term_to_term(x.arguments[0])
                    if lhs.type == _ast.ASTType.Symbol and lhs.symbol.type == _clingo.SymbolType.Number:
                        lhs = lhs.symbol.number
                self(rhs, self.__add_range(x.location, rng, lhs, lhs))
            elif x.name == "&" and lhs is None:
                if rhs.type != _ast.ASTType.Symbol or len(rhs.symbol.arguments) != 0 or rhs.symbol.name not in g_tel_keywords:
                    raise RuntimeError("invalid temporal formula in rule head: {}".format(_tf.str_location(x.location)))
            else:
                rng_left, rng_right = rng, rng
                if x.name == ">?" or x.name == ">*" or x.name == ">>":
                    rng_left = self.__add_range(x.location, rng, 0, float("inf"))
                    rng_right = rng_left
                elif x.name == ";>" or x.name == ";>:":
                    rng_right = self.__add_range(x.location, rng, 1, 1)
                if is_binary:
                    self(lhs, rng_left)
                self(rhs, rng_right)
        else:
            self.__add_atom(x, rng)

        return x

    def visit_TheoryAtomElement(self, x):
        """
        Transforms one elementary theory elements without conditions into formulas.
        """
        if len(x.tuple) != 1 or len(x.condition) != 0:
            raise RuntimeError("invalid temporal formula in rule head: {}".format(_tf.str_location(x.location)))
        x.tuple[0] = self(x.tuple[0], (0, 0))
        return x

    def visit_TheoryAtom(self, x):
        """
        Transforms the given theory atom to be processed further.

        The theory atom is renamed from tel to tel_head(__t) and the
        """
        if len(x.elements) != 1 or x.guard is not None:
            raise RuntimeError("invalid temporal formula in rule head: {}".format(_tf.str_location(x.location)))
        x.term.name = "tel_head"
        x.elements[0] = self(x.elements[0])
        return x

def transform_theory_atom(x):
    """
    Transforms the given theory atom.
    """
    atoms = []
    atom = TheoryAtomTransformer(atoms)(x)

    # maps atoms to a set of numeric ranges
    numeric = {}
    # maps ranges to a set of symbolic ranges
    other = {}

    # add to symbolic ranges converting numeric ranges
    def add(atm, lhs, rhs):
        if isinstance(lhs, _Number):
            lhs = _ast.Symbol(atom.location, _clingo.Number(lhs))
        if rhs == float("inf"):
            rhs = _ast.Symbol(atom.location, _clingo.Supremum)
        elif isinstance(rhs, _Number):
            rhs = _ast.Symbol(atom.location, _clingo.Number(rhs))

        rng = (lhs, rhs)
        other.setdefault(str(rng), (rng, {}))[1].setdefault(str(atm), atm)

    # split into numeric and symbolic ranges
    for atm, (lhs, rhs) in atoms:
        if isinstance(lhs, _Number) and isinstance(rhs, _Number):
            numeric.setdefault(str(atm), (atm, IntervalSet()))[1].add((lhs, rhs+1))
        else:
            add(atm, lhs, rhs)

    # add combined numeric ranges as symbolic ranges
    for atm, rngs in numeric.values():
        for lhs, rhs in rngs:
            add(atm, lhs, rhs-1)

    # flatten symbolic ranges into a list
    ranges = []
    for _, (rng, atoms) in sorted(other.items(), key=_itemgetter(0)):
        ranges.append((rng, [atm for _, atm in sorted(atoms.items(), key=_itemgetter(0))]))

    return atom, ranges

# {{{1 get_variables

class VariablesVisitor(_tf.Transformer):
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
        self.__variables[str(x)] = x
        return x

def get_variables(x):
    """
    Gets all variables in a formula.
    """
    v = {}
    VariablesVisitor(v)(x)
    return [val for _, val in sorted(v.items(), key=lambda x: x[0])]

# {{{1 shift_tel_formula

class ShiftTransformer(_tf.Transformer):
    def __init__(self, rules, aux):
        self.__rules = rules
        self.__aux = aux

    def visit_TelNext(self, x, start):
        loc = x.location

        sym = lambda v: _ast.Symbol(loc, _clingo.Function(v, []))
        num = lambda v: _ast.Symbol(loc, _clingo.Number(v))
        var = lambda v: _ast.Variable(loc, v)
        com = lambda v: TelComparison(loc, t_lhs, v, start)

        t_lhs = num(1) if x.lhs is None else x.lhs
        rhs   = self(x.rhs, _ast.BinaryOperation(loc, _ast.BinaryOperator.Plus, start, t_lhs))
        t_lhs = _ast.BinaryOperation(loc, _ast.BinaryOperator.Minus, t_lhs, sym(_tf.g_time_parameter_name))
        t_lhs = _ast.BinaryOperation(loc, _ast.BinaryOperator.Plus, t_lhs, var(g_tel_shift_variable))

        nxt = TelNext(x.location, term_to_theory_term(t_lhs), x.rhs, x.weak)
        prv = TelFormula(x.location, _ast.TheoryFunction(x.location, "<", [term_to_theory_term(_ast.UnaryOperation(x.location, _ast.UnaryOperator.Minus, t_lhs)), formula_to_theory_term(x.rhs)]))
        frm = lambda v: TelFormula(x.location, formula_to_theory_term(TelNegation(x.location, TelNegation(x.location, v))))

        cur = TelClause(loc, [rhs, com(_ast.ComparisonOperator.NotEqual)], False)
        fut = TelClause(loc, [frm(nxt), com(_ast.ComparisonOperator.LessEqual)], False)
        pst = TelClause(loc, [frm(prv), com(_ast.ComparisonOperator.GreaterEqual)], False)
        return TelClause(loc, [pst, cur, fut], True)

    def visit_TelUntil(self, x):
        raise RuntimeError("visit_TelUntil: implement me...")

def shift_tel_formula(x, aux):
    rules = []
    x = ShiftTransformer(rules, aux)(x, _ast.Symbol(x.location, _clingo.Number(0)))
    return x, rules

# {{{1 transform_head

def factor_out_tel_formula(x):
    if x.type == "TelClause":
        if x.conjunctive:
            ret = []
            for y in x.elements:
                ret.extend(factor_out_tel_formula(y))
        else:
            ret = factor_out_tel_formula(x.elements[0])
            for y in x.elements[1:]:
                ret = [a + b for b in factor_out_tel_formula(y) for a in ret]
        return ret
    else:
        return [[x]]

def shift_literal(literal, head, body):
    """
    ~ ~ F ->     not &tel { F } # body
    ~ F   -> not not &tel { F } # body
    atom  -> atom               # head
    a > b -> not a > b          # body

    This should be everything!!!
    """
    if literal.type == "TelFormula":
        n = 0
        formula = literal.formula
        while formula.type == _ast.ASTType.TheoryFunction and formula.name == "~":
            formula = formula.arguments[0]
            n += 1
        assert(n > 0)
        sign = _ast.Sign.Negation if n % 2 == 0 else _ast.Sign.DoubleNegation
        body.append(_ast.Literal(literal.location, sign, theory_term_to_theory_atom(formula)))
    elif literal.type == "TelAtom":
        atom = _ast.Function(literal.location, literal.name, literal.arguments + [_ast.Symbol(literal.location, _clingo.Function(_tf.g_time_parameter_name))], False)
        if not literal.positive:
            atom = _ast.UnaryOperation(literal.location, _ast.UnaryOperator, atom)
        head.append(_ast.Literal(literal.location, _ast.Sign.NoSign, _ast.SymbolicAtom(atom)))
    elif literal.type == "TelComparison":
        body.append(_ast.Literal(literal.location, _ast.Sign.Negation, _ast.Comparison(literal.operator, literal.lhs, literal.rhs)))
    else:
        raise RuntimeError("cannot happen")

# TODO: change completely
# - introduce an auxiliary external atom per step that never becomes true
# - extract head atoms
# - attach time step and change the atom name
class HeadTransformer:
    def __init__(self):
        self.__num_aux = 0

    def __aux_atom(self, location, variables, inc=1):
        self.__num_aux += inc
        return _ast.Literal(location, _ast.Sign.NoSign, _ast.SymbolicAtom(_ast.Function(location, "__aux_{}".format(self.__num_aux - 1), variables, False)))

    def transform(self, atom):
        # TODO: reimplement
        """
        formula = theory_atom_to_formula(atom)
        rules = []
        # TODO: a time parameter has to be attached to the atom
        variables = get_variables(formula)
        atom  = self.__aux_atom(atom.location, variables + [_ast.Symbol(atom.location, _clingo.Function(_tf.g_time_parameter_name))])
        batom = self.__aux_atom(atom.location, variables + [_ast.Variable(atom.location, g_tel_shift_variable)], inc=0)
        shifted, rules = shift_tel_formula(formula, atom)
        for clause in factor_out_tel_formula(shifted):
            #print ([str(lit) for lit in clause])
            head, body = [], [batom]
            # TODO: the aux atom has to be added to the body
            for lit in clause:
                shift_literal(lit, head, body)
            if len(head) == 1:
                head = head[0]
            else:
                head = _ast.Disjunction(atom.location, [_ast.ConditionalLiteral(atom.location, x, []) for x in head])
            rules.append(_ast.Rule(atom.location, head, body))
        return atom, rules
        """

