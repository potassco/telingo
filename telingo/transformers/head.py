"""
Module with functions to transform heads referring to the future.
"""

from .transformer import *
from collections import namedtuple

Atom = namedtuple("Atom", "location sign name arguments")
Literal = namedtuple("Literal", "location sign formula")

class TheoryParser:
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
        if len(self.__stack) < 2:
            return False
        priority, associativity = self.__priority_and_associativity(operator)
        previous_priority       = self.__priority(*self.__stack[-2])
        return previous_priority > priority or (previous_priority == priority and associativity)

    def __reduce(self):
        b = self.__stack.pop()
        operator, unary = self.__stack.pop()
        if unary:
            self.__stack.append(ast.TheoryFunction(b.location, operator, [b]))
        else:
            a = self.__stack.pop()
            l = {"begin": a.location["begin"], "end": b.location["end"]}
            self.__stack.append(ast.TheoryFunction(l, operator, [a, b]))

    def parse(self, x):
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

class HeadAtomTransformer(Transformer):
    def __init__(self):
        self.__parser = TheoryParser()

    def visit_TheoryAtomElement(self, x):
        if len(x.tuple) != 1 or len(x.condition) != 0:
            raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))
        return self.visit(x.tuple[0])

    def visit_Symbol(self, x):
        raise RuntimeError("implement me: symbol")

    def visit_TheoryUnparsedTerm(self, x):
        return self.visit(self.__parser.parse(x))

    def visit_TheoryFunction(self, x):
        raise RuntimeError("implement me: Theory Function")

    def visit_TheoryAtom(self, x):
        if len(x.elements) != 1 or x.guard is not None:
            raise RuntimeError("invalid temporal formula in rule head: {}".format(str_location(x.location)))
        return self.visit(x.elements[0])

    def visit(self, x, *args, **kwargs):
        # TODO: for debugging
        # print ("visited: {}".format(x))
        return Transformer.visit(self, x, *args, **kwargs)

class HeadTransformer:
    def __init__(self):
        self.__transformer = HeadAtomTransformer()

    def transform(self, atom):
        self.__transformer.visit(atom)
        raise RuntimeError("implement me: transform")

