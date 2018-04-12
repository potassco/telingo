import unittest
import sys
import clingo
import telingo
import telingo.transformers.head as th

class TestCase(unittest.TestCase):
    def assertRaisesRegex(self, *args, **kwargs):
        return (self.assertRaisesRegexp(*args, **kwargs)
            if sys.version_info[0] < 3
            else unittest.TestCase.assertRaisesRegex(self, *args, **kwargs))

def parse_formula(s):
    ret = []
    prg = clingo.Control(message_limit=0)
    clingo.parse_program("&tel{{{}}}.".format(s), ret.append)
    return ret[-1].head

def parse_atom(s):
    return parse_formula(s).elements[0].tuple[0]

def transform_atom(s, positive=True):
    return str(th.theory_term_to_atom(parse_atom(s), positive))

def transform_formula(s):
    return str(th.theory_atom_to_formula(parse_formula(s)))

def shift_formula(s):
    f, r = th.shift_formula(th.theory_atom_to_formula(parse_formula(s)))
    return str(f), list(map(str, r))

class TestHead(TestCase):
    def test_atom(self):
        self.assertEqual(transform_atom("a"), "a")
        self.assertEqual(transform_atom("-a"), "-a")
        self.assertEqual(transform_atom("- -a"), "a")
        self.assertEqual(transform_atom("a", False), "-a")
        self.assertEqual(transform_atom("-a", False), "a")
        self.assertEqual(transform_atom("a(X)"), "a(X)")
        self.assertEqual(transform_atom("a(X,x)"), "a(X,x)")
        self.assertEqual(transform_atom("a(X,-x)"), "a(X,-x)")

    def test_formula(self):
        self.assertEqual(transform_formula(">a"), "(>a)")
        self.assertEqual(transform_formula(">:a"), "(>:a)")
        self.assertEqual(transform_formula("2>a"), "(2>a)")
        self.assertEqual(transform_formula("(-2)>a"), "(-2>a)")
        self.assertEqual(transform_formula("-2>a"), "(-2>a)")
        self.assertEqual(transform_formula("a>?b"), "(a>?b)")
        self.assertEqual(transform_formula("a>*b"), "(a>*b)")
        self.assertEqual(transform_formula("~a"), "(~a)")
        self.assertEqual(transform_formula("~ ~a"), "(~(~a))")
        self.assertEqual(transform_formula("a & b"), "(a&b)")
        self.assertEqual(transform_formula("a | b"), "(a|b)")
        self.assertEqual(transform_formula("a ;> b"), "(a&(>b))")
        self.assertEqual(transform_formula("a ;>: b"), "(a&(>:b))")
        self.assertEqual(transform_formula("&true"), "&true")
        self.assertEqual(transform_formula("&false"), "&false")
        self.assertEqual(transform_formula("&final"), "__final")
        self.assertEqual(transform_formula(">>a"), "(>*(__final|a))")

    def test_variables(self):
        self.assertEqual(str(th.get_variables(parse_atom("p(X,Y) | a(X,Z)"))), "[X, Y, Z]")

    def test_shift(self):
        self.assertEqual(shift_formula("a"), ("a", []))
