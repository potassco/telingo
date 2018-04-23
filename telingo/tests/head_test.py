import unittest
import sys
import clingo
import telingo
from telingo.transformers import head as th

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

def theory_term_to_atom(s, positive=True):
    return str(th.theory_term_to_atom(parse_atom(s), positive))

class TestHead(TestCase):
    def test_atom(self):
        self.assertEqual(theory_term_to_atom("a(1+2)"), "a((1+2))")
        self.assertEqual(theory_term_to_atom("a"), "a")
        self.assertEqual(theory_term_to_atom("-a"), "-a")
        self.assertEqual(theory_term_to_atom("- -a"), "a")
        self.assertEqual(theory_term_to_atom("a", False), "-a")
        self.assertEqual(theory_term_to_atom("-a", False), "a")
        self.assertEqual(theory_term_to_atom("a(X)"), "a(X)")
        self.assertEqual(theory_term_to_atom("a(X,x)"), "a(X,x)")
        self.assertEqual(theory_term_to_atom("a(X,-x)"), "a(X,-x)")

    def test_formula(self):
        """
        self.assertEqual(theory_atom_to_formula(">a"), "(>a)")
        self.assertEqual(theory_atom_to_formula(">:a"), "(>:a)")
        self.assertEqual(theory_atom_to_formula("2>a"), "(2>a)")
        self.assertEqual(theory_atom_to_formula("(-2)>a"), "(-2>a)")
        self.assertEqual(theory_atom_to_formula("-2>a"), "(-2>a)")
        self.assertEqual(theory_atom_to_formula("a>?b"), "(a>?b)")
        self.assertEqual(theory_atom_to_formula("a>*b"), "(a>*b)")
        self.assertEqual(theory_atom_to_formula("~a"), "(~a)")
        self.assertEqual(theory_atom_to_formula("~ ~a"), "(~(~a))")
        self.assertEqual(theory_atom_to_formula("a & b"), "(a&b)")
        self.assertEqual(theory_atom_to_formula("a | b"), "(a|b)")
        self.assertEqual(theory_atom_to_formula("a ;> b"), "(a&(>b))")
        self.assertEqual(theory_atom_to_formula("a ;>: b"), "(a&(>:b))")
        self.assertEqual(theory_atom_to_formula("&true"), "&true")
        self.assertEqual(theory_atom_to_formula("&false"), "&false")
        self.assertEqual(theory_atom_to_formula("&final"), "__final")
        self.assertEqual(theory_atom_to_formula(">>a"), "(>*(__final|a))")

        self.assertEqual(formula_to_theory_term(">a"), ">(a)")
        self.assertEqual(formula_to_theory_term(">:a"), ">:(a)")
        self.assertEqual(formula_to_theory_term("2>a"), ">(2,a)")
        self.assertEqual(formula_to_theory_term("(-2)>a"), ">(-(2),a)")
        self.assertEqual(formula_to_theory_term("-2>a"), ">(-(2),a)")
        self.assertEqual(formula_to_theory_term("a>?b"), ">?(a,b)")
        self.assertEqual(formula_to_theory_term("a>*b"), ">*(a,b)")
        self.assertEqual(formula_to_theory_term("~a"), "~(a)")
        self.assertEqual(formula_to_theory_term("~ ~a"), "~(~(a))")
        self.assertEqual(formula_to_theory_term("a & b"), "&(a,b)")
        self.assertEqual(formula_to_theory_term("a | b"), "|(a,b)")
        self.assertEqual(formula_to_theory_term("a ;> b"), "&(a,>(b))")
        self.assertEqual(formula_to_theory_term("a ;>: b"), "&(a,>:(b))")
        self.assertEqual(formula_to_theory_term("&true"), "&(true)")
        self.assertEqual(formula_to_theory_term("&false"), "&(false)")
        self.assertEqual(formula_to_theory_term("&final"), "__final")
        self.assertEqual(formula_to_theory_term(">>a"), ">*(|(__final,a))")

        self.assertEqual(formula_to_theory_atom(">a"), "&tel(__t) { >(a) :  }")
        """

    def test_interval_set(self):
        self.assertEqual(str(th.IntervalSet([(1,1)])), "{}")
        self.assertEqual(str(th.IntervalSet([(1,2)])), "{[1,2)}")
        self.assertEqual(str(th.IntervalSet([(1,2), (3,4)])), "{[1,2),[3,4)}")
        self.assertEqual(str(th.IntervalSet([(1,2), (3,4), (-1,0)])), "{[-1,0),[1,2),[3,4)}")
        self.assertEqual(str(th.IntervalSet([(1,2),(3,4),(2,3)])), "{[1,4)}")
        self.assertEqual(str(th.IntervalSet([(1,2),(3,4),(5,7),(0,10)])), "{[0,10)}")
        self.assertIn((0,0), th.IntervalSet([(1,2),(3,4)]))
        self.assertIn((1,2), th.IntervalSet([(1,2),(3,4)]))
        self.assertIn((3,4), th.IntervalSet([(1,2),(3,5)]))
        self.assertIn((4,5), th.IntervalSet([(1,2),(3,5)]))
        self.assertNotIn((1,4), th.IntervalSet([(1,2),(3,4)]))

    def test_variables(self):
        self.assertEqual(str(th.get_variables(parse_atom("p(X,Y) | a(X,Z)"))), "[X, Y, Z]")

    def test_shift(self):
        """
        self.assertEqual(shift_formula("a"), ("a", []))
        l = '((1-__t)+__S)'
        m = '+(-(1,__t),__S)'
        self.assertEqual(shift_formula(">a"), ('((~(~(<(-({m}),a)))|({l}>=0))&(a|({l}!=0))&(~(~(>({m},a)))|({l}<=0)))'.format(l=l, m=m), []))
        """
