import unittest
import sys
import clingo
import telingo
from numbers import Number
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

def transform_theory_atom(s):
    atom, atoms = th.transform_theory_atom(parse_formula(s))
    tostr = lambda x: x if isinstance(x, Number) else str(x)
    return (str(atom), [(str(a), (tostr(l), tostr(r))) for a, (l, r) in atoms])

class TestHead(TestCase):
    def test_atom(self):
        self.assertEqual(theory_term_to_atom("a(1+2)"), "a(3)")
        self.assertEqual(theory_term_to_atom("a(1+a)"), "a((1+a))")
        self.assertEqual(theory_term_to_atom("a"), "a")
        self.assertEqual(theory_term_to_atom("-a"), "-a")
        self.assertEqual(theory_term_to_atom("- -a"), "a")
        self.assertEqual(theory_term_to_atom("a", False), "-a")
        self.assertEqual(theory_term_to_atom("-a", False), "a")
        self.assertEqual(theory_term_to_atom("a(X)"), "a(X)")
        self.assertEqual(theory_term_to_atom("a(X,x)"), "a(X,x)")
        self.assertEqual(theory_term_to_atom("a(X,-x)"), "a(X,-x)")

    def test_formula(self):
        inf = float("inf")
        self.assertEqual(transform_theory_atom(">a"), ('&tel_head { >(a) :  }', [('a', (1, 1))]))
        self.assertEqual(transform_theory_atom(">:a"), ('&tel_head { >:(a) :  }', [('a', (1, 1))]))
        self.assertEqual(transform_theory_atom("2>a"), ('&tel_head { >(2,a) :  }', [('a', (2, 2))]))
        self.assertEqual(transform_theory_atom("(-2)>a"), ('&tel_head { >((- 2),a) :  }', [('a', (-2, -2))]))
        self.assertEqual(transform_theory_atom("a>?b"), ('&tel_head { >?(a,b) :  }', [('a', (0, inf)), ('b', (0, inf))]))
        self.assertEqual(transform_theory_atom("> (a >? > b)"), ('&tel_head { >((a >? > b)) :  }', [('a', (1, inf)), ('b', (2, inf))]))
        self.assertEqual(transform_theory_atom("~a"), ('&tel_head { ~(a) :  }', []))
        self.assertEqual(transform_theory_atom("~ ~a"), ('&tel_head { ~(~(a)) :  }', []))
        self.assertEqual(transform_theory_atom("a & b"), ('&tel_head { &(a,b) :  }', [('a', (0, 0)), ('b', (0, 0))]))
        self.assertEqual(transform_theory_atom("a | b"), ('&tel_head { |(a,b) :  }', [('a', (0, 0)), ('b', (0, 0))]))
        self.assertEqual(transform_theory_atom("a ;> b"), ('&tel_head { ;>(a,b) :  }', [('a', (0, 0)), ('b', (1, 1))]))
        self.assertEqual(transform_theory_atom("a ;>: b"), ('&tel_head { ;>:(a,b) :  }', [('a', (0, 0)), ('b', (1, 1))]))
        self.assertEqual(transform_theory_atom("&true"), ('&tel_head { &(true) :  }', []))
        self.assertEqual(transform_theory_atom("&false"), ('&tel_head { &(false) :  }', []))
        self.assertEqual(transform_theory_atom("&final"), ('&tel_head { &(final) :  }', []))
        self.assertEqual(transform_theory_atom(">>a"), ('&tel_head { >>(a) :  }', [('a', (0, inf))]))
        self.assertEqual(transform_theory_atom("2+X>a"), ('&tel_head { >(+(2,X),a) :  }', [('a', ('(2+X)', '(2+X)'))]))

        # TODO: next combine the ranges

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
        # TODO: might become unnecessary
        self.assertEqual(str(th.get_variables(parse_atom("p(X,Y) | a(X,Z)"))), "[X, Y, Z]")

    def test_shift(self):
        """
        self.assertEqual(shift_formula("a"), ("a", []))
        l = '((1-__t)+__S)'
        m = '+(-(1,__t),__S)'
        self.assertEqual(shift_formula(">a"), ('((~(~(<(-({m}),a)))|({l}>=0))&(a|({l}!=0))&(~(~(>({m},a)))|({l}<=0)))'.format(l=l, m=m), []))
        """
