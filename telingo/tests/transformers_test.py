import unittest
import clingo
import clingo.ast as ast
import telingo.transformers as transformers

def parse_term(t):
    ret = [None]
    def extract_term(s):
        if s.type == ast.ASTType.Rule:
            ret[0] = s.head.atom.term
    clingo.parse_program("{}.".format(t), lambda s: extract_term(s))
    return ret[0]

def transform_term(s, replace_future=False, fail_future=False, fail_past=False, disjunctive=False):
    a = {}
    m = [0]
    t = transformers.TermTransformer(clingo.Function("t"), a)
    return str(t.visit(parse_term(s), replace_future, fail_future, fail_past, disjunctive, m)), a, m[0]

class TestTermTransformer(unittest.TestCase):
    def test_keep_future(self):
        self.assertEqual(transform_term("p"), ("p(t)", {}, 0))
        self.assertEqual(transform_term("p'p"), ("p'p(t)", {}, 0))
        self.assertEqual(transform_term("'p"), ("p((t+-1))", {}, 0))
        self.assertEqual(transform_term("''p"), ("p((t+-2))", {}, 0))
        self.assertEqual(transform_term("p'"), ("p((t+1))", {}, 1))
        self.assertEqual(transform_term("p''"), ("p((t+2))", {}, 2))
        self.assertEqual(transform_term("'p''"), ("p((t+1))", {}, 1))
        self.assertEqual(transform_term("''p'"), ("p((t+-1))", {}, 0))
        self.assertEqual(transform_term("''p'(X,Y)"), ("p(X,Y,(t+-1))", {}, 0))

    def test_replace_future(self):
        self.assertEqual(transform_term("p", True), ("p(t)", {}, 0))
        self.assertEqual(transform_term("p'p", True), ("p'p(t)", {}, 0))
        self.assertEqual(transform_term("'p", True), ("p((t+-1))", {}, 0))
        self.assertEqual(transform_term("''p", True), ("p((t+-2))", {}, 0))
        self.assertEqual(transform_term("p'", True), ("__future_p(1,(t+1))", {('__future_p', 0, False): [1]}, 0))
        self.assertEqual(transform_term("p''", True), ("__future_p(2,(t+2))", {('__future_p', 0, False): [2]}, 0))
        self.assertEqual(transform_term("'p''", True), ("__future_p(1,(t+1))", {('__future_p', 0, False): [1]}, 0))
        self.assertEqual(transform_term("''p'", True), ("p((t+-1))", {}, 0))
        self.assertEqual(transform_term("p'(X,Y)", True), ("__future_p(X,Y,1,(t+1))", {('__future_p', 2, False): [1]}, 0))

    def test_fail(self):
        self.assertRaisesRegexp(RuntimeError, "past atoms not supported", transform_term, "'p", fail_past=True)
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_term, "p'", fail_future=True)

    def test_pool(self):
        self.assertEqual(transform_term("p'(1;2,3)"), ("(p(1,(t+1));p(2,3,(t+1)))", {}, 1))

def transform_program(p):
    a = {}
    ret = []
    t = transformers.ProgramTransformer(clingo.Function("t"), a)
    clingo.parse_program(p, lambda s: ret.append(str(t.visit(s))))
    return ret

class TestProgramTransformer(unittest.TestCase):
    def test_rule(self):
        self.assertEqual(transform_program("p."), ['#program base(t).', 'p(t).'])
