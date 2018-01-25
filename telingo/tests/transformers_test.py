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

def transform(s, replace_future=False, fail_future=False, fail_past=False, disjunctive=False):
    a = {}
    t = transformers.TermTransformer(clingo.Function("t"), a)
    return str(t.visit(parse_term(s), replace_future, fail_future, fail_past, disjunctive)), a

class TestTermTransformer(unittest.TestCase):
    def test_keep_future(self):
        self.assertEqual(transform("p"), ("p(t)", {}))
        self.assertEqual(transform("p'p"), ("p'p(t)", {}))
        self.assertEqual(transform("'p"), ("p((t+-1))", {}))
        self.assertEqual(transform("''p"), ("p((t+-2))", {}))
        self.assertEqual(transform("p'"), ("p((t+1))", {}))
        self.assertEqual(transform("p''"), ("p((t+2))", {}))
        self.assertEqual(transform("'p''"), ("p((t+1))", {}))
        self.assertEqual(transform("''p'"), ("p((t+-1))", {}))
        self.assertEqual(transform("''p'(X,Y)"), ("p(X,Y,(t+-1))", {}))

    def test_replace_future(self):
        self.assertEqual(transform("p", True), ("p(t)", {}))
        self.assertEqual(transform("p'p", True), ("p'p(t)", {}))
        self.assertEqual(transform("'p", True), ("p((t+-1))", {}))
        self.assertEqual(transform("''p", True), ("p((t+-2))", {}))
        self.assertEqual(transform("p'", True), ("__future_p(1,(t+1))", {('__future_p', 0, False): [1]}))
        self.assertEqual(transform("p''", True), ("__future_p(2,(t+2))", {('__future_p', 0, False): [2]}))
        self.assertEqual(transform("'p''", True), ("__future_p(1,(t+1))", {('__future_p', 0, False): [1]}))
        self.assertEqual(transform("''p'", True), ("p((t+-1))", {}))
        self.assertEqual(transform("p'(X,Y)", True), ("__future_p(X,Y,1,(t+1))", {('__future_p', 2, False): [1]}))

    def test_fail(self):
        self.assertRaisesRegexp(RuntimeError, "past atoms not supported", transform, "'p", fail_past=True)
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform, "p'", fail_future=True)

    def test_pool(self):
        self.assertEqual(transform("p'(1;2,3)"), ("(p(1,(t+1));p(2,3,(t+1)))", {}))
