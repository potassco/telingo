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

def transform(s, head=False):
    a = {}
    t = transformers.TermTransformer(clingo.Function("t"), a)
    return str(t.visit(parse_term(s), head)), a

class TestTermTransformer(unittest.TestCase):
    def test_body(self):
        self.assertEqual(transform("p"), ("p(t)", {}))
        self.assertEqual(transform("p'p"), ("p'p(t)", {}))
        self.assertEqual(transform("'p"), ("p((t+-1))", {}))
        self.assertEqual(transform("''p"), ("p((t+-2))", {}))
        self.assertEqual(transform("p'"), ("p((t+1))", {}))
        self.assertEqual(transform("p''"), ("p((t+2))", {}))
        self.assertEqual(transform("'p''"), ("p((t+1))", {}))
        self.assertEqual(transform("''p'"), ("p((t+-1))", {}))

    def test_head(self):
        self.assertEqual(transform("p", True), ("p(t)", {}))
        self.assertEqual(transform("p'p", True), ("p'p(t)", {}))
        self.assertEqual(transform("'p", True), ("p((t+-1))", {}))
        self.assertEqual(transform("''p", True), ("p((t+-2))", {}))
        self.assertEqual(transform("p'", True), ("__future_p((t+1))", {}))
        self.assertEqual(transform("p''", True), ("p((t+2))", {}))
        self.assertEqual(transform("'p''", True), ("p((t+1))", {}))
        self.assertEqual(transform("''p'", True), ("p((t+-1))", {}))
