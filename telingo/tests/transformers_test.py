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
    def test_transform(self):
        self.assertEqual(transform("p"), ("p(t)", {}))
        self.assertEqual(transform("p'p"), ("p'p(t)", {}))
        self.assertEqual(transform("'p"), ("p((t-1))", {}))
