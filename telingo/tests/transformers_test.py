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

def parse_rule(r):
    ret = []
    clingo.parse_program(r, lambda s: ret.append(s))
    return ret[-1]

def transform_program(p):
    a = {}
    c = {}
    ret = []
    t = transformers.ProgramTransformer(clingo.Function("t"), a, c)
    clingo.parse_program(p, lambda s: ret.append(str(t.visit(s))))
    return (ret, a, {key: [(str(r), str(l)) for r, l in stms] for key, stms in c.items()})

class TestClassify(unittest.TestCase):
    def test_constraint(self):
        self.assertTrue(transformers.is_constraint(parse_rule(":-p.")))
        self.assertTrue(transformers.is_constraint(parse_rule("#false :- p.")))
        self.assertTrue(transformers.is_constraint(parse_rule("not q :- p.")))
        self.assertTrue(transformers.is_constraint(parse_rule("not not q :- p.")))
        self.assertFalse(transformers.is_constraint(parse_rule("p.")))
        self.assertFalse(transformers.is_constraint(parse_rule("{p}.")))
        self.assertFalse(transformers.is_constraint(parse_rule("a | b.")))
        self.assertFalse(transformers.is_constraint(parse_rule("not a:#true.")))

    def test_disjunction(self):
        self.assertTrue(transformers.is_disjunction(parse_rule("a|b.")))
        self.assertTrue(transformers.is_disjunction(parse_rule("a:#true.")))
        self.assertFalse(transformers.is_disjunction(parse_rule("a.")))
        self.assertFalse(transformers.is_disjunction(parse_rule(":-a.")))

class TestProgramTransformer(unittest.TestCase):
    def test_rule(self):
        # simple rules
        self.assertEqual(transform_program("p."), (['#program static(t).', 'p(t).'], {}, {}))
        self.assertEqual(transform_program("p :- 'p."), (['#program static(t).', 'p(t) :- p((t+-1)).'], {}, {}))
        self.assertEqual(transform_program("p'."), (['#program static(t).', '__future_p(1,(t+1)).'], {('__future_p', 0, False): [1]}, {}))
        self.assertRaisesRegexp(RuntimeError, "past atoms not supported", transform_program, "'p.")
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_program, "p :- p'.")
        # body aggregates
        self.assertEqual(transform_program("p :- {'p:q}."), (['#program static(t).', 'p(t) :- { p((t+-1)) : q(t) }.'], {}, {}))
        self.assertEqual(transform_program("p :- {p:'q}."), (['#program static(t).', 'p(t) :- { p(t) : q((t+-1)) }.'], {}, {}))
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_program, "p :- {p : q'}.")
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_program, "p :- {p' : q}.")
        # head aggregates
        self.assertEqual(transform_program("{p' : 'q}."), (['#program static(t).', '{ __future_p(1,(t+1)) : q((t+-1)) }.'], {('__future_p', 0, False): [1]}, {}))
        self.assertEqual(transform_program("{not 'p : 'q}."), (['#program static(t).', '{ not p((t+-1)) : q((t+-1)) }.'], {}, {}))
        self.assertRaisesRegexp(RuntimeError, "past atoms not supported", transform_program, "{'p : q}.")
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_program, "{p : q'}.")

    def test_constraint(self):
        # simple rules
        self.assertEqual(transform_program(":- p."), (['#program static(t).', '#false :- p(t).'], {}, {}))
        self.assertEqual(transform_program(":- 'p."), (['#program static(t).', '#false :- p((t+-1)).'], {}, {}))
        self.assertEqual(transform_program(":- p'."), (
            ['#program static(t).', '#false :- p((t+1)); __final(t).'], {},
            {('static', 't', 1): [('#false :- p((t+1)); __final(t).', '#false :- p((t+1)).')]}))
        self.assertEqual(transform_program("not p :- p'."), (
            ['#program static(t).', 'not p(t) :- p((t+1)); __final(t).'], {},
            {('static', 't', 1): [('not p(t) :- p((t+1)); __final(t).', 'not p(t) :- p((t+1)).')]}))
        self.assertEqual(transform_program("not 'p :- p'."), (
            ['#program static(t).', 'not p((t+-1)) :- p((t+1)); __final(t).'], {},
            {('static', 't', 1): [('not p((t+-1)) :- p((t+1)); __final(t).', 'not p((t+-1)) :- p((t+1)).')]}))
        self.assertEqual(transform_program("not p' :- p'."), (
            ['#program static(t).', 'not p((t+1)) :- p((t+1)); __final(t).'], {},
            {('static', 't', 1): [('not p((t+1)) :- p((t+1)); __final(t).', 'not p((t+1)) :- p((t+1)).')]}))
        # body aggregates
        self.assertEqual(transform_program(":- {p':q'}."), (
            ['#program static(t).', '#false :- { p((t+1)) : q((t+1)) }; __final(t).'], {},
            {('static', 't', 1): [('#false :- { p((t+1)) : q((t+1)) }; __final(t).', '#false :- { p((t+1)) : q((t+1)) }.')]}))

def transform(p):
    r, f, c = transformers.transform([p])
    return [str(s) for s in r], f, c

class TestTransform(unittest.TestCase):
    def test_transform(self):
        self.assertEqual(transform("p."), (['#program static(__t).', 'p(__t).'], [], []))

