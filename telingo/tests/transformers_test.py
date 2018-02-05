import unittest
import sys
import clingo
import clingo.ast as ast
import telingo.transformers as transformers

class TestCase(unittest.TestCase):
    def assertRaisesRegex(self, *args, **kwargs):
        return (self.assertRaisesRegexp(*args, **kwargs)
            if sys.version_info[0] < 3
            else unittest.TestCase.assertRaisesRegex(self, *args, **kwargs))

def parse_term(t):
    ret = [None]
    def extract_term(s):
        if s.type == ast.ASTType.Rule:
            ret[0] = s.head.atom.term
    clingo.parse_program("{}.".format(t), lambda s: extract_term(s))
    return ret[0]

def transform_term(s, replace_future=False, fail_future=False, fail_past=False):
    a = set()
    m = [0]
    t = transformers.TermTransformer(a)
    return str(t.visit(parse_term(s), replace_future, fail_future, fail_past, m)), a, m[0]

class TestTermTransformer(TestCase):
    def test_keep_future(self):
        self.assertEqual(transform_term("p"), ("p(__t)", set(), 0))
        self.assertEqual(transform_term("p'p"), ("p'p(__t)", set(), 0))
        self.assertEqual(transform_term("'p"), ("p((__t+-1))", set(), 0))
        self.assertEqual(transform_term("''p"), ("p((__t+-2))", set(), 0))
        self.assertEqual(transform_term("p'"), ("p((__t+1))", set(), 1))
        self.assertEqual(transform_term("p''"), ("p((__t+2))", set(), 2))
        self.assertEqual(transform_term("'p''"), ("p((__t+1))", set(), 1))
        self.assertEqual(transform_term("''p'"), ("p((__t+-1))", set(), 0))
        self.assertEqual(transform_term("''p'(X,Y)"), ("p(X,Y,(__t+-1))", set(), 0))

    def test_replace_future(self):
        self.assertEqual(transform_term("p", True), ("p(__t)", set(), 0))
        self.assertEqual(transform_term("p'p", True), ("p'p(__t)", set(), 0))
        self.assertEqual(transform_term("'p", True), ("p((__t+-1))", set(), 0))
        self.assertEqual(transform_term("''p", True), ("p((__t+-2))", set(), 0))
        self.assertEqual(transform_term("p'", True), ("__future_p(1,(__t+1))", set([('p', 0, 1)]), 0))
        self.assertEqual(transform_term("p''", True), ("__future_p(2,(__t+2))", set([('p', 0, 2)]), 0))
        self.assertEqual(transform_term("'p''", True), ("__future_p(1,(__t+1))", set([('p', 0, 1)]), 0))
        self.assertEqual(transform_term("''p'", True), ("p((__t+-1))", set(), 0))
        self.assertEqual(transform_term("p'(X,Y)", True), ("__future_p(X,Y,1,(__t+1))", set([('p', 2, 1)]), 0))

    def test_fail(self):
        self.assertRaisesRegex(RuntimeError, "past atoms not supported", transform_term, "'p", fail_past=True)
        self.assertRaisesRegex(RuntimeError, "future atoms not supported", transform_term, "p'", fail_future=True)

    def test_pool(self):
        self.assertEqual(transform_term("p'(1;2,3)"), ("(p(1,(__t+1));p(2,3,(__t+1)))", set(), 1))

def parse_rule(r):
    ret = []
    clingo.parse_program(r, lambda s: ret.append(s))
    return ret[-1]

def transform_program(p):
    a = set()
    c = {}
    ret = []
    t = transformers.ProgramTransformer(a, c)
    def append(s):
        if s is not None:
            ret.append(str(s))
    clingo.parse_program(p, lambda s: append(t.visit(s)))
    return (ret, a, {key: [(str(r), str(l)) for r, l in stms] for key, stms in c.items()})

class TestClassify(TestCase):
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

    def test_normal(self):
        self.assertTrue(transformers.is_normal(parse_rule("a.")))
        self.assertTrue(transformers.is_normal(parse_rule("a :- b.")))
        self.assertFalse(transformers.is_normal(parse_rule("a:#true.")))
        self.assertFalse(transformers.is_normal(parse_rule("not a.")))
        self.assertFalse(transformers.is_normal(parse_rule("{a}.")))

class TestProgramTransformer(TestCase):
    def test_rule(self):
        # simple rules
        self.assertEqual(transform_program("p."), (['#program always(__t,__u).', 'p(__t).'], set(), {}))
        self.assertEqual(transform_program("p :- 'p."), (['#program always(__t,__u).', 'p(__t) :- p((__t+-1)).'], set(), {}))
        self.assertEqual(transform_program("p'."), (['#program always(__t,__u).', '__future_p(1,(__t+1)).'], set([('p', 0, 1)]), {}))
        self.assertRaisesRegex(RuntimeError, "past atoms not supported", transform_program, "'p.")
        self.assertRaisesRegex(RuntimeError, "future atoms not supported", transform_program, "p :- p'.")
        # body aggregates
        self.assertEqual(transform_program("p :- {'p:q}."), (['#program always(__t,__u).', 'p(__t) :- { p((__t+-1)) : q(__t) }.'], set(), {}))
        self.assertEqual(transform_program("p :- {p:'q}."), (['#program always(__t,__u).', 'p(__t) :- { p(__t) : q((__t+-1)) }.'], set(), {}))
        self.assertRaisesRegex(RuntimeError, "future atoms not supported", transform_program, "p :- {p : q'}.")
        self.assertRaisesRegex(RuntimeError, "future atoms not supported", transform_program, "p :- {p' : q}.")
        # head aggregates
        self.assertRaisesRegex(RuntimeError, "future atoms not supported", transform_program, "{p' : 'q}.")
        self.assertRaisesRegex(RuntimeError, "future atoms not supported", transform_program, "{not p' : 'q}.")
        self.assertEqual(transform_program("{not 'p : 'q}."), (['#program always(__t,__u).', '{ not p((__t+-1)) : q((__t+-1)) }.'], set(), {}))
        self.assertRaisesRegex(RuntimeError, "past atoms not supported", transform_program, "{'p : q}.")
        self.assertRaisesRegex(RuntimeError, "future atoms not supported", transform_program, "{p : q'}.")
        # head aggregates
        self.assertRaisesRegex(RuntimeError, "future atoms not supported", transform_program, "p'|q.")

    def test_constraint(self):
        # simple rules
        self.assertEqual(transform_program(":- p."), (['#program always(__t,__u).', '#false :- p(__t).'], set(), {}))
        self.assertEqual(transform_program(":- 'p."), (['#program always(__t,__u).', '#false :- p((__t+-1)).'], set(), {}))
        self.assertEqual(transform_program(":- p'."), (
            ['#program always(__t,__u).'], set(),
            {('always', 1): [('#false :- p((__t+1)); __final(__u).', '#false :- p((__t+1)).')]}))
        self.assertEqual(transform_program("not p :- p'."), (
            ['#program always(__t,__u).'], set(),
            {('always', 1): [('not p(__t) :- p((__t+1)); __final(__u).', 'not p(__t) :- p((__t+1)).')]}))
        self.assertEqual(transform_program("not 'p :- p'."), (
            ['#program always(__t,__u).'], set(),
            {('always', 1): [('not p((__t+-1)) :- p((__t+1)); __final(__u).', 'not p((__t+-1)) :- p((__t+1)).')]}))
        self.assertEqual(transform_program("not p' :- p'."), (
            ['#program always(__t,__u).'], set(),
            {('always', 1): [('not p((__t+1)) :- p((__t+1)); __final(__u).', 'not p((__t+1)) :- p((__t+1)).')]}))
        # body aggregates
        self.assertEqual(transform_program(":- {p':q'}."), (
            ['#program always(__t,__u).'], set(),
            {('always', 1): [('#false :- { p((__t+1)) : q((__t+1)) }; __final(__u).', '#false :- { p((__t+1)) : q((__t+1)) }.')]}))

    def test_theory(self):
        self.assertEqual(transform_program(":- &tel { a }."), (['#program always(__t,__u).', '#false :- &tel(__t) { a :  }.'], set(), {}))
        self.assertEqual(transform_program("a :- not &tel { a }."), (['#program always(__t,__u).', 'a(__t) :- not &tel(__t) { a :  }.'], set(), {}))
        self.assertEqual(transform_program("a :- not not &tel { a }."), (['#program always(__t,__u).', 'a(__t) :- not not &tel(__t) { a :  }.'], set(), {}))
        self.assertRaisesRegex(RuntimeError, "temporal formulas not supported", transform_program, "a :- &tel { a }.")
        self.assertRaisesRegex(RuntimeError, "temporal formulas not supported", transform_program, "&tel { a } :- a.")
        self.assertRaisesRegex(RuntimeError, "temporal formulas not supported", transform_program, "&tel { a } :- a.")
        self.assertRaisesRegex(RuntimeError, "invalid temporal formula", transform_program, ":- &tel { a : a }.")
        self.assertRaisesRegex(RuntimeError, "invalid temporal formula", transform_program, ":- &tel { }.")
        self.assertRaisesRegex(RuntimeError, "invalid temporal formula", transform_program, ":- &tel { a; b }.")

def transform(p):
    r = []
    def append(s):
        if s.type != ast.ASTType.TheoryDefinition:
            r.append(str(s))
    f, c = transformers.transform([p], append)
    return r, f, c

class TestTransform(unittest.TestCase):
    static = ['#program initial(__t,__u).',
              '__initial(__t).',
              '#program always(__t,__u).',
              '#external __final(__t).']
    parts  = [('always', 'always', range(0, 1)),
              ('dynamic', 'dynamic', range(0, 1)),
              ('initial', 'initial', range(0, 1))]

    def test_transform(self):
        self.assertEqual(transform("p."), (['#program always(__t,__u).', 'p(__t).'] + TestTransform.static, [], TestTransform.parts))
        self.assertEqual(transform("p'."), (
            ['#program always(__t,__u).',
             '__future_p(1,(__t+1)).',
             '#program always(__t,__u).',
             'p(__t) :- __future_p(1,__t).'] + TestTransform.static,
            [('__future_p', 2)], TestTransform.parts))
        self.assertEqual(transform("p(X)|q."), (
            ['#program always(__t,__u).',
             'q(__t) : ; p(X,__t) : .'] + TestTransform.static,
            [], TestTransform.parts))
        self.assertEqual(transform(":- p''."), (
            ['#program always(__t,__u).',
             '#program always_0_1(__t,__u).',
             '#false :- p((__t+2)); __final(__u).',
             '#program always_2(__t,__u).',
             '#false :- p((__t+2)).'] + TestTransform.static, [],
            [('always', 'always_0_1', range(0, 2)),
             ('always', 'always_2',   range(2, 3))] + TestTransform.parts))

