import unittest
import clingo
import clingo.ast as ast
import telingo.transformers as transformers

transformers._future_prefix = "f_"
transformers._time_parameter_name = "t"
transformers._time_parameter_name_alt = "u"

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
        self.assertEqual(transform_term("p'", True), ("f_p(1,(t+1))", {('p', 0, 1): False}, 0))
        self.assertEqual(transform_term("p''", True), ("f_p(2,(t+2))", {('p', 0, 2): False}, 0))
        self.assertEqual(transform_term("'p''", True), ("f_p(1,(t+1))", {('p', 0, 1): False}, 0))
        self.assertEqual(transform_term("''p'", True), ("p((t+-1))", {}, 0))
        self.assertEqual(transform_term("p'(X,Y)", True), ("f_p(X,Y,1,(t+1))", {('p', 2, 1): False}, 0))

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
    def append(s):
        if s is not None:
            ret.append(str(s))
    clingo.parse_program(p, lambda s: append(t.visit(s)))
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
        self.assertEqual(transform_program("p'."), (['#program static(t).', 'f_p(1,(t+1)).'], {('p', 0, 1): False}, {}))
        self.assertRaisesRegexp(RuntimeError, "past atoms not supported", transform_program, "'p.")
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_program, "p :- p'.")
        # body aggregates
        self.assertEqual(transform_program("p :- {'p:q}."), (['#program static(t).', 'p(t) :- { p((t+-1)) : q(t) }.'], {}, {}))
        self.assertEqual(transform_program("p :- {p:'q}."), (['#program static(t).', 'p(t) :- { p(t) : q((t+-1)) }.'], {}, {}))
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_program, "p :- {p : q'}.")
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_program, "p :- {p' : q}.")
        # head aggregates
        self.assertEqual(transform_program("{p' : 'q}."), (['#program static(t).', '{ f_p(1,(t+1)) : q((t+-1)) }.'], {('p', 0, 1): False}, {}))
        self.assertEqual(transform_program("{not 'p : 'q}."), (['#program static(t).', '{ not p((t+-1)) : q((t+-1)) }.'], {}, {}))
        self.assertRaisesRegexp(RuntimeError, "past atoms not supported", transform_program, "{'p : q}.")
        self.assertRaisesRegexp(RuntimeError, "future atoms not supported", transform_program, "{p : q'}.")

    def test_constraint(self):
        # simple rules
        self.assertEqual(transform_program(":- p."), (['#program static(t).', '#false :- p(t).'], {}, {}))
        self.assertEqual(transform_program(":- 'p."), (['#program static(t).', '#false :- p((t+-1)).'], {}, {}))
        self.assertEqual(transform_program(":- p'."), (
            ['#program static(t).'], {},
            {('static', 1): [('#false :- p((t+1)); __final(u).', '#false :- p((t+1)).')]}))
        self.assertEqual(transform_program("not p :- p'."), (
            ['#program static(t).'], {},
            {('static', 1): [('not p(t) :- p((t+1)); __final(u).', 'not p(t) :- p((t+1)).')]}))
        self.assertEqual(transform_program("not 'p :- p'."), (
            ['#program static(t).'], {},
            {('static', 1): [('not p((t+-1)) :- p((t+1)); __final(u).', 'not p((t+-1)) :- p((t+1)).')]}))
        self.assertEqual(transform_program("not p' :- p'."), (
            ['#program static(t).'], {},
            {('static', 1): [('not p((t+1)) :- p((t+1)); __final(u).', 'not p((t+1)) :- p((t+1)).')]}))
        # body aggregates
        self.assertEqual(transform_program(":- {p':q'}."), (
            ['#program static(t).'], {},
            {('static', 1): [('#false :- { p((t+1)) : q((t+1)) }; __final(u).', '#false :- { p((t+1)) : q((t+1)) }.')]}))

def transform(p):
    r = []
    f, c = transformers.transform([p], lambda s: r.append(str(s)))
    return r, f, c

class TestTransform(unittest.TestCase):
    def test_transform(self):
        self.assertEqual(transform("p."), (['#program static(t).', 'p(t).'], [], []))
        self.assertEqual(transform("p'."), (
            ['#program static(t).',
             'f_p(1,(t+1)).',
             '#program static(t).',
             'p(t) :- f_p(1,t).'],
            [('f_p', 2)], []))
        self.assertEqual(transform("p'|q."), (
            ['#program static(t).',
             'q(t) : ; f_p(1,(t+1)) : .',
             '#program static(t).',
             '#external p((t+1)) : f_p(1,(t+1)).',
             'f_p(1,(t+1)) :- p((t+1)).',
             'p(t) :- f_p(1,t).'],
            [('f_p', 2)], []))
        self.assertEqual(transform("p'. p'|q."), (
            ['#program static(t).',
             'f_p(1,(t+1)).',
             'q(t) : ; f_p(1,(t+1)) : .',
             '#program static(t).',
             '#external p((t+1)) : f_p(1,(t+1)).',
             'f_p(1,(t+1)) :- p((t+1)).',
             'p(t) :- f_p(1,t).'],
            [('f_p', 2)], []))
        self.assertEqual(transform("p'(X)|q."), (
            ['#program static(t).',
             'q(t) : ; f_p(X,1,(t+1)) : .',
             '#program static(t).',
             '#external p(X0,(t+1)) : f_p(X0,1,(t+1)).',
             'f_p(X0,1,(t+1)) :- p(X0,(t+1)).',
             'p(X0,t) :- f_p(X0,1,t).'],
            [('f_p', 3)], []))
        self.assertEqual(transform(":- p''."), (
            ['#program static(t).',
             '#program static_0_1(t,u).',
             '#false :- p((t+2)); __final(u).',
             '#program static_2(t,u).',
             '#false :- p((t+2)).'], [],
            [('static', 'static_0_1', range(0, 2)),
             ('static', 'static_2',   range(2, 3))]))

