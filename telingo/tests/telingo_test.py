import unittest
import clingo
import telingo
import telingo.transformers as transformers

def parse_model(m):
    ret = []
    for sym in m.symbols(shown=True):
        if not sym.name.startswith("__"):
            ret.append(sym)
    return list(map(str, sorted(ret)))

def solve(s, imin=0):
    r = []
    imax  = 20
    prg = clingo.Control(['0'], message_limit=0)
    with prg.builder() as b:
        future_sigs, reground_parts = transformers.transform([s], b.add)
    telingo.imain(prg, future_sigs, reground_parts, lambda m, s: r.append(parse_model(m)), imax = 20, imin=imin)
    return sorted(r)

class TestMain(unittest.TestCase):
    def test_simple(self):
        self.assertEqual(solve("p."), [['p(0)']])
        self.assertEqual(solve("p :- q. {q}."), [[], ['p(0)', 'q(0)']])
        self.assertEqual(solve("p(1..2). q(X) :- p(X)."), [['p(1,0)', 'p(2,0)', 'q(1,0)', 'q(2,0)']])
        self.assertEqual(solve("p(1;2)."), [['p(1,0)', 'p(2,0)']])
        self.assertEqual(solve("p(1;2,3)."), [['p(1,0)', 'p(2,3,0)']])
        self.assertEqual(solve("{p : q}. q."), [['p(0)', 'q(0)'], ['q(0)']])
        self.assertEqual(solve("p : q. q."), [['p(0)', 'q(0)']])
        self.assertEqual(solve("r :- p : q. p. {q}."), [['p(0)', 'q(0)', 'r(0)'], ['p(0)', 'r(0)']])
        self.assertEqual(solve("r :- {p : q} >= 1. p. {q}."), [['p(0)'], ['p(0)', 'q(0)', 'r(0)']])

    def test_future(self):
        self.assertEqual(solve("p'."), [])
        self.assertEqual(solve("p' :- q. {q}."), [[]])
        self.assertEqual(solve("p' :- q. {q}. :- not q, __initial."), [['p(1)', 'q(0)']])
        self.assertEqual(solve("p'(1;2,3) :- __initial."), [['p(1,1)', 'p(2,3,1)']])

    def test_constraint(self):
        self.assertEqual(solve(":- p'."), [[]])
        self.assertEqual(solve(":- not p', __initial. {p}."), [['p(0)', 'p(1)'], ['p(1)']])
        self.assertEqual(solve(":- not p'', __initial. {p}."), [['p(0)', 'p(1)', 'p(2)'], ['p(0)', 'p(2)'], ['p(1)', 'p(2)'], ['p(2)']])

    def test_program(self):
        self.assertEqual(solve("#program static. p.", imin=2), [['p(0)'], ['p(0)', 'p(1)']])
        self.assertEqual(solve("#program initial. p.", imin=2), [['p(0)'], ['p(0)']])
        self.assertEqual(solve("#program final. p.", imin=2), [['p(0)'], ['p(1)']])
        self.assertEqual(solve("#program dynamic. p.", imin=2), [[], ['p(1)']])
