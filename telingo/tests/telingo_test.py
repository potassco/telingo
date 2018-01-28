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

def solve(s):
    r = []
    imax  = 20
    prg = clingo.Control(['0'], message_limit=0)
    with prg.builder() as b:
        future_sigs, reground_parts = transformers.transform([s], b.add)
    telingo.imain(prg, future_sigs, reground_parts, lambda m: r.append(parse_model(m)), imax = 20)
    return sorted(r)

class TestMain(unittest.TestCase):

    def test_simple(self):
        self.assertEqual(solve("p."), [['p(0)']])
        self.assertEqual(solve("p :- q. {q}."), [[], ['p(0)', 'q(0)']])
        # TODO: more...

    def test_future(self):
        self.assertEqual(solve("p'."), [])
        self.assertEqual(solve("p' :- q. {q}."), [[]])
        self.assertEqual(solve("p' :- q. {q}. :- not q, __initial."), [['p(1)', 'q(0)']])
        self.assertEqual(solve("q | p'. :- __initial, q."), [['p(1)', 'q(1)']])
        # TODO: more...

    def test_constraint(self):
        self.assertEqual(solve(":- p'."), [[]])
        # TODO: more...

    def test_static(self):
        # TODO: more...
        pass

    def test_initial(self):
        # TODO: more...
        pass

    def test_final(self):
        # TODO: more...
        pass

    def test_dynamic(self):
        # TODO: more...
        pass
