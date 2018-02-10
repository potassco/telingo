import unittest
import sys
import clingo
import telingo
import telingo.transformers as transformers

class TestCase(unittest.TestCase):
    def assertRaisesRegex(self, *args, **kwargs):
        return (self.assertRaisesRegexp(*args, **kwargs)
            if sys.version_info[0] < 3
            else unittest.TestCase.assertRaisesRegex(self, *args, **kwargs))

def parse_model(m, s, dual):
    ret = []
    for sym in m.symbols(shown=True):
        if not sym.name.startswith("__"):
            ret.append(sym)
    if dual:
        flip = lambda sym: clingo.Function(sym.name, sym.arguments[:-1] + [s - sym.arguments[-1].number], sym.positive)
        ret = [flip(sym) for sym in ret]
    return list(map(str, sorted(ret)))

def solve(s, imin=0, dual=False, always=True):
    r = []
    imax  = 20
    prg = clingo.Control(['0'], message_limit=0)
    with prg.builder() as b:
        future_sigs, reground_parts = transformers.transform([("#program always. " if always else "") + s], b.add)
    telingo.imain(prg, future_sigs, reground_parts, lambda m, s: r.append(parse_model(m, s, dual)), imax=20, imin=imin)
    return sorted(r)

class TestMain(TestCase):
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
        self.assertEqual(solve("{p}. :- &initial, not p."), [['p(0)']])
        self.assertEqual(solve("{p}. :- &final, not p."), [['p(0)']])
        self.assertEqual(solve("p. :- &final, &initial."), [['p(0)', 'p(1)']])
        self.assertEqual(solve("&initial :- a. {a}. q. :- &final, &initial."), [['a(0)', 'q(0)', 'q(1)'], ['q(0)', 'q(1)']])
        self.assertEqual(solve("p. &false :- &final, &initial."), [['p(0)', 'p(1)']])
        self.assertEqual(solve("p. &true :- &final, &initial."), [['p(0)']])

    def test_future(self):
        self.assertEqual(solve("p'."), [])
        self.assertEqual(solve("p' :- q. {q}."), [[]])
        self.assertEqual(solve("p' :- q. {q}. :- not q, __initial."), [['p(1)', 'q(0)']])
        self.assertEqual(solve("-p' :- q. {p}. {q}. :- not q, __initial."), [['p(0)', 'q(0)', '-p(1)'], ['q(0)', '-p(1)']])
        self.assertEqual(solve("p'(1;2,3) :- __initial."), [['p(1,1)', 'p(2,3,1)']])

    def test_constraint(self):
        self.assertEqual(solve(":- p'.", always=False), [[]])
        self.assertEqual(solve(":- not p'. #program always. {p}.", always=False), [['p(0)', 'p(1)'], ['p(1)']])
        self.assertEqual(solve(":- not p''. #program always. {p}.", always=False), [['p(0)', 'p(1)', 'p(2)'], ['p(0)', 'p(2)'], ['p(1)', 'p(2)'], ['p(2)']])

    def test_program(self):
        self.assertEqual(solve("#program always. p.", imin=2), [['p(0)'], ['p(0)', 'p(1)']])
        self.assertEqual(solve("#program initial. p.", imin=2), [['p(0)'], ['p(0)']])
        self.assertEqual(solve("#program final. p.", imin=2), [['p(0)'], ['p(1)']])
        self.assertEqual(solve("#program dynamic. p.", imin=2), [[], ['p(1)']])

    def test_theory_boolean(self):
        self.assertEqual(solve("{p}. q :- not &tel {p}."), [['p(0)'], ['q(0)']])
        self.assertEqual(solve("{p}. q :- not &tel {p}. r :- not &tel {p}."), [['p(0)'], ['q(0)', 'r(0)']])
        self.assertEqual(solve('{p(1,a,(1,a),f(2,a),"test",#inf,#sup)}. q(0) :- not &tel {p(1,a,(1,a),f(2,a),"test",#inf,#sup)}.'), [['p(1,a,(1,a),f(2,a),"test",#inf,#sup,0)'], ['q(0,0)']])
        self.assertEqual(solve("{p; q}. :- not &tel {p & q}."), [['p(0)', 'q(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {p | q}."), [[]])
        self.assertEqual(solve("{p; q}. :- &tel {p <> q}."), [[], ['p(0)', 'q(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {p -> q}."), [['p(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {p <- q}."), [['q(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {~p | ~q}."), [['p(0)', 'q(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {~(~p & ~q)}."), [[]])

    def test_theory_tel(self):
        self.assertRaisesRegex(RuntimeError, "leading primes", solve, ":- &tel {'p}.")
        self.assertRaisesRegex(RuntimeError, "trailing primes", solve, ":- &tel {p'}.")
        self.assertEqual(solve("{p}. :- not &tel {p}."), [['p(0)']])

    def test_theory_tel_past(self):
        self.assertEqual(solve("{p}. :- __final, not &tel {<p}."), [['p(0)'], ['p(0)', 'p(1)']])
        self.assertEqual(solve("{p}. :- __final, &tel {<:p}."), [[], ['p(1)']])
        self.assertEqual(solve("{p}. :- __final, not &tel {<*p}.", imin=3), [['p(0)'], ['p(0)', 'p(1)'], ['p(0)', 'p(1)', 'p(2)']])
        self.assertEqual(solve("q. {p}. :- __final, &tel {<?p}.", imin=3), [['q(0)'], ['q(0)', 'q(1)'], ['q(0)', 'q(1)', 'q(2)']])
        self.assertEqual(solve("s. {q;p}. :- __final, not &tel { < s }. :- not &tel {p <* q}."), [
            ['p(0)', 'p(1)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['p(0)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['p(1)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['q(0)', 'q(1)', 's(0)', 's(1)']])
        self.assertEqual(solve("s. {q;p}. :- __final, not &tel { < s }. :- __final, not &tel {p <* q}."), [
            ['p(0)', 'p(1)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['p(0)', 'p(1)', 'q(1)', 's(0)', 's(1)'],
            ['p(0)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['p(1)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['p(1)', 'q(1)', 's(0)', 's(1)'],
            ['q(0)', 'q(1)', 's(0)', 's(1)']])
        self.assertEqual(solve("s. {q;p}. :- &tel {(~p) <* (~q)}."), [
            ['p(0)', 'q(0)', 's(0)'],
            ['q(0)', 's(0)']])
        models = solve("""\
            s.
            {q;p}.
            #program final.
            :- not &tel { < s }.
            #program initial.
            :- not q.
            :- not q', not p'.
            :- not q', not q.
            """)
        self.assertEqual(models, solve("s. {q;p}. :- __final, not &tel { < s }. :- &tel {(~p) <* (~q)}."))
        self.assertEqual(models, solve("s. {q;p}. :- __final, not &tel { < s }. :- not &tel {p <? q}."))

    def test_theory_tel_future(self):
        self.assertEqual(solve("{p}. :- __initial, not &tel {>p}."), [['p(0)', 'p(1)'], ['p(1)']])
        self.assertEqual(solve("{p}. :- __initial, not &tel {> > p}."), [['p(0)', 'p(1)', 'p(2)'], ['p(0)', 'p(2)'], ['p(1)', 'p(2)'], ['p(2)']])
        self.assertEqual(solve("{p}. #program initial. :- not &tel {> > p}."), [['p(0)', 'p(1)', 'p(2)'], ['p(0)', 'p(2)'], ['p(1)', 'p(2)'], ['p(2)']])
        self.assertEqual(solve("s. {p}. #program initial. :- not &tel {>* p}.", imin=3), [['p(0)', 'p(1)', 'p(2)', 's(0)', 's(1)', 's(2)'], ['p(0)', 'p(1)', 's(0)', 's(1)'], ['p(0)', 's(0)']])
        self.assertEqual(solve("s. {p}. #program initial. :- &tel {>? p}.", imin=3), [['s(0)'], ['s(0)', 's(1)'], ['s(0)', 's(1)', 's(2)']])
        self.assertEqual(solve("q. {p}. :- __initial, &tel {>?p}.", imin=3), [['q(0)'], ['q(0)', 'q(1)'], ['q(0)', 'q(1)', 'q(2)']])
        self.assertEqual(solve("s. {q;p}. :- __final, not &tel { < s }. :- __initial, &tel {p >? q}."), [
            ['p(0)', 'p(1)', 's(0)', 's(1)'],
            ['p(0)', 's(0)', 's(1)'],
            ['p(1)', 'q(1)', 's(0)', 's(1)'],
            ['p(1)', 's(0)', 's(1)'],
            ['q(1)', 's(0)', 's(1)'],
            ['s(0)', 's(1)']])
        self.assertEqual(solve("s. {q;p}. :- __final, not &tel { < s }. :- __initial, not &tel {p >* q}."), [
            ['p(0)', 'p(1)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['p(0)', 'p(1)', 'q(0)', 's(0)', 's(1)'],
            ['p(0)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['p(0)', 'q(0)', 's(0)', 's(1)'],
            ['p(1)', 'q(0)', 'q(1)', 's(0)', 's(1)'],
            ['q(0)', 'q(1)', 's(0)', 's(1)']])

    def test_theory_tel_prop(self):
        self.assertEqual(solve("q. {p}. :- __initial, &tel {>?p}.", imin=3), solve("q. {p}. :- __final, &tel {<?p}.", imin=3))
        self.assertEqual(solve("q. {p}. :- __initial, not &tel {>?p}.", imin=3), solve("q. {p}. :- __final, not &tel {<?p}.", imin=3))
        self.assertEqual(solve("q. {p}. :- __initial, &tel {>*p}.", imin=3), solve("q. {p}. :- __final, &tel {<*p}.", imin=3))
        self.assertEqual(solve("q. {p}. :- __initial, not &tel {>*p}.", imin=3), solve("q. {p}. :- __final, not &tel {<*p}.", imin=3))
        self.assertEqual(solve("s. {p;q}. :- __initial, &tel {p>?q}.", imin=2), solve("s. {p;q}. :- __final, &tel {p<?q}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q}. :- __initial, &tel {p>*q}.", imin=2), solve("s. {p;q}. :- __final, &tel {p<*q}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q;r}. :- __initial, &tel {p>*(q>?r)}.", imin=2), solve("s. {p;q;r}. :- __final, &tel {p<*(q<?r)}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q;r}. :- &tel {p>*(q>?r)}.", imin=2), solve("s. {p;q;r}. :- &tel {p<*(q<?r)}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q;r}. :- &tel {p>*(q<?r)}.", imin=2), solve("s. {p;q;r}. :- &tel {p<*(q>?r)}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q;r}. :- &tel {p<*(q>?r)}.", imin=2), solve("s. {p;q;r}. :- &tel {p>*(q<?r)}.", imin=2, dual=True))

    def test_classical(self):
        self.assertEqual(solve("-q."), [['-q(0)']])
        self.assertEqual(solve("{-q}. :- not &tel{ -q }."), [['-q(0)']])
        self.assertEqual(solve("{-q(9)}. :- not &tel{ -q(9) }."), [['-q(9,0)']])

    def test_future_tel(self):
        self.assertEqual(solve("1 {p;q} 1. :- p', &tel { q }.", imin=2), [['p(0)'], ['p(0)', 'p(1)'], ['p(0)', 'q(1)'], ['q(0)'], ['q(0)', 'q(1)']])

    def test_other(self):
        self.assertEqual(solve("p. :- &tel { &final & &initial }."), [['p(0)', 'p(1)']])
        self.assertEqual(solve("p :- not not &tel { &true }. q :- not not &tel { &false }."), [['p(0)']])

    def test_eventually(self):
        s = '''
        #program initial.
        aux.
        #program dynamic.
        aux :- 'aux, not 'q.
        #program always.
        p.
        q :- aux, not &tel{ > >? q }.
        #show p/0.
        #show q/0.
        '''
        self.assertEqual(solve(s, imin=3), [
            ['p(0)', 'p(1)', 'p(2)', 'q(0)'],
            ['p(0)', 'p(1)', 'p(2)', 'q(1)'],
            ['p(0)', 'p(1)', 'p(2)', 'q(2)'],
            ['p(0)', 'p(1)', 'q(0)'],
            ['p(0)', 'p(1)', 'q(1)'],
            ['p(0)', 'q(0)']])
        self.assertEqual(solve(s + "#program initial. q.", imin=3), [['p(0)', 'p(1)', 'p(2)', 'q(0)'], ['p(0)', 'p(1)', 'q(0)'], ['p(0)', 'q(0)']])
        self.assertEqual(solve(s + "#program initial. q'.", imin=3), [['p(0)', 'p(1)', 'p(2)', 'q(1)'], ['p(0)', 'p(1)', 'q(1)']])
        self.assertEqual(solve(s + "#program initial. q''.", imin=3), [['p(0)', 'p(1)', 'p(2)', 'q(2)']])

