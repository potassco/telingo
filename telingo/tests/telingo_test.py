import unittest
import sys
import clingo
import telingo
import telingo.transformers as transformers
from clingo.ast import ProgramBuilder

def parse_model(m, s, dual):
    ret = []
    for sym in m.symbols(shown=True):
        if not sym.name.startswith("__"):
            ret.append(sym)
    if dual:
        def flip(sym): return clingo.Function(
            sym.name, sym.arguments[:-1] + [clingo.Number(s - sym.arguments[-1].number)], sym.positive)
        ret = [flip(sym) for sym in ret]
    return list(map(str, sorted(ret)))


def solve(s, imin=0, dual=False, always=True):
    r = []
    imax = 20
    prg = clingo.Control(['0'], message_limit=0)
    with ProgramBuilder(prg) as bld:
        future_sigs, reground_parts = transformers.transform(
            [("#program always. " if always else "") + s], bld.add)
    telingo.imain(prg, future_sigs, reground_parts, lambda m,
                  s: r.append(parse_model(m, s, dual)), imax=20, imin=imin)
    return sorted(r)


class TestMain(unittest.TestCase):

    def test_dynamic(self):
        self.assertEqual(
            solve("#program initial. :- not &del{ ?q .>? p}."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?q .>* p}."), [[]])
        self.assertEqual(
            solve("#program initial. z :- not &del{ ?q .>? p}."), [['z(0)']])
        self.assertEqual(
            solve("#program initial. z :- not &del{ ?q .>* p}."), [[]])
        self.assertEqual(
            solve("#program initial. z :- not &del{ ?q .>* p}. q."), [['q(0)', 'z(0)']])
        self.assertEqual(solve("#program initial. :- &del{ ?q .>? p}."), [[]])
        self.assertEqual(solve("#program initial. :- &del{ ?q .>* p}."), [])

        self.assertEqual(
            solve("#program initial. :- not &del{ &true .>* p}."), [[]])
        self.assertEqual(
            solve("#program initial. :- not &del{ &true .>* p}.q'."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ &true .>* p}.p'."), [['p(1)']])
        self.assertEqual(
            solve("#program initial. :- not &del{ &true .>? p}."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ &true .>? p}.p'."), [['p(1)']])

        self.assertEqual(
            solve("#program initial. :- not &del{ ?p;; ?q .>* s}.p.q."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?p;; ?q .>* s}.p."), [['p(0)']])
        self.assertEqual(solve(
            "#program initial. :- not &del{ ?p;; ?q .>* s}.p.q.s."), [['p(0)', 'q(0)', 's(0)']])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?p;; ?q .>? s}."), [])
        self.assertEqual(solve(
            "#program initial. :- not &del{ ?p;; ?q .>? s}.p.q.s."), [['p(0)', 'q(0)', 's(0)']])
        self.assertEqual(solve(
            "#program initial. :- not &del{ &true;; ?q .>? s}.q'.s'."), [['q(1)', 's(1)']])
        self.assertEqual(solve(
            "#program initial. :- not &del{ &true + ?q .>* s}.q.s.s'."), [['q(0)', 's(0)', 's(1)']])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?p+ ?q .>? s}."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?p+ ?q .>? s}.p.s."), [['p(0)', 's(0)']])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?p+ &true .>? s}.s'."), [['s(1)']])

        self.assertEqual(
            solve("#program initial. :- not &del{ * &true .>? s}.s'."), [['s(1)']])
        self.assertEqual(
            solve("#program initial. :- not &del{ * &true .>* s}.s''."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ * &true .>* s}.s'.a''."), [])

        self.assertEqual(
            solve("#program initial. :- not &del{ * (p) .>* s}."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ * (p) .>* s}.s."), [["s(0)"]])

        self.assertEqual(
            solve("#program initial. :- not &del{ * (?p ;; &true) .>* s}."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ * (?p ;; &true) .>* s}.s."), [["s(0)"]])
        self.assertEqual(
            solve("#program initial. :- not &del{ * (?p ;; &true) .>* s}.s.p.a'."), [])
        self.assertEqual(solve(
            "#program initial. :- not &del{ * (?p ;; &true) .>* s}.s.p.s'."), [['p(0)', 's(0)', 's(1)']])
        self.assertEqual(solve(
            "#program initial. :- not &del{ ?p + * &true .>* s}.s.p.s'."), [['p(0)', 's(0)', 's(1)']])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?p + * &true .>* s}.p.s'."), [])

        self.assertEqual(
            solve("#program initial. :- not &del{ ?p .>? &true .>* &false }.p.s'."), [])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?p .>? &true .>* &false }.p."), [['p(0)']])
        self.assertEqual(
            solve("#program initial. :- not &del{ ?p .>? ?q .>? &true }.p."), [])
        self.assertEqual(solve(
            "#program initial. :- not &del{ ?p .>? ?q .>? &true }.p.q."), [['p(0)', 'q(0)']])

    def test_simple(self):
        self.assertEqual(solve("p."), [['p(0)']])
        self.assertEqual(solve("p :- q. {q}."), [[], ['p(0)', 'q(0)']])
        self.assertEqual(solve("p(1..2). q(X) :- p(X)."),
                         [['p(1,0)', 'p(2,0)', 'q(1,0)', 'q(2,0)']])
        self.assertEqual(solve("p(1;2)."), [['p(1,0)', 'p(2,0)']])
        self.assertEqual(solve("p(1;2,3)."), [['p(1,0)', 'p(2,3,0)']])
        self.assertEqual(solve("{p : q}. q."), [['p(0)', 'q(0)'], ['q(0)']])
        self.assertEqual(solve("p : q. q."), [['p(0)', 'q(0)']])
        self.assertEqual(
            solve("r :- p : q. p. {q}."), [['p(0)', 'q(0)', 'r(0)'], ['p(0)', 'r(0)']])
        self.assertEqual(
            solve("r :- {p : q} >= 1. p. {q}."), [['p(0)'], ['p(0)', 'q(0)', 'r(0)']])
        self.assertEqual(solve("{p}. :- &initial, not p."), [['p(0)']])
        self.assertEqual(solve("{p}. :- &final, not p."), [['p(0)']])
        self.assertEqual(solve("p. :- &final, &initial."), [['p(0)', 'p(1)']])
        self.assertEqual(solve("&initial :- a. {a}. q. :- &final, &initial."), [
                         ['a(0)', 'q(0)', 'q(1)'], ['q(0)', 'q(1)']])
        self.assertEqual(
            solve("p. &false :- &final, &initial."), [['p(0)', 'p(1)']])
        self.assertEqual(solve("p. &true :- &final, &initial."), [['p(0)']])
        self.assertEqual(solve("d. :- &final. #program always. p :- d. q :- _d.",
                               always=False), [['d(0)', 'p(0)', 'q(0)', 'q(1)']])

    def test_future(self):
        self.assertEqual(solve("p'."), [])
        self.assertEqual(solve("p' :- q. {q}."), [[]])
        self.assertEqual(
            solve("p' :- q. {q}. :- not q, __initial."), [['p(1)', 'q(0)']])
        self.assertEqual(solve("-p' :- q. {p}. {q}. :- not q, __initial."), [
                         ['p(0)', 'q(0)', '-p(1)'], ['q(0)', '-p(1)']])
        self.assertEqual(solve("p'(1;2,3) :- __initial."),
                         [['p(1,1)', 'p(2,3,1)']])

    def test_constraint(self):
        self.assertEqual(solve(":- p'.", always=False), [[]])
        self.assertEqual(solve(
            ":- not p'. #program always. {p}.", always=False), [['p(0)', 'p(1)'], ['p(1)']])
        self.assertEqual(solve(":- not p''. #program always. {p}.", always=False), [
                         ['p(0)', 'p(1)', 'p(2)'], ['p(0)', 'p(2)'], ['p(1)', 'p(2)'], ['p(2)']])

    def test_program(self):
        self.assertEqual(solve("#program always. p.", imin=2),
                         [['p(0)'], ['p(0)', 'p(1)']])
        self.assertEqual(solve("#program initial. p.", imin=2), [
                         ['p(0)'], ['p(0)']])
        self.assertEqual(solve("#program final. p.", imin=2),
                         [['p(0)'], ['p(1)']])
        self.assertEqual(solve("#program dynamic. p.", imin=2), [[], ['p(1)']])

    def test_theory_boolean(self):
        self.assertEqual(solve(
            '{p(-a,1+2,"test")}. q :- not &tel {p(-a,1+2,"test")}.'), [['p(-a,3,"test",0)'], ['q(0)']])
        self.assertEqual(
            solve("{p}. q :- not &tel {p}."), [['p(0)'], ['q(0)']])
        self.assertEqual(solve(
            "{p}. q :- not &tel {p}. r :- not &tel {p}."), [['p(0)'], ['q(0)', 'r(0)']])
        self.assertEqual(solve('{p(1,a,(1,a),f(2,a),"test",#inf,#sup)}. q(0) :- not &tel {p(1,a,(1,a),f(2,a),"test",#inf,#sup)}.'), [
                         ['p(1,a,(1,a),f(2,a),"test",#inf,#sup,0)'], ['q(0,0)']])
        self.assertEqual(
            solve("{p; q}. :- not &tel {p & q}."), [['p(0)', 'q(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {p | q}."), [[]])
        self.assertEqual(
            solve("{p; q}. :- &tel {p <> q}."), [['p(0)'], ['q(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {p -> q}."), [['p(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {p <- q}."), [['q(0)']])
        self.assertEqual(
            solve("{p; q}. :- &tel {~p | ~q}."), [['p(0)', 'q(0)']])
        self.assertEqual(solve("{p; q}. :- &tel {~(~p & ~q)}."), [[]])

    def test_theory_tel(self):
        self.assertRaisesRegex(
            RuntimeError, "leading primes", solve, ":- &tel {'p}.")
        self.assertRaisesRegex(
            RuntimeError, "trailing primes", solve, ":- &tel {p'}.")
        self.assertEqual(solve("{p}. :- not &tel {p}."), [['p(0)']])

    def test_theory_tel_past(self):
        self.assertEqual(
            solve("{p}. :- __final, not &tel {<p}."), [['p(0)'], ['p(0)', 'p(1)']])
        self.assertEqual(solve("{p}. :- __final, &tel {<:p}."), [[], ['p(1)']])
        self.assertEqual(solve("{p}. :- __final, not &tel {<*p}.", imin=3),
                         [['p(0)'], ['p(0)', 'p(1)'], ['p(0)', 'p(1)', 'p(2)']])
        self.assertEqual(solve("q. {p}. :- __final, &tel {<?p}.", imin=3),
                         [['q(0)'], ['q(0)', 'q(1)'], ['q(0)', 'q(1)', 'q(2)']])
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
        self.assertEqual(models, solve(
            "s. {q;p}. :- __final, not &tel { < s }. :- &tel {(~p) <* (~q)}."))
        self.assertEqual(models, solve(
            "s. {q;p}. :- __final, not &tel { < s }. :- not &tel {p <? q}."))

    def test_theory_tel_future(self):
        self.assertEqual(
            solve("{p}. :- __initial, not &tel {>p}."), [['p(0)', 'p(1)'], ['p(1)']])
        self.assertEqual(solve("{p}. :- __initial, not &tel {> > p}."), [
                         ['p(0)', 'p(1)', 'p(2)'], ['p(0)', 'p(2)'], ['p(1)', 'p(2)'], ['p(2)']])
        self.assertEqual(solve("{p}. #program initial. :- not &tel {> > p}."), [
                         ['p(0)', 'p(1)', 'p(2)'], ['p(0)', 'p(2)'], ['p(1)', 'p(2)'], ['p(2)']])
        self.assertEqual(solve("s. {p}. #program initial. :- not &tel {>* p}.", imin=3), [
                         ['p(0)', 'p(1)', 'p(2)', 's(0)', 's(1)', 's(2)'], ['p(0)', 'p(1)', 's(0)', 's(1)'], ['p(0)', 's(0)']])
        self.assertEqual(solve("s. {p}. #program initial. :- &tel {>? p}.", imin=3), [
                         ['s(0)'], ['s(0)', 's(1)'], ['s(0)', 's(1)', 's(2)']])
        self.assertEqual(solve("q. {p}. :- __initial, &tel {>?p}.", imin=3), [
                         ['q(0)'], ['q(0)', 'q(1)'], ['q(0)', 'q(1)', 'q(2)']])
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
        self.assertEqual(solve("q. {p}. :- __initial, &tel {>?p}.",
                               imin=3), solve("q. {p}. :- __final, &tel {<?p}.", imin=3))
        self.assertEqual(solve("q. {p}. :- __initial, not &tel {>?p}.",
                               imin=3), solve("q. {p}. :- __final, not &tel {<?p}.", imin=3))
        self.assertEqual(solve("q. {p}. :- __initial, &tel {>*p}.",
                               imin=3), solve("q. {p}. :- __final, &tel {<*p}.", imin=3))
        self.assertEqual(solve("q. {p}. :- __initial, not &tel {>*p}.",
                               imin=3), solve("q. {p}. :- __final, not &tel {<*p}.", imin=3))
        self.assertEqual(solve("s. {p;q}. :- __initial, &tel {p>?q}.", imin=2), solve(
            "s. {p;q}. :- __final, &tel {p<?q}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q}. :- __initial, &tel {p>*q}.", imin=2), solve(
            "s. {p;q}. :- __final, &tel {p<*q}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q;r}. :- __initial, &tel {p>*(q>?r)}.", imin=2), solve(
            "s. {p;q;r}. :- __final, &tel {p<*(q<?r)}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q;r}. :- &tel {p>*(q>?r)}.", imin=2),
                         solve("s. {p;q;r}. :- &tel {p<*(q<?r)}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q;r}. :- &tel {p>*(q<?r)}.", imin=2),
                         solve("s. {p;q;r}. :- &tel {p<*(q>?r)}.", imin=2, dual=True))
        self.assertEqual(solve("s. {p;q;r}. :- &tel {p<*(q>?r)}.", imin=2),
                         solve("s. {p;q;r}. :- &tel {p>*(q<?r)}.", imin=2, dual=True))

    def test_classical(self):
        self.assertEqual(solve("-q."), [['-q(0)']])
        self.assertEqual(solve("{-q}. :- not &tel{ -q }."), [['-q(0)']])
        self.assertEqual(
            solve("{-q(9)}. :- not &tel{ -q(9) }."), [['-q(9,0)']])

    def test_future_tel(self):
        self.assertEqual(solve("1 {p;q} 1. :- p', &tel { q }.", imin=2), [['p(0)'], [
                         'p(0)', 'p(1)'], ['p(0)', 'q(1)'], ['q(0)'], ['q(0)', 'q(1)']])

    def test_other(self):
        self.assertEqual(
            solve("p. :- &tel { &final & &initial }."), [['p(0)', 'p(1)']])
        self.assertEqual(
            solve("p :- not not &tel { &true }. q :- not not &tel { &false }."), [['p(0)']])

    def test_ally(self):
        self.assertEqual(solve(
            "d. :- &final. #program always. p :- d. q :- not not &tel { << d }.", always=False), [['d(0)', 'p(0)', 'q(0)', 'q(1)']])
        self.assertEqual(solve("#program final. d. #program always. p :- d. q :- not not &tel { >> d }.", always=False, imin=3), [
            ['d(0)', 'p(0)', 'q(0)'],
            ['d(1)', 'p(1)', 'q(0)', 'q(1)'],
            ['d(2)', 'p(2)', 'q(0)', 'q(1)', 'q(2)']])

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
        self.assertEqual(solve(s + "#program initial. q.", imin=3), [
                         ['p(0)', 'p(1)', 'p(2)', 'q(0)'], ['p(0)', 'p(1)', 'q(0)'], ['p(0)', 'q(0)']])
        self.assertEqual(solve(s + "#program initial. q'.", imin=3),
                         [['p(0)', 'p(1)', 'p(2)', 'q(1)'], ['p(0)', 'p(1)', 'q(1)']])
        self.assertEqual(solve(s + "#program initial. q''.",
                               imin=3), [['p(0)', 'p(1)', 'p(2)', 'q(2)']])

    def test_sequence(self):
        self.assertEqual(solve("{b}. a. #program initial. :- not &tel {b ;> b}.", imin=3), [['a(0)', 'a(1)', 'a(2)', 'b(0)', 'b(1)'], [
                         'a(0)', 'a(1)', 'a(2)', 'b(0)', 'b(1)', 'b(2)'], ['a(0)', 'a(1)', 'b(0)', 'b(1)']])
        self.assertEqual(solve("{b}. a. #program final. :- not &tel {b <; b}.", imin=3), [
                         ['a(0)', 'a(1)', 'a(2)', 'b(0)', 'b(1)', 'b(2)'], ['a(0)', 'a(1)', 'a(2)', 'b(1)', 'b(2)'], ['a(0)', 'a(1)', 'b(0)', 'b(1)']])
        self.assertEqual(solve("{b}. a. #program initial. :- not &tel {b ;> b ;> b}.",
                               imin=3), [['a(0)', 'a(1)', 'a(2)', 'b(0)', 'b(1)', 'b(2)']])
        self.assertEqual(solve("{b}. a. #program final. :- not &tel {b <; b <; b}.",
                               imin=3), [['a(0)', 'a(1)', 'a(2)', 'b(0)', 'b(1)', 'b(2)']])
        self.assertEqual(solve("{b}. a. #program initial. :- not &tel {b ;>: b}.",
                               imin=2), [['a(0)', 'a(1)', 'b(0)', 'b(1)'], ['a(0)', 'b(0)']])
        self.assertEqual(solve("{b}. a. #program final. :- not &tel {b <:; b}.", imin=2), [
                         ['a(0)', 'a(1)', 'b(0)', 'b(1)'], ['a(0)', 'b(0)']])

    def test_assoc(self):
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< 4 < b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < < < b}."))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< 2 < 2 < b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < < < b}."))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < 2 < b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < < < b}."))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < 2 < < b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < < < b}."))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< 2 < < 2 < b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < < < < b}."))

    def test_arith(self):
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {1+2 < b}."), [
                         ['a(0)', 'a(1)', 'a(2)', 'a(3)', 'b(0)']])
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {-1+5-1 < b}."), [
                         ['a(0)', 'a(1)', 'a(2)', 'a(3)', 'b(0)']])

    def test_previous(self):
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < b}."), [
                         ['a(0)', 'a(1)', 'a(2)', 'a(3)', 'b(0)']])
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {3 < b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < b}."))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {5 < b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {< < < < < b}."))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {<: <: b}.", imin=3), [
            ['a(0)'],
            ['a(0)', 'a(1)'],
            ['a(0)', 'a(1)', 'a(2)', 'b(0)'],
            ['a(0)', 'a(1)', 'b(0)'],
            ['a(0)', 'a(1)', 'b(1)'],
            ['a(0)', 'b(0)']])
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {2 <: b}.", imin=3),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {<: <: b}.", imin=3))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {4 <: b}.", imin=5),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program final. :- not &tel {<: <: <: <: b}.", imin=5))

    def test_next(self):
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {> > > b}."), [['a(0)', 'a(1)', 'a(2)', 'a(3)', 'b(3)']])

        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {> > > b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {3 > b}."))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {> > > > > b}."),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {5 > b}."))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {>: >: b}.", imin=3), [
            ['a(0)'],
            ['a(0)', 'a(1)'],
            ['a(0)', 'a(1)', 'a(2)', 'b(2)'],
            ['a(0)', 'a(1)', 'b(0)'],
            ['a(0)', 'a(1)', 'b(1)'],
            ['a(0)', 'b(0)']])
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {2 >: b}.", imin=3),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {>: >: b}.", imin=3))
        self.assertEqual(solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {4 >: b}.", imin=5),
                         solve("{b}. a. :- b, &tel { > >? b}.  #program initial. :- not &tel {>: >: >: >: b}.", imin=5))

    def test_aggregate(self):
        self.assertEqual(solve(":- &tel {}."), [])
        self.assertEqual(solve(":- not &tel {}."), [[]])
        self.assertEqual(
            solve("{a; b}. :- not &tel {a; b}."), [['a(0)', 'b(0)']])
        self.assertEqual(
            solve("{ p(1..3); q(1..3) }. :-        p(X) : q(X)."),
            solve("{ p(1..3); q(1..3) }. :- &tel { p(X) : q(X) }."), [])

    def test_head(self):
        self.assertEqual(solve("{body}. &tel { (a & b) | (c & (d | f)) } :- body."), [[], [
                         'a(0)', 'b(0)', 'body(0)'], ['body(0)', 'c(0)', 'd(0)'], ['body(0)', 'c(0)', 'f(0)']])
        self.assertEqual(solve("#program initial. &tel { > b & b | > > c}. #program always. s.", imin=3),
                         [['b(0)', 'b(1)', 's(0)', 's(1)'], ['b(0)', 'b(1)', 's(0)', 's(1)', 's(2)'], ['c(2)', 's(0)', 's(1)', 's(2)']
                          ])
        self.assertEqual(solve("{c}. &tel { a | ~c }."), [
                         [], ['a(0)', 'c(0)']])
        self.assertEqual(solve("{c}. &tel { a | ~ ~c }."), [
                         ['a(0)'], ['c(0)']])
        self.assertEqual(solve("&tel { a | &true }."), [[]])
        self.assertEqual(solve("&tel { a | &false }."), [['a(0)']])
        self.assertEqual(solve("{a;b;c}. &tel { ~(a & b & c) }."),
                         [[], ['a(0)'], ['a(0)', 'b(0)'], ['a(0)', 'c(0)'], ['b(0)'], ['b(0)', 'c(0)'], ['c(0)']
                          ])
        self.assertEqual(solve(
            "&tel { >* a & > > b }.", always=False), [['a(0)', 'a(1)', 'a(2)', 'b(2)']])
        self.assertEqual(solve("&tel { >? a & > > b }.", always=False), [
                         ['a(0)', 'b(2)'], ['a(1)', 'b(2)'], ['a(2)', 'b(2)']])
        self.assertEqual(solve("#program initial. &tel { > > c }.  &tel { >? b }. #program always. &tel { >* a } :- b."),
                         [['a(0)', 'a(1)', 'a(2)', 'b(0)', 'c(2)'], ['a(1)', 'a(2)', 'b(1)', 'c(2)'], ['a(2)', 'b(2)', 'c(2)']
                          ])
        self.assertEqual(solve("&tel { a >? b & 2 > c }.", always=False, imin=3),
                         [['a(0)', 'a(1)', 'b(2)', 'c(2)'], ['a(0)', 'b(1)', 'c(2)'], ['b(0)', 'c(2)']
                          ])
        self.assertEqual(solve("&tel { a >* b & 2 > c }.", always=False, imin=3),
                         [['a(0)', 'b(0)', 'c(2)'], ['a(1)', 'b(0)', 'b(1)', 'c(2)'], ['b(0)', 'b(1)', 'b(2)', 'c(2)']
                          ])
        self.assertEqual(solve("&tel { >? >* a }. #program always. c.", always=False, imin=3),
                         [['a(0)', 'c(0)'], ['a(1)', 'c(0)', 'c(1)'], ['a(2)', 'c(0)', 'c(1)', 'c(2)']
                          ])
        self.assertEqual(solve("&tel { >* c }.  &tel { >> a }.", always=False, imin=3),
                         [['a(0)', 'c(0)'], ['a(1)', 'c(0)', 'c(1)'], ['a(2)', 'c(0)', 'c(1)', 'c(2)']
                          ])
        self.assertEqual(solve("&tel { a ;> b ;> c }.", always=False), [
                         ['a(0)', 'b(1)', 'c(2)']])
        self.assertEqual(solve("&tel { a(1) ;> b(2) ;> c(3) }.", always=False), [
                         ['a(1,0)', 'b(2,1)', 'c(3,2)']])
        self.assertEqual(solve("&tel { a(X) ;> b(X) ;> c(X) } :- X=(1;2).", always=False), [
                         ['a(1,0)', 'a(2,0)', 'b(1,1)', 'b(2,1)', 'c(1,2)', 'c(2,2)']])
        self.assertEqual(solve("&tel { a ;>: b ;>: c }.", always=False, imin=3), [
                         ['a(0)'], ['a(0)', 'b(1)'], ['a(0)', 'b(1)', 'c(2)']])
        self.assertEqual(solve("&tel { >* (&final | a) }. &tel { >* b }.", always=False, imin=3),
                         [['a(0)', 'a(1)', 'b(0)', 'b(1)', 'b(2)'], ['a(0)', 'b(0)', 'b(1)'], ['b(0)']
                          ])
        self.assertEqual(solve("&tel { >* (&initial | a) }. &tel { >* b }.", always=False, imin=3),
                         [['a(1)', 'a(2)', 'b(0)', 'b(1)', 'b(2)'], ['a(1)', 'b(0)', 'b(1)'], ['b(0)']
                          ])
        self.assertEqual(solve("&tel { 2 > a }. &tel { >* b }.", always=False),
                         [['a(2)', 'b(0)', 'b(1)', 'b(2)']
                          ])
        self.assertEqual(solve("&tel { 2 >: a }. &tel { >* b }.", always=False, imin=3),
                         [['a(2)', 'b(0)', 'b(1)', 'b(2)'], ['b(0)'], ['b(0)', 'b(1)']
                          ])
