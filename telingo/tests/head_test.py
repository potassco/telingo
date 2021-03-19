import unittest
import sys
import clingo
import telingo
from numbers import Number
from telingo.transformers import head as th

def parse_formula(s):
    ret = []
    clingo.ast.parse_string("&tel{{{}}}.".format(s), ret.append)
    return ret[-1].head

def parse_atom(s):
    return parse_formula(s).elements[0].terms[0]

def theory_term_to_atom(s, positive=True):
    return str(th.theory_term_to_atom(parse_atom(s), positive))

def transform_theory_atom(s):
    atom, ranges = th.transform_theory_atom(parse_formula(s))
    tostr = lambda x: x.symbol.number if x.ast_type == clingo.ast.ASTType.SymbolicTerm and x.symbol.type == clingo.SymbolType.Number else str(x)
    return (str(atom), [((tostr(l), tostr(r)), [str(a) for a in atms]) for (l, r), atms in ranges])

def transform(s):
    atom, rules = th.HeadTransformer().transform(parse_formula(s))
    return (str(atom), [str(rule).replace(". [false]", ".") for rule in rules])

class TestHead(unittest.TestCase):
    def test_atom(self):
        self.assertEqual(theory_term_to_atom("a(1+2)"), "a(3,__t)")
        self.assertEqual(theory_term_to_atom("a(1+a)"), "a((1+a),__t)")
        self.assertEqual(theory_term_to_atom("a"), "a(__t)")
        self.assertEqual(theory_term_to_atom("-a"), "-a(__t)")
        self.assertEqual(theory_term_to_atom("- -a"), "a(__t)")
        self.assertEqual(theory_term_to_atom("a", False), "-a(__t)")
        self.assertEqual(theory_term_to_atom("-a", False), "a(__t)")
        self.assertEqual(theory_term_to_atom("a(X)"), "a(X,__t)")
        self.assertEqual(theory_term_to_atom("a(X,x)"), "a(X,x,__t)")
        self.assertEqual(theory_term_to_atom("a(X,-x)"), "a(X,-x,__t)")

    def test_formula(self):
        self.assertEqual(transform_theory_atom(">a"), ('&__tel_head(__t) { >(a) }', [((1, 1), ['a(__t)'])]))
        self.assertEqual(transform_theory_atom(">:a"), ('&__tel_head(__t) { >:(a) }', [((1, 1), ['a(__t)'])]))
        self.assertEqual(transform_theory_atom("2>a"), ('&__tel_head(__t) { >(2,a) }', [((2, 2), ['a(__t)'])]))
        self.assertEqual(transform_theory_atom("(-2)>a"), ('&__tel_head(__t) { >((- 2),a) }', [((-2, -2), ['a(__t)'])]))
        self.assertEqual(transform_theory_atom("a>?b"), ('&__tel_head(__t) { >?(a,b) }', [((0, '#sup'), ['a(__t)', 'b(__t)'])]))
        self.assertEqual(transform_theory_atom("> (a >? > b)"), ('&__tel_head(__t) { >((a >? > b)) }', [((1, '#sup'), ['a(__t)']), ((2, '#sup'), ['b(__t)'])]))
        self.assertEqual(transform_theory_atom("~a"), ('&__tel_head(__t) { ~(a) }', []))
        self.assertEqual(transform_theory_atom("~ ~a"), ('&__tel_head(__t) { ~(~(a)) }', []))
        self.assertEqual(transform_theory_atom("a & b"), ('&__tel_head(__t) { &(a,b) }', [((0, 0), ['a(__t)', 'b(__t)'])]))
        self.assertEqual(transform_theory_atom("a | b"), ('&__tel_head(__t) { |(a,b) }', [((0, 0), ['a(__t)', 'b(__t)'])]))
        self.assertEqual(transform_theory_atom("a ;> b"), ('&__tel_head(__t) { ;>(a,b) }', [((0, 0), ['a(__t)']), ((1, 1), ['b(__t)'])]))
        self.assertEqual(transform_theory_atom("a ;>: b"), ('&__tel_head(__t) { ;>:(a,b) }', [((0, 0), ['a(__t)']), ((1, 1), ['b(__t)'])]))
        self.assertEqual(transform_theory_atom("&true"), ('&__tel_head(__t) { &(true) }', []))
        self.assertEqual(transform_theory_atom("&false"), ('&__tel_head(__t) { &(false) }', []))
        self.assertEqual(transform_theory_atom("&final"), ('&__tel_head(__t) { &(final) }', []))
        self.assertEqual(transform_theory_atom("&initial"), ('&__tel_head(__t) { &(initial) }', []))
        self.assertEqual(transform_theory_atom(">>a"), ('&__tel_head(__t) { >>(a) }', [((0, '#sup'), ['a(__t)'])]))
        self.assertEqual(transform_theory_atom("2+X>a"), ('&__tel_head(__t) { >(+(2,X),a) }', [(('(2+X)', '(2+X)'), ['a(__t)'])]))

        self.assertEqual(transform_theory_atom(">a | > > a"), ('&__tel_head(__t) { |(>(a),>(>(a))) }', [((1, 2), ['a(__t)'])]))
        self.assertEqual(transform_theory_atom(">a | >* a"), ('&__tel_head(__t) { |(>(a),>*(a)) }', [((0, '#sup'), ['a(__t)'])]))

    def test_interval_set(self):
        self.assertEqual(str(th.IntervalSet([(1, 1)])), "{}")
        self.assertEqual(str(th.IntervalSet([(1, 2)])), "{[1,2)}")
        self.assertEqual(str(th.IntervalSet([(1, 2), (3, 4)])), "{[1,2),[3,4)}")
        self.assertEqual(str(th.IntervalSet([(1, 2), (3, 4), (-1, 0)])), "{[-1,0),[1,2),[3,4)}")
        self.assertEqual(str(th.IntervalSet([(1, 2), (3, 4), (2, 3)])), "{[1,4)}")
        self.assertEqual(str(th.IntervalSet([(1, 2), (3, 4), (5, 7), (0, 10)])), "{[0,10)}")

        self.assertIn((0, 0), th.IntervalSet([(1, 2), (3, 4)]))
        self.assertIn((1, 2), th.IntervalSet([(1, 2), (3, 4)]))
        self.assertIn((3, 4), th.IntervalSet([(1, 2), (3, 5)]))
        self.assertIn((4, 5), th.IntervalSet([(1, 2), (3, 5)]))
        self.assertNotIn((1, 4), th.IntervalSet([(1, 2),(3, 4)]))

    def test_variables(self):
        self.assertEqual([str(v) for v in th.get_variables(parse_atom("p(X,Y) | a(X,Z)"))], ['X', 'Y', 'Z'])

    def test_transform(self):
        self.assertEqual(transform("a"), ('__aux_0(__t)',
            [ '#external __false(__t).'
            , '&__tel_head(__t) { a } :- __aux_0(__t).'
            , 'a(__t): (__t-__S) <= 0 :- __aux_0(__S); __false(__t).'
            ]))

        transformed = transform("> a | > > > b")
        self.assertEqual(transformed[0], '__aux_0(__t)')
        self.assertEqual(transformed[1][0], '#external __false(__t).')
        self.assertEqual(transformed[1][1], '&__tel_head(__t) { |(>(a),>(>(>(b)))) } :- __aux_0(__t).')
        head_elements = transformed[1][2].split(' :- ')[0].split('; ')
        body = transformed[1][2].split(' :- ')[1]
        expected_head_elements = ['a(__t): 1 <= (__t-__S), (__t-__S) <= 1', 'b(__t): 3 <= (__t-__S), (__t-__S) <= 3']
        head_elements.sort()
        self.assertEqual(head_elements,expected_head_elements)
        self.assertEqual(body, '__aux_0(__S); __false(__t).')
        self.assertEqual(transform("> >? a"), ('__aux_0(__t)',
            [ '#external __false(__t).'
            , '&__tel_head(__t) { >(>?(a)) } :- __aux_0(__t).'
            , 'a(__t): 1 <= (__t-__S) :- __aux_0(__S); __false(__t).']))
