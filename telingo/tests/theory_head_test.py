import unittest
import sys
import clingo
import clingo.ast as ast
import telingo
from numbers import Number
from telingo import transformers as tf
from telingo.theory import head as hd
from clingo.ast import ProgramBuilder

def create_formula(atom):
    clause = []
    for x in atom.elements:
        clause.append(hd.create_formula(x.terms[0], lambda y: y))
    return clause


def theory_atoms(s):
    ctl = clingo.Control()
    with ProgramBuilder(ctl) as bld:
        tf.transform([s], bld.add)
    ctl.ground([("initial", [clingo.Number(0), clingo.Number(0)]), ("always", [clingo.Number(0), clingo.Number(0)])])
    ret = []
    for x in ctl.theory_atoms:
        ret.append(str(hd.translate_formula(x, lambda y: y)))
    ret.sort()
    return ret

class TestTheoryHead(unittest.TestCase):
    def test_transform(self):
        self.assertEqual(theory_atoms("&tel { >a }."), ['(1>a)@0'])
        self.assertEqual(theory_atoms("&tel { > >a }."), ['(1>(1>a))@0'])
        self.assertEqual(theory_atoms("&tel { >>a }."), ['(>*((~__final)|a))@0'])
        self.assertEqual(theory_atoms("&tel { a>?b }."), ['(a>?b)@0'])
        self.assertEqual(theory_atoms("&tel { a>*b }."), ['(a>*b)@0'])
        self.assertEqual(theory_atoms("&tel { -a }."), ['-a@0'])
        self.assertEqual(theory_atoms("&tel { ~a }."), ['(~a)@0'])
        self.assertEqual(theory_atoms("&tel { a&b }."), ['(a&b)@0'])
        self.assertEqual(theory_atoms("&tel { a|b }."), ['(a|b)@0'])
        self.assertEqual(theory_atoms("&tel { &final }."), ['(~(~__final))@0'])
        self.assertEqual(theory_atoms("&tel { &true }."), ['&true@0'])
        self.assertEqual(theory_atoms("&tel { &false }."), ['&false@0'])
        self.assertEqual(theory_atoms("&tel { &initial }."), ['(~(~__initial))@0'])
        self.assertEqual(theory_atoms("&tel { a;b }."), ['(a|b)@0'])
