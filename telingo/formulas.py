"""
TODO: document
"""

import clingo

class Formula:
    def __init__(self, rep):
        self.__rep = rep
        self.__atoms = set()

    def add_atom(self, atom):
        self.__atoms.add(atom)

    def translate(self, b, step):
        if self.__rep.type == clingo.TheoryTermType.Symbol:
            lit = b.add_atom(clingo.Function(self.__rep.name, [step]))
            for atom in self.__atoms:
                b.add_rule([atom], [lit])
        else:
            print("implement me: translate {} at {}".format(self.__rep, step))
            assert(False)

class Formulas:
    def __init__(self):
        self.__formulas = {}
        self.__bytime   = {}

    def translate(self, step, prg):
        for atom in prg.theory_atoms:
            time    = atom.term.arguments[0].number
            rep     = atom.elements[0].terms[0]
            # TODO: change ...
            formula = self.__formulas.setdefault(str(rep), Formula(rep))
            self.__bytime.setdefault(time, set()).add(formula)
            formula.add_atom(abs(atom.literal))
        if step in self.__bytime:
            with prg.backend() as b:
                for formula in sorted(self.__bytime[step]):
                    formula.translate(b, step)
