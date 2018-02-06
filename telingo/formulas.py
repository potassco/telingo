"""
TODO: document
"""

import clingo

def make_equal(builder, a, b):
    builder.add_rule([], [ a, -b])
    builder.add_rule([], [-a,  b])

class Formula:
    def __init__(self, rep):
        self._rep = rep
        self.__atom  = None
        self.__atoms = set()
        self.__done  = set()
        self.__todo  = []

    def translate(self, builder, step, horizon, add_todo):
        if len(self.__todo) > 0:
            for atom in self.__todo:
                make_equal(atom, self.__atom)
            del self.__todo[:]
        if step not in self.__done and self.do_translate(self.__atom, builder, step, horizon, add_todo):
            self.__done.add(step)
        return self.__atom

    def add_atom(self, atom):
        if atom not in self.__atoms:
            self.__atoms.add(atom)
            if self.__atom is None:
                self.__atom = atom
            else:
                self.__todo.append(atom)

class Atom(Formula):
    def do_translate(self, atom, builder, step, horizon, add_todo):
        if step > horizon:
            add_todo(self.__atom, str(self._rep), formula, step)
            return False
        else:
            lit = builder.add_atom(clingo.Function(self._rep.name, [step]))
            make_equal(builder, atom, lit)
            return True

def create_formula(rep, literal, formulas, step):
    if rep.type == clingo.TheoryTermType.Symbol:
        formula = Atom(rep)
    else:
        print("implement me: translate {} at {}".format(rep, step))
        assert(False)
    formula = formulas.add_formula(str(rep), literal, formula, step)
    return formula

class Formulas:
    def __init__(self):
        self.__formulas = {}
        self.__todo_keys = set()
        self.__todo = []

    def add_formula(self, key, literal, formula, step):
        formula = self.__formulas.setdefault(key, formula)
        formula.add_atom(abs(literal))
        return formula

    def add_todo(self, key, formula, step):
        key = (step, key)
        if key not in self.__todo_keys:
            self.__todo_keys.add(key)
            self.__todo.append((step, formula))

    def translate(self, horizon, prg):
        for atom in prg.theory_atoms:
            time    = atom.term.arguments[0].number
            rep     = atom.elements[0].terms[0]
            formula = create_formula(rep, atom.literal, self, horizon)
            self.add_todo(str(rep), formula, horizon)

        atom_set = set()
        assumptions = []
        def add_todo(atom, key, formula, step):
            if atom not in atom_set:
                atom_set.add(atom)
                assumptions.add(-atom)
            self.add_todo(key, formula, step)

        if len(self.__todo) > 0:
            todo, self.__todo, self.__todo_keys = self.__todo, [], set()
            with prg.backend() as b:
                for step, formula in todo:
                    formula.translate(b, step, horizon, add_todo)

        return assumptions
