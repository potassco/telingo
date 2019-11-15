"""
This module exports functions to translate (ground) theory atoms to rules via
clingo's backend.
"""

import clingo as _clingo
from . import formula as _frm
from . import body as _bd
from . import head as _hd

class Theory:
    """
    Class holding a set of formulas.

    Formulas can be added to this theory incrementally. Such formulas are then
    also incrementally translated into rules.

    Members:
    __formulas      -- A dictionary of formulas mapping string representations
                       to actual formulas.
    __todo_keys     -- Set of keys of formulas that still have to be translated
                       (makes sure that formulas in the todo list appear only
                       once).
    __todo          -- List of formulas to translate.
    __false_literal -- A literal that is false used during translation.
    """
    def __init__(self):
        """
        Initializes an empty theory.
        """
        self.__formulas = {}
        self.__todo_keys = set()
        self.__todo = []
        self.__false_literal = None

    def add_formula(self, formula):
        """
        Add the given formula to the theory.
        """
        formula = self.__formulas.setdefault(formula._rep, formula)
        return formula

    def add_todo(self, formula, step):
        """
        Add the given formula to the todo list.

        Arguments:
        formula -- The formula to add.
        step    -- The step at which to translate the formula.
        """
        key = (step, formula._rep)
        if key not in self.__todo_keys:
            self.__todo_keys.add(key)
            self.__todo.append((step, formula))

    def false_literal(self, backend):
        """
        Returns a false program literal.

        Arguments:
        backend -- The backend to add the literal to if there is no false
                   literal yet.
        """
        if self.__false_literal is None:
            self.__false_literal = backend.add_atom()
        return self.__false_literal

    def translate(self, horizon, prg):
        """
        Translates the next step for the given horizon.

        Also adds theory atoms from prg.

        Arguments:
        horizon -- The current horizon.
        prg     -- Control object (with theory atoms).
        """
        for atom in prg.theory_atoms:
            if atom.term.name == "del" and len(atom.term.arguments) == 1:
                step    = atom.term.arguments[0].number
                formula = _bd.translate_elements(atom.elements, self.add_formula, True)
                formula.add_atom(atom.literal, step)
                self.add_todo(formula, step)
            elif atom.term.name == "tel" and len(atom.term.arguments) == 1:
                step    = atom.term.arguments[0].number
                formula = _bd.translate_elements(atom.elements, self.add_formula, False)
                formula.add_atom(atom.literal, step)
                self.add_todo(formula, step)
            elif atom.term.name == "__tel_head" and len(atom.term.arguments) == 1:
                step    = atom.term.arguments[0].number
                formula = _hd.translate_formula(atom, self.add_formula)
                self.add_todo(formula, step)

        if len(self.__todo) > 0:
            todo, self.__todo, self.__todo_keys = self.__todo, [], set()
            with prg.backend() as b:
                ctx = _frm.Context(b, prg.symbolic_atoms, self.add_todo, self.add_formula, self.false_literal, horizon)
                for step, formula in todo:
                    formula.translate(ctx, step)
