"""
This module contains simple helper functions.
"""
import sys
import clingo
import telingo
import telingo.transformers as transformers
from telingo.tests.telingo_test import solve


class Observer:
    def __init__(self):
        self.rules = []
        self.externals = {}  # Dyanamic
        self.prg_map = {}
        self.assumeed_lit = []  # Dynamic

    def prg_update(self, prg):
        self.prg_map.update({s.literal: str(s.symbol)
                             for s in prg.symbolic_atoms})
        self.prg_map.update({s.literal: str(s) for s in prg.theory_atoms})

    def get_prop(self, l):
        s = self.prg_map[l]
        if s[0] == '(' or s[0] == '&':
            return "l_{}".format(l)
        return self.prg_map[l]

    def get_map(self):
        m = ""
        for k, v in self.prg_map.items():
            if v[0] == '(' or v[0] == '&':
                m += "% l_{} := {}\n".format(k, v)
        return m

    def get_clingo_program(self, false_literal=None):
        prg = "\n% *******************  RULES\n"
        for k, v in self.externals.items():
            if v.__class__ == clingo.TruthValue:
                self.externals[k] = "#true"
            elif "true" in str(v).lower():
                self.externals[k] = "#true"
            elif "false" in str(v).lower():
                self.externals[k] = "#false"
            elif "free" in str(v).lower():
                self.externals[k] = "#false"
        self.prg_map.update(self.externals)
        self.prg_map[false_literal] = "#false"

        lit_with_added_choice = []
        for rule in self.rules:
            bracket_l = "{"if rule[0] else ""
            bracket_r = "}"if rule[0] else ""
            head = "; ".join([str(self.get_prop(l)) for l in rule[1]])
            false_body = False
            body_lits = []
            for l in rule[2]:
                if l > 0:
                    p = self.get_prop(l)
                    if p == "#false":
                        false_body = True
                    if p != "#true":
                        body_lits.append(p)
                else:
                    p = self.get_prop(-l)
                    if p == "#true":
                        false_body = True

                    if p != "#false":
                        body_lits.append("not " + p)

                    # Add choice for theory in :- not &t
                    if self.prg_map[-l][0] == "&" and not -l in lit_with_added_choice:
                        prg += "{}{}{}. % Choice for theory added manually\n".format(
                            '{', self.get_prop(-l), '}')
                        lit_with_added_choice.append(-l)
            is_choice_on_prop = rule[0] and len(
                rule[1]) == 1 and head[:2] != "l_"
            if is_choice_on_prop or false_body:
                prg += "%"
            impl = ":- "if len(rule[2]) != 0 else ""
            prg += "{}{}{}{}{}.\n".format(bracket_l,
                                          head, bracket_r, impl, ", ".join(body_lits))
        for l in self.assumeed_lit:
            if l > 0:
                prg += "{}.".format(self.get_prop(l))
            elif l < 0:
                prg += ":- {}.".format(self.get_prop(-1*l))
        prg += "% *******************\n"
        prg += self.get_map()
        return prg

    def rule(self, choice, head, body):
        """
        Observe rules passed to the solver.

        Parameters
        ----------
        choice : bool
            Determines if the head is a choice or a disjunction.
        head : List[int]
            List of program atoms forming the rule head.
        body : List[int]
            List of program literals forming the rule body.

        Returns
        -------
        None
        """
        # print("OBSERVER: Rule {} :- {}".format(head, body))
        self.rules.append((choice, head, body))

    def external(self, atom, value):
        """
        Observe external statements passed to the solver.

        Parameters
        ----------
        atom : int
            The external atom in form of a program literal.
        value : TruthValue
            The truth value of the external statement.

        Returns
        -------
        None
        """
        self.externals[atom] = value

    def assume(self, literals):
        """
        Observe assumption directives passed to the solver.

        Parameters
        ----------
        literals : List[int]
            The program literals to assume (positive literals are true andz 
            negative literals false for the next solve call).

        Returns
        -------
        None
        """
        self.assumeed_lit = literals


global observer
observer = Observer()

if __name__ == "__main__":
    program = ""
    for fn in sys.argv[3:]:
        f = open(fn, 'r')
        program += f.read()
        f.close()
    solve(program, int(
        sys.argv[1]), out_file=sys.argv[2], imax=int(
        sys.argv[1]))
