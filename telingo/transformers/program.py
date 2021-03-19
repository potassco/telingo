"""
Module with functions to transform programs.

Classes:
ProgramTransformer -- Class to transform programs.
"""

from . import transformer as _tf
from . import term as _tt
from . import head as _th

import clingo as _clingo
from clingo import ast as _ast

class ProgramTransformer(_ast.Transformer):
    """
    Rewrites all temporal operators in a logic program.

    Statements should be passed one after the other to the visit method.

    Members:
    __final            -- Final rules are put into the always program part and
                          the __final atom put into their body. This flag
                          indicates that the __final atom has to be appended.
    __head             -- Indicates that the head of a rule is being visited.
    __constraint       -- Whether the current statement is a constraint.
    __negation         -- Whether the child nodes are in the scope of a
                          negation (this is overridden by positive nested
                          literals).
    __normal           -- Whether the current statement is a normal rule.
    __max_shift        -- The maximum number of steps a rule looks into the
                          future. Determines window to reground constraints.
                          Stored as a list with one integer element to allow
                          passing by reference.
    __term_transformer -- The transformer used to rewrite terms.
    __constraint_parts -- Parts that have to be regrounded because of
                          constraints referring to the future.
    __aux_rules        -- Auxiliary always quantified rules added during
                          translation.
    """
    def __init__(self, future_predicates, constraint_parts, aux_rules):
        self.__final = False
        self.__head = False
        self.__constraint = False
        self.__negation = False
        self.__normal = False
        self.__max_shift = [0]
        self.__term_transformer = _tt.TermTransformer(future_predicates)
        self.__head_transformer = _th.HeadTransformer()
        self.__constraint_parts = constraint_parts
        self.__aux_rules        = aux_rules

    def __append_final(self, x, param=None):
        loc = x.location
        fun = _ast.Function(loc, "__final", [_ast.SymbolicTerm(loc, param)] if param is not None else [], False)
        x.body.append(_ast.Literal(loc, _ast.Sign.NoSign, _ast.SymbolicAtom(fun)));

    def visit(self, x, *args, **kwargs):
        """
        Extends the transformer's generic visit method to add the final atom to
        all AST nodes in final program parts having a body.

        The extension happens before the node is visited normally so the time
        parameter is added to the atom accordingly.
        """
        if self.__final and isinstance(x, _ast.AST) and hasattr(x, "body"):
            self.__append_final(x)
        if isinstance(x, _ast.ASTSequence):
            return _ast.Transformer.visit_sequence(self, x, *args, **kwargs)

        return _ast.Transformer.visit(self, x, *args, **kwargs)

    def visit_Rule(self, rule):
        """
        Sets the state flags when visiting a rule.

        After that the head and body of the rule are visited in the right context.
        """
        try:
            self.__head = True
            self.__max_shift = [0]
            self.__constraint = _tf.is_constraint(rule)
            self.__normal = _tf.is_normal(rule)
            rule.head = self.visit(rule.head)
            self.__head = False
            rule.body = self.visit(rule.body)
            if self.__max_shift[0] > 0 and not self.__final:
                last = _ast.Rule(rule.location, rule.head, rule.body[:])
                self.__append_final(rule, _clingo.Function(_tf.g_time_parameter_name_alt))
                self.__constraint_parts.setdefault((self.__part, self.__max_shift[0]), []).append((rule, last))
                return None
        finally:
            self.__head        = False
            self.__max_shift   = [0]
            self.__constraint  = False
            self.__normal = False
        return rule

    def visit_Literal(self, literal):
        """
        Removes the head flag for negative head literals.
        """
        head = self.__head
        try:
            self.__negation = literal.sign != _ast.Sign.NoSign
            self.__head = self.__head and literal.sign == _ast.Sign.NoSign
            return literal.update(**self.visit_children(literal))
        finally:
            self.__negation = False
            self.__head = head

    def visit_ConditionalLiteral(self, literal):
        """
        Make sure that conditions are traversed as non-head literals.
        """
        self.visit(literal.literal)
        head = self.__head
        try:
            self.__head = False
            self.visit(literal.condition)
        finally:
            self.__head = head
        return literal

    def visit_SymbolicAtom(self, atom):
        """
        Rewrites the given symbolic atom appending a time parameter.

        If this atom appears in a head then it is also replaced by a
        corresponding future atom defined later.
        """
        atom.symbol = self.__term_transformer.visit(atom.symbol, self.__head, not self.__constraint and (not self.__head or not self.__normal), self.__head, self.__max_shift)
        return atom

    def visit_TheoryAtom(self, atom):
        """
        Rewrites theory atoms related to temporal formulas.

        An atom of form `&tel {...}` is rewritten to `&tel(k) {...}`, atoms of
        form `&initial` and `&final` are rewritten to `__initial` and
        `__final`, and atoms of form `&true` and `&false` are rewritten to
        `#true` and `#false`.
        """
        if atom.term.ast_type == _ast.ASTType.Function and len(atom.term.arguments) == 0:
            time = lambda loc: _ast.SymbolicTerm(loc, _clingo.Function(_tf.g_time_parameter_name))
            wrap = lambda loc, atom: _ast.Literal(loc, _ast.Sign.DoubleNegation, atom) if self.__head else atom
            if atom.term.name == "del" :
                if not self.__negation and not self.__constraint:
                        raise RuntimeError("dynamic formulas not supported in this context: {}".format(_tf.str_location(atom.location)))
                atom.term.arguments = [_ast.SymbolicTerm(atom.term.location, _clingo.Function("__t"))]
            elif atom.term.name == "tel" :
                if self.__head:
                    atom, rules = self.__head_transformer.transform(atom)
                    self.__aux_rules.extend(rules)
                else:
                    if not self.__negation and not self.__constraint:
                        raise RuntimeError("temporal formulas not supported in this context: {}".format(_tf.str_location(atom.location)))
                    for element in atom.elements:
                        if len(element.terms) != 1:
                            raise RuntimeError("invalid temporal formula: {}".format(_tf.str_location(atom.location)))
                        self.visit(element.condition)
                    atom.term = self.__term_transformer.visit(atom.term, False, True, True, self.__max_shift)
            elif atom.term.name == "initial":
                atom = wrap(atom.location, _ast.SymbolicAtom(_ast.Function(atom.location, "__initial", [time(atom.location)], False)))
            elif atom.term.name == "final":
                atom = wrap(atom.location, _ast.SymbolicAtom(_ast.Function(atom.location, "__final", [time(atom.location)], False)))
            elif atom.term.name == "true":
                atom = wrap(atom.location, _ast.BooleanConstant(True))
            elif atom.term.name == "false":
                atom = wrap(atom.location, _ast.BooleanConstant(False))
        return atom

    def visit_Program(self, prg):
        """
        Adds the time parameter to the given program given directive.

        Furthermore, the final program part is turned into an always program
        part and the __final flag set accordingly.
        """
        self.__final = prg.name == "final"
        if self.__final:
            prg.name = "always"
        if prg.name == "base":
            prg.name = "initial"
        prg.parameters.append(_ast.Id(prg.location, _tf.g_time_parameter_name))
        prg.parameters.append(_ast.Id(prg.location, _tf.g_time_parameter_name_alt))
        self.__part = prg.name
        return prg

    def visit_ShowSignature(self, sig):
        """
        Adjusts the arity of show predicate statements.

        For example `#show p/2` becomes `#show p/3` because all occurrences of
        atoms over `p` are extended with a time parameter.
        """
        sig.arity += 1
        return sig

    def visit_ProjectSignature(self, sig):
        """
        Adjusts the arity of project predicate statements.

        See visit_ShowSignature.
        """
        sig.arity += 1
        return sig

    def visit_Input(self, sig):
        """
        Adjusts the arity of input predicate statements.

        See visit_ShowSignature.
        """
        sig.arity += 1
        return sig



