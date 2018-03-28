"""
Module with functions to transform programs.

Classes:
ProgramTransformer -- Class to transform programs.
"""

from telingo.transformers.term import *

class ProgramTransformer(Transformer):
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
    """
    def __init__(self, future_predicates, constraint_parts):
        self.__final = False
        self.__head = False
        self.__constraint = False
        self.__negation = False
        self.__normal = False
        self.__max_shift = [0]
        self.__term_transformer = TermTransformer(future_predicates)
        self.__constraint_parts = constraint_parts

    def __append_final(self, x, param=None):
        loc = x.location
        x.body.append(clingo.ast.Literal(loc, clingo.ast.Sign.NoSign, clingo.ast.SymbolicAtom(clingo.ast.Function(loc, "__final", [clingo.ast.Symbol(loc, param)] if param is not None else [], False))));

    def visit(self, x, *args, **kwargs):
        """
        Extends the transformer's generic visit method to add the final atom to
        all AST nodes in final program parts having a body.

        The extension happens before the node is visited normally so the time
        parameter is added to the atom accordingly.
        """
        if self.__final and isinstance(x, clingo.ast.AST) and hasattr(x, "body"):
            self.__append_final(x)
        ret = Transformer.visit(self, x, *args, **kwargs)
        return ret

    def visit_Rule(self, rule):
        """
        Sets the state flags when visiting a rule.

        After that the head and body of the rule are visited in the right context.
        """
        try:
            self.__head = True
            self.__max_shift = [0]
            self.__constraint = is_constraint(rule)
            self.__normal = is_normal(rule)
            rule.head = self.visit(rule.head)
            self.__head = False
            rule.body = self.visit(rule.body)
            if self.__max_shift[0] > 0 and not self.__final:
                last = ast.Rule(rule.location, rule.head, rule.body[:])
                self.__append_final(rule, clingo.Function(g_time_parameter_name_alt))
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
            self.__negation = literal.sign != ast.Sign.NoSign
            self.__head = self.__head and literal.sign == ast.Sign.NoSign
            return self.visit_children(literal)
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
        atom.term = self.__term_transformer.visit(atom.term, self.__head, not self.__constraint and (not self.__head or not self.__normal), self.__head, self.__max_shift)
        return atom

    def visit_TheoryAtom(self, atom):
        """
        Rewrites theory atoms related to temporal formulas.

        An atom of form `&tel {...}` is rewritten to `&tel(k) {...}`, atoms of
        form `&initial` and `&final` are rewritten to `__initial` and
        `__final`, and atoms of form `&true` and `&false` are rewritten to
        `#true` and `#false`.
        """
        if atom.term.type == ast.ASTType.Function and len(atom.term.arguments) == 0:
            time = lambda loc: ast.Symbol(loc, clingo.Function(g_time_parameter_name))
            wrap = lambda loc, atom: ast.Literal(loc, ast.Sign.DoubleNegation, atom) if self.__head else atom
            if atom.term.name == "tel" :
                if not self.__negation and not self.__constraint:
                    raise RuntimeError("temporal formulas not supported in this context: {}".format(str_location(atom.location)))
                for element in atom.elements:
                    if len(element.tuple) != 1:
                        raise RuntimeError("invalid temporal formula: {}".format(str_location(atom.location)))
                    self.visit(element.condition)
                atom.term = self.__term_transformer.visit(atom.term, False, True, True, self.__max_shift)
            elif atom.term.name == "initial":
                atom = wrap(atom.location, ast.SymbolicAtom(ast.Function(atom.location, "__initial", [time(atom.location)], False)))
            elif atom.term.name == "final":
                atom = wrap(atom.location, ast.SymbolicAtom(ast.Function(atom.location, "__final", [time(atom.location)], False)))
            elif atom.term.name == "true":
                atom = wrap(atom.location, ast.BooleanConstant(True))
            elif atom.term.name == "false":
                atom = wrap(atom.location, ast.BooleanConstant(False))
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
        prg.parameters.append(clingo.ast.Id(prg.location, g_time_parameter_name))
        prg.parameters.append(clingo.ast.Id(prg.location, g_time_parameter_name_alt))
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


