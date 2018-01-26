"""
This module is responsible for visiting and rewriting a programs AST to account
for temporal operators.

The following are random notes sketched before writing the code in this module:

- Past Body:

  H :- p', B.
  becomes
  H :- p(t-1), B.

- Future Head:

  'p :- q', B.
  becomes
  __f_p(t+1) :- q(t-1), B.
  #external p(t) : __f_p(t+1).
  __f_p(t+1) :-     p(t). % only for disjunctions
      p(t)   :- __f_p(t).

  Note: needs chains if there are gaps
        (actually doesn't because of the equivalences)

- Future Body:

  p :- 'q, B.
  can be reduced to Past Head case
  p' :- q, B, t >= 1.

- Past Head:

  Requires domain expansion and will not be supported
  q  :- p.
  p' :- B.

  # p' :- B.
  __e_p(t,1) :- B.
  # q :- p.
  __e_q(t,D) :- __e_p(t,D).

  __e_p(t,D-1) :- __e_p(t+1,D), D >= 1.
  __e_p(t,D+1) :- __e_p(t-1,D), D <= m.

  p(T-D) :- __e_p(T,D), @undefined(p,T-D).
  q(T-D) :- __e_q(T,D), @undefined(q,T-D).

- Future Body in constraints:

  simply reground at the boundary if a non-positive simple atom refers to the future!!!
  once everything is in the past -> no problem!!!
  #external 'q.

  _f_p(t,1) :- p(t,1).

  :- 'p, not 'q.
"""

import clingo
import clingo.ast as ast

class Transformer:
    """
    Basic visitor to traverse and modify an AST.

    Transformers to modify an AST should subclass this class and add visit_TYPE
    methods where TYPE corresponds to an ASTType. This function is called
    whenever a node of the respective type is visited. Its return value will
    replace the node in the parent.

    Function visit should be called on the root of the AST to be visited. It is
    the users responsibility to visit children of nodes that have node-specific
    visitor.
    """
    def visit_children(self, x, *args, **kwargs):
        """
        Visits and transforms the children of the given node.
        """
        for key in x.child_keys:
            setattr(x, key, self.visit(getattr(x, key), *args, **kwargs))
        return x

    def visit(self, x, *args, **kwargs):
        """
        Visits the given node and returns its transformation.

        If there is a matching visit_TYPE function where TYPE corresponds to
        the ASTType of the given node then this function called and its value
        returned. Otherwise, its children are visited and transformed.

        This function accepts additional positional and keyword arguments,
        which are passed to node-specific visit functions and to the visit
        function called for child nodes.
        """
        if isinstance(x, clingo.ast.AST):
            attr = "visit_" + str(x.type)
            if hasattr(self, attr):
                return getattr(self, attr)(x, *args, **kwargs)
            else:
                return self.visit_children(x, *args, **kwargs)
        elif isinstance(x, list):
            return [self.visit(y, *args, **kwargs) for y in x]
        elif x is None:
            return x
        else:
            raise TypeError("unexpected type")

class TermTransformer(Transformer):
    """
    This class traverses the AST of a term until a Function is found. It then
    add a time parameter to its argument and optionally rewrites the and
    records the predicate name.

    Members:
    parameter         -- Time parameter to extend atoms with.
    future_predicates -- Reference to the map of future predicates
                         having type '(name, arity, disjunctive) -> shift'
                         where shift corresponds to the number of next
                         operators and disjunctive determines if the predicate
                         occurred in a disjunction.
    """
    def __init__(self, parameter, future_predicates):
        """
        Parameters:
        parameter         -- time parameter to extend atoms with
        future_predicates -- reference to the map of future predicates
        """
        self.__parameter         = parameter
        self.__future_predicates = future_predicates

    def __get_param(self, name, arity, location, replace_future, fail_future, fail_past, disjunctive, max_shift):
        """
        Strips previous and next operators from function names
        and returns the updated name plus the time arguments to append.

        If replace_future is set this also introduces a new name for the
        predicate, which is recorded in the list of atoms that have to be made
        redefinable. In this case the name is prefixed with __future_. Such
        dynamic predicates are recorded in the future_predicates list.

        Arguments:
        name           -- The name of the predicate
                          (trailing primes denote previous operators).
        location       -- Location for generated terms.
        replace_future -- Whether atoms referring to the future have to be
                          replaced by a special future atom.
        fail_future    -- Fail if the atom refers to the future.
        fail_past      -- Fail if the atom refers to the past.
        max_shift      -- The maximum number of steps terms look into the
                          future.

        Example for body atoms:

            p(X) :- 'q(X)

        becomes

            p(X,t) :- q(X,t-1)

        Example for head atoms (replace_future=True):

            p''(X) :- q(X).

        becomes

            __future__p(X,2,t) :- q(X,t).

        and future_predicates is extended with (p,1,False) -> 2
        """
        n = name.strip("'")
        shift = 0
        for c in name:
            if c == "'":
                shift -= 1
            else:
                break
        shift += len(name) - len(n) + shift

        params = [clingo.ast.Symbol(location, self.__parameter)]
        if shift != 0:
            if fail_future and shift > 0:
                raise RuntimeError("future atoms not supported in this context: {}".format(location))
            if fail_past and shift < 0:
                raise RuntimeError("past atoms not supported in this context: {}".format(location))
            if shift > 0:
                if replace_future:
                    n = "__future_" + n
                    self.__future_predicates.setdefault((n, arity, disjunctive), []).append(shift)
                    params.insert(0, clingo.ast.Symbol(location, shift))
                else:
                    max_shift[0] = max(max_shift[0], shift)
            params[-1] = clingo.ast.BinaryOperation(location, clingo.ast.BinaryOperator.Plus, params[-1], clingo.ast.Symbol(location, shift))
        return (n, params)

    def visit_Function(self, term, *args, **kwargs):
        """
        Transforms the given term.

        See __get_param for more information.
        """
        term.name, params = self.__get_param(term.name, len(term.arguments), term.location, *args, **kwargs)
        term.arguments.extend(params)
        return term

    def visit_Symbol(self, term, *args, **kwargs):
        """
        Raises a runtime error.

        This function is not necessary if gringo's parser is used but this case
        could occur in a valid AST.
        """
        raise RuntimeError("not implemented")

def is_constraint(s):
    """
    Check if the given AST node is a constraint.

    As a special case this function also considers rules with a negative
    literal in the head as a disjunction.
    """
    return (s.type == ast.ASTType.Rule and s.head.type == ast.ASTType.Literal and
            ((s.head.atom.type == ast.ASTType.BooleanConstant and not s.head.atom.value) or
             (s.head.sign != ast.Sign.NoSign)))

def is_disjunction(s):
    """
    Check if a given AST node is a disjunction.

    Normal rules and constraints are not conisdered disjunctions.
    """
    return (s.type == ast.ASTType.Rule and s.head.type == ast.ASTType.Disjunction)

class ProgramTransformer(Transformer):
    """
    Rewrites all temporal operators in a logic program.

    Statements should be passed one after the other to the visit method.

    Members:
    __final            -- Final rules are put into the static program part and
                          the __final atom put into their body. This flag
                          indicates that the __final atom has to be appended.
    __head             -- Indicates that the head of a rule is being visited.
    __constraint       -- Whether the current statement is a constraint.
    __disjunction      -- Wether the current statement is a disjunction.
    __max_shift        -- The maximum number of steps a rule looks into the
                          future. Determines window to reground constraints.
                          Stored as a list with one integer element to allow
                          passing by reference.
    __parameter        -- The time parameter appended to atoms.
    __term_transformer -- The transformer used to rewrite terms.
    __constraint_parts -- Parts that have to be regrounded because of
                          constraints referring to the future.
    """
    def __init__(self, parameter, future_predicates, constraint_parts):
        self.__final = False
        self.__head = False
        self.__constraint = False
        self.__disjunction = False
        self.__max_shift = [0]
        self.__parameter = parameter
        self.__term_transformer = TermTransformer(parameter, future_predicates)
        self.__constraint_parts = constraint_parts

    def __append_final(self, x, add_param=False):
        loc = x.location
        x.body.append(clingo.ast.Literal(loc, clingo.ast.Sign.NoSign, clingo.ast.SymbolicAtom(clingo.ast.Function(loc, "__final", [clingo.ast.Symbol(loc, self.__parameter)] if add_param else [], False))));

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
            self.__disjunction = is_disjunction(rule)
            rule.head = self.visit(rule.head)
            self.__head = False
            rule.body = self.visit(rule.body)
            if self.__max_shift[0] > 0 and not self.__final:
                last = ast.Rule(rule.location, rule.head, rule.body[:])
                self.__append_final(rule, True)
                self.__constraint_parts.setdefault((self.__part, self.__parameter.name, self.__max_shift[0]), []).append((rule, last))
        finally:
            self.__head        = False
            self.__max_shift   = [0]
            self.__constraint  = False
            self.__disjunction = False
        return rule

    def visit_Literal(self, literal):
        """
        Removes the head flag for negative head literals.
        """
        head = self.__head
        try:
            self.__head = self.__head and literal.sign == ast.Sign.NoSign
            return self.visit_children(literal)
        finally:
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
        atom.term = self.__term_transformer.visit(atom.term, self.__head, not self.__head and not self.__constraint, self.__head, self.__head and self.__disjunction, self.__max_shift)
        return atom

    def visit_Program(self, prg):
        """
        Adds the time parameter to the given program given directive.

        Furthermore, the final program part is turned into a static program
        part and the __final flag set accordingly.
        """
        self.__final = prg.name == "final"
        if self.__final:
            prg.name = "static"
        prg.parameters.append(clingo.ast.Id(prg.location, self.__parameter.name))
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

