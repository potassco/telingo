"""
This module is responsible for visiting and rewriting a programs AST to account
for temporal operators.

Handling of normal atoms
========================
The temporal program

  p :- q.

becomes

  p(t) :- q(t).

Handling of past atoms in the body
==================================
The temporal program

  p :- 'q.

becomes

  p(t) :- q(t-1).

Handling of future atoms in the head
====================================
The temporal program

  p'.

referring to the future in a normal rule head is rewritten into the following
ASP program:

  f_p(1,t+1).

with auxiliary rules

  #program always(t).
  p(t) :- f_p(1,t).

and future signatures [('f_p', 2)] whose atoms have to be set to False if
referring to the future.

Handling of constraints referring to the future
===============================================
The temporal program

  :- p''.

is rewritten into

  #program always(t).
  #program always_0_1(t,u).
  :- p((t+2)); __final(u).
  #program always_2(t,u).
  :- p((t+2)).

where the constraint is removed from the always part and put into two
additional program parts which have to be grounded for time points t, t-1, and
t-2 as given by the last return value:

  [('always', 'always_0_1', range(0, 2)),
   ('always', 'always_2',   range(2, 3))]
"""

import clingo
import clingo.ast as ast

_future_prefix = "__future_"
_variable_prefix = "X"
_time_parameter_name = "__t"
_time_parameter_name_alt = "__u"

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

def str_location(loc):
    begin = loc["begin"]
    end   = loc["end"]
    ret = "{}:{}:{}".format(begin["filename"], begin["line"], begin["column"])
    dash = True
    eq = begin["filename"] == end["filename"]
    if not eq:
        ret += "{}{}".format("-" if dash else ":", end["filename"])
        dash = False
    eq = eq and begin["line"] == end["line"]
    if not eq:
        ret += "{}{}".format("-" if dash else ":", end["line"])
        dash = False
    eq = eq and begin["column"] == end["column"]
    if not eq:
        ret += "{}{}".format("-" if dash else ":", end["column"])
        dash = False
    return ret

class TermTransformer(Transformer):
    """
    This class traverses the AST of a term until a Function is found. It then
    add a time parameter to its argument and optionally rewrites the and
    records the predicate name.

    Members:
    parameter         -- Time parameter to extend atoms with.
    future_predicates -- Reference to the set of future predicates
                         having type '{(name, arity, shift)}'
                         where shift corresponds to the number of next
                         operators.
    """
    def __init__(self, future_predicates):
        """
        Parameters:
        future_predicates -- reference to the map of future predicates
        """
        self.__future_predicates = future_predicates

    def __get_param(self, name, arity, location, replace_future, fail_future, fail_past, max_shift):
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

        and future_predicates is extended with (p,1,2) -> False
        """
        n = name.strip("'")
        shift = 0
        for c in name:
            if c == "'":
                shift -= 1
            else:
                break
        shift += len(name) - len(n) + shift

        params = [clingo.ast.Symbol(location, clingo.Function(_time_parameter_name))]
        if shift != 0:
            if fail_future and shift > 0:
                raise RuntimeError("future atoms not supported in this context: {}".format(str_location(location)))
            if fail_past and shift < 0:
                raise RuntimeError("past atoms not supported in this context: {}".format(str_location(location)))
            if shift > 0:
                if replace_future:
                    self.__future_predicates.add((n, arity, shift))
                    n = _future_prefix + n
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
    literal in the head as a constraint.
    """
    return (s.type == ast.ASTType.Rule and s.head.type == ast.ASTType.Literal and
            ((s.head.atom.type == ast.ASTType.BooleanConstant and not s.head.atom.value) or
             (s.head.sign != ast.Sign.NoSign)))

def is_normal(s):
    return (s.type == ast.ASTType.Rule and
            s.head.type == ast.ASTType.Literal and
            s.head.sign == ast.Sign.NoSign and
            s.head.atom.type == ast.ASTType.SymbolicAtom)

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
    __final            -- Final rules are put into the always program part and
                          the __final atom put into their body. This flag
                          indicates that the __final atom has to be appended.
    __head             -- Indicates that the head of a rule is being visited.
    __constraint       -- Whether the current statement is a constraint.
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
                self.__append_final(rule, clingo.Function(_time_parameter_name_alt))
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
        atom.term = self.__term_transformer.visit(atom.term, self.__head, not self.__constraint and (not self.__head or not self.__normal), self.__head, self.__max_shift)
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
            prg.name = "always"
        prg.parameters.append(clingo.ast.Id(prg.location, _time_parameter_name))
        prg.parameters.append(clingo.ast.Id(prg.location, _time_parameter_name_alt))
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

def transform(inputs, callback):
    """
    Transforms the given list of temporal programs in string form into an ASP
    program.

    Returns the future predicates whose atoms have to be set to false if
    referring to the future, and program parts that have to be regrounded if
    there are constraints referring to the future.

    Arguments:
    inputs   -- The list of inputs.
    callback -- Callback for rewritten statements.
    """
    loc               = {'begin': {'line': 1, 'column': 1, 'filename': '<transform>'},
                         'end':   {'line': 1, 'column': 1, 'filename': '<transform>'}}
    future_predicates = set()
    constraint_parts  = {}
    time              = ast.Symbol(loc, clingo.Function(_time_parameter_name))
    wrap_lit          = lambda a: ast.Literal(loc, ast.Sign.NoSign, a)

    # apply transformer to program
    def append(s):
        if s is not None:
            callback(s)
    transformer = ProgramTransformer(future_predicates, constraint_parts)
    for i in inputs:
        clingo.parse_program(i, lambda s: append(transformer.visit(s)))

    # add auxiliary rules for future predicates
    future_sigs = []
    if len(future_predicates) > 0:
        callback(ast.Program(loc, "always", [ast.Id(loc, _time_parameter_name), ast.Id(loc, _time_parameter_name_alt)]))
        for name, arity, shift in sorted(future_predicates):
            variables = [ ast.Variable(loc, "{}{}".format(_variable_prefix, i)) for i in range(arity) ]
            s = ast.Symbol(loc, clingo.Number(shift))
            t_shifted = ast.BinaryOperation(loc, ast.BinaryOperator.Plus, time, s)
            p_current = ast.SymbolicAtom(ast.Function(loc, name, variables + [time], False))
            f_current =  ast.SymbolicAtom(ast.Function(loc, _future_prefix + name, variables + [s, time], False))
            callback(ast.Rule(loc, wrap_lit(p_current), [wrap_lit(f_current)]))
            future_sigs.append((_future_prefix + name, arity + 2))

    # gather rules for constraints referring to the future
    reground_parts = []
    if len(constraint_parts) > 0:
        for (name, shift), rules in constraint_parts.items():
            assert(shift > 0)
            params = [ast.Id(loc, _time_parameter_name), ast.Id(loc, _time_parameter_name_alt)]
            # parts to be regrounded
            part = "{}_0_{}".format(name, shift-1)
            callback(ast.Program(loc, part, params))
            for p, l in rules:
                callback(p)
            reground_parts.append((name, part, range(shift)))
            # parts that no longer have to be regrounded
            last_part = "{}_{}".format(name, shift)
            callback(ast.Program(loc, last_part, params))
            for p, l in rules:
                callback(l)
            reground_parts.append((name, last_part, range(shift, shift+1)))

    def add_part(part_name, atom_name, statement, wrap=lambda x: x):
        params = [ast.Id(loc, _time_parameter_name), ast.Id(loc, _time_parameter_name_alt)]
        callback(ast.Program(loc, part_name, params))
        atom = wrap(ast.SymbolicAtom(ast.Function(loc, atom_name, [time], False)))
        callback(statement(loc, atom, []))
    add_part('initial', '__initial', ast.Rule, wrap_lit)
    add_part('always', '__final', ast.External)

    reground_parts.append(('always',  'always',  range(1)))
    reground_parts.append(('dynamic', 'dynamic', range(1)))
    reground_parts.append(('initial', 'initial', range(1)))

    return future_sigs, reground_parts

