"""
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

class Transformer:
    def visit_children(self, x, *args, **kwargs):
        for key in x.child_keys:
            setattr(x, key, self.visit(getattr(x, key), *args, **kwargs))
        return x

    def visit(self, x, *args, **kwargs):
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
    Members:
    parameter         -- time parameter to extend atoms with
    future_predicates -- reference to the map of future predicates
                         having type '(name, arity, disjunctive) -> shift'
                         where shift corresponds to the number of next
                         operators and disjunctive determines if the predicate
                         occurred in a disjunction
    """
    def __init__(self, parameter, future_predicates):
        """
        Parameters:
        parameter         -- time parameter to extend atoms with
        future_predicates -- reference to the map of future predicates
        """
        self.__parameter         = parameter
        self.__future_predicates = future_predicates

    def __get_param(self, name, arity, location, replace_future, fail_future, fail_past, disjunctive):
        """
        Strips previous and next operators from function names
        and returns the updated name plus the time arguments to append.

        If replace_future is set this also introduces a new name for the
        predicate, which is recorded in the list of atoms that have to be made
        redefinable. In this case the name is prefixed with __future_. Such
        dynamic predicates are recorded in the future_predicates list.

        Arguments:
        name           -- the name of the predicate
                          (trailing primes denote previous operators)
        location       -- location for generated terms
        replace_future -- wheather this is a head occurrence
        fail_future    -- fail if the atom refers to the future
        fail_past      -- fail if the atom refers to the past

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
            if replace_future and shift > 0:
                n = "__future_" + n
                self.__future_predicates.setdefault((n, arity, disjunctive), []).append(shift)
                params.insert(0, clingo.ast.Symbol(location, shift))
            params[-1] = clingo.ast.BinaryOperation(location, clingo.ast.BinaryOperator.Plus, params[-1], clingo.ast.Symbol(location, shift))
        return (n, params)

    def visit_Function(self, term, *args, **kwargs):
        term.name, params = self.__get_param(term.name, len(term.arguments), term.location, *args, **kwargs)
        term.arguments.extend(params)
        return term

    def visit_Symbol(self, term, *args, **kwargs):
        # this function is not necessary if gringo's parser is used
        # but this case could occur in a valid AST
        raise RuntimeError("not implemented")

class ProgramTransformer(Transformer):
    def __init__(self, parameter, dynamic_atoms):
        self.final = False
        self.head = False
        self.parameter = parameter
        self.term_transformer = TermTransformer(parameter, dynamic_atoms)

    def visit(self, x, *args, **kwargs):
        ret = Transformer.visit(self, x, *args, **kwargs)
        if self.final and isinstance(x, clingo.ast.AST) and hasattr(x, "body"):
            loc = x.location
            x.body.append(clingo.ast.Literal(loc, clingo.ast.Sign.NoSign, clingo.ast.SymbolicAtom(clingo.ast.Function(loc, "finally", [clingo.ast.Symbol(loc, self.parameter)], False))));
        return ret

    def visit_Rule(self, rule):
        try:
            self.head = True
            self.visit(rule.head)
        finally:
            self.head = False
        self.visit(rule.body)
        return rule

    def visit_SymbolicAtom(self, atom):
        atom.term = self.term_transformer.visit(atom.term, self.head)
        return atom

    def visit_Program(self, prg):
        self.final = prg.name == "final"
        if self.final:
            prg.name = "static"
        prg.parameters.append(clingo.ast.Id(prg.location, self.parameter.name))
        return prg

    def visit_ShowSignature(self, sig):
        sig.arity += 1
        return sig

    def visit_ProjectSignature(self, sig):
        sig.arity += 1
        return sig

