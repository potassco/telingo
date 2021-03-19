"""
Module with functions to transform terms.

Classes:
TermTransformer -- Class to transform terms.
"""


import clingo as _clingo
from clingo import ast as _ast

from . import transformer as _tf

class TermTransformer(_ast.Transformer):
    """
    This class traverses the AST of a term until a Function is found. It then
    add a time parameter to its argument and optionally rewrites the and
    records the predicate name.

    Members:
    parameter         -- Time parameter to extend atoms with.
    future_predicates -- Reference to the set of future predicates
                         having type '{(name, arity, positive, shift)}'
                         where shift corresponds to the number of next
                         operators and positive whether the literal is
                         positive.
    """
    def __init__(self, future_predicates):
        """
        Parameters:
        future_predicates -- reference to the map of future predicates
        """
        self.__future_predicates = future_predicates
        self.__positive = True

    def __get_param(self, name, arity, location, replace_future, fail_future, fail_past, max_shift):
        """
        Strips previous and next operators from function names
        and returns the updated name plus the time arguments to append.
        Furthermore, if the initially operator (_ prefix) is used, then the
        time parameter is replaced with 0. Otherwise, it is treated like a past
        operator.

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

        initially = False
        if n.startswith("_") and not n.startswith("__"):
            n = n[1:]
            if n.startswith("'") or name.startswith("'") or name.endswith("'"):
                raise RuntimeError("initially operator cannot be used with primes: {}".format(_tf.str_location(location)))
            initially = True

        finally_ = False
        if n.endswith("_") and not n.endswith("__"):
            n = n[:-1]
            if n.endswith("'") or name.startswith("'") or name.endswith("'"):
                raise RuntimeError("finally operator cannot be used with primes: {}".format(_tf.str_location(location)))
            finally_ = True
            raise RuntimeError("finally operator not yet supported: {}".format(_tf.str_location(location)))

        if initially and finally_:
            raise RuntimeError("finally and initially operator cannot used together: {}".format(_tf.str_location(location)))
        params = [_ast.SymbolicTerm(location, _clingo.Function(_tf.g_time_parameter_name))]
        if fail_future and (shift > 0 or finally_):
            raise RuntimeError("future atoms not supported in this context: {}".format(_tf.str_location(location)))
        if fail_past and (shift < 0 or initially):
            raise RuntimeError("past atoms not supported in this context: {}".format(_tf.str_location(location)))
        if shift > 0:
            if replace_future:
                self.__future_predicates.add((n, arity, self.__positive, shift))
                n = _tf.g_future_prefix + n
                params.insert(0, _ast.SymbolicTerm(location, _clingo.Number(shift)))
            else:
                max_shift[0] = max(max_shift[0], shift)
        if shift != 0:
            params[-1] = _ast.BinaryOperation(location, _ast.BinaryOperator.Plus, params[-1], _ast.SymbolicTerm(location, _clingo.Number(shift)))
        elif initially:
            params[-1] = _ast.SymbolicTerm(location, _clingo.Number(0))
        return (n, params)

    def visit_UnaryOperation(self, term, *args, **kwargs):
        """
        Determins classical negation.
        """
        try:
            self.__positive = not self.__positive
            return term.update(**self.visit_children(term, *args, **kwargs))
        finally:
            self.__positive = not self.__positive
        return term

    def visit_Function(self, term, *args, **kwargs):
        """
        Transforms the given term.

        See __get_param for more information.
        """
        term.name, params = self.__get_param(term.name, len(term.arguments), term.location, *args, **kwargs)
        term.arguments.extend(params)
        return term

    def visit_SymbolicTerm(self, term, *args, **kwargs):
        """
        Raises a runtime error.

        This function is not necessary if gringo's parser is used but this case
        could occur in a valid AST.
        """
        raise RuntimeError("not implemented")
