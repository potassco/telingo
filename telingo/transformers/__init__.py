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

and future signatures [('f_p', 2, True)] whose atoms have to be set to False if
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

Functions:
transform -- transforms telingo programs into incremental ASP
"""

from textwrap import dedent
from telingo.transformers.transformer import *
from telingo.transformers.program import *

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
    time              = ast.Symbol(loc, clingo.Function(g_time_parameter_name))
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
        callback(ast.Program(loc, "always", [ast.Id(loc, g_time_parameter_name), ast.Id(loc, g_time_parameter_name_alt)]))
        for name, arity, positive, shift in sorted(future_predicates):
            variables = [ ast.Variable(loc, "{}{}".format(g_variable_prefix, i)) for i in range(arity) ]
            s = ast.Symbol(loc, clingo.Number(shift))
            t_shifted = ast.BinaryOperation(loc, ast.BinaryOperator.Plus, time, s)
            add_sign = lambda lit: lit if positive else ast.UnaryOperation(loc, ast.UnaryOperator.Minus, lit)
            p_current = ast.SymbolicAtom(add_sign(ast.Function(loc, name, variables + [time], False)))
            f_current =  ast.SymbolicAtom(add_sign(ast.Function(loc, g_future_prefix + name, variables + [s, time], False)))
            callback(ast.Rule(loc, wrap_lit(p_current), [wrap_lit(f_current)]))
            future_sigs.append((g_future_prefix + name, arity + 2, positive))

    # gather rules for constraints referring to the future
    reground_parts = []
    if len(constraint_parts) > 0:
        for (name, shift), rules in constraint_parts.items():
            assert(shift > 0)
            params = [ast.Id(loc, g_time_parameter_name), ast.Id(loc, g_time_parameter_name_alt)]
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
        params = [ast.Id(loc, g_time_parameter_name), ast.Id(loc, g_time_parameter_name_alt)]
        callback(ast.Program(loc, part_name, params))
        atom = wrap(ast.SymbolicAtom(ast.Function(loc, atom_name, [time], False)))
        callback(statement(loc, atom, []))
    add_part('initial', '__initial', ast.Rule, wrap_lit)
    add_part('always', '__final', ast.External)

    reground_parts.append(('always',  'always',  range(1)))
    reground_parts.append(('dynamic', 'dynamic', range(1)))
    reground_parts.append(('initial', 'initial', range(1)))

    def no_program(s):
        if s.type != ast.ASTType.Program:
            callback(s)

    clingo.parse_program(dedent('''\
        #theory tel {
            formula  {
                &   : 6, unary;         % prefix for keywords
                -   : 6, unary;         % classical negation
                ~   : 5, unary;         % negation
                <   : 5, unary;         % previous
                <   : 5, binary, right; % n x previous
                <:  : 5, unary;         % weak previous
                <:  : 5, binary, right; % n x weak previous
                <?  : 5, unary;         % eventually-
                <*  : 5, unary;         % always-
                <<  : 5, unary;         % initially
                >   : 5, unary;         % next
                >   : 5, binary, right; % n x next
                >:  : 5, unary;         % weak next
                >:  : 5, binary, right; % n x weak next
                >?  : 5, unary;         % eventually+
                >*  : 5, unary;         % always+
                >>  : 5, unary;         % finally
                >*  : 4, binary, left;  % release
                >?  : 4, binary, left;  % until
                <*  : 4, binary, left;  % trigger
                <?  : 4, binary, left;  % since
                &   : 3, binary, left;  % and
                |   : 2, binary, left;  % or
                <-  : 1, binary, left;  % left implication
                ->  : 1, binary, left;  % right implication
                <>  : 1, binary, left;  % equivalence
                ;>  : 0, binary, right; % sequence next
                ;>: : 0, binary, right; % sequence weak next
                <;  : 0, binary, left;  % sequence previous
                <:; : 0, binary, left   % sequence weak previous
            };
            &tel/1 : formula, body
        }.
        '''), no_program)
    return future_sigs, reground_parts