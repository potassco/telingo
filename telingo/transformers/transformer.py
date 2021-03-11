"""
This module contains the basic transformer to traves and change an AST as well
as constants used during translation.

Classes:
Transformer -- Base class to modify ASTs.

Functions:
str_location   -- Turn a location into a string.
is_constraint  -- Check whether a statement is a constraint.
is_normal      -- Check whether a statement is a normal rule.
is_disjunction -- Check whether a statement is a disjunctive rule.

Constants:
g_future_prefix           -- Prefix for predicates referring to the future.
g_variable_prefix         -- Prefix for auxiliary variables.
g_time_parameter_name     -- Prefix for the time parameter.
g_time_parameter_name_alt -- Prefix for the second time parameter used when
                             grounding rules within a given range.
"""

import clingo as _clingo
from clingo import ast as _ast

g_future_prefix = "__future_"
g_variable_prefix = "X"
g_time_parameter_name = "__t"
g_time_parameter_name_alt = "__u"

def str_location(loc):
    """
    This function takes a location from a clingo AST and transforms it into a
    readable format.
    """
    begin = loc.begin
    end   = loc.end
    ret = "{}:{}:{}".format(begin.filename, begin.line, begin.column)
    dash = True
    eq = begin.filename == end.filename
    if not eq:
        ret += "{}{}".format("-" if dash else ":", end.filename)
        dash = False
    eq = eq and begin.line == end.line
    if not eq:
        ret += "{}{}".format("-" if dash else ":", end.line)
        dash = False
    eq = eq and begin.column == end.column
    if not eq:
        ret += "{}{}".format("-" if dash else ":", end.column)
        dash = False
    return ret

def is_constraint(s):
    """
    Check if the given AST node is a constraint.

    As a special case this function also considers rules with a negative
    literal in the head as a constraint.
    """
    return (s.ast_type == _ast.ASTType.Rule and s.head.ast_type == _ast.ASTType.Literal and
            ((s.head.atom.ast_type == _ast.ASTType.BooleanConstant and not s.head.atom.value) or
             (s.head.sign != _ast.Sign.NoSign)))

def is_normal(s):
    """
    Check if the given statement is a normal rule.
    """
    return (s.ast_type == _ast.ASTType.Rule and
            s.head.ast_type == _ast.ASTType.Literal and
            s.head.sign == _ast.Sign.NoSign and
            s.head.atom.ast_type == _ast.ASTType.SymbolicAtom)

def is_disjunction(s):
    """
    Check if a given AST node is a disjunction.

    Normal rules and constraints are not conisdered disjunctions.
    """
    return (s.ast_type == _ast.ASTType.Rule and s.head.ast_type == _ast.ASTType.Disjunction)

class TelTransformer:
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
        updated = []
        for key in x.keys:
            if key in x.child_keys:
                value = self.visit(getattr(x, key), *args, **kwargs)
                updated.append(value)
            else:
                updated.append(getattr(x, key))
        return x.__class__(*updated)

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
        if hasattr(x, "ast_type"):
            attr = "visit_" + str(x.ast_type)
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

    def __call__(self, x, *args, **kwargs):
        """
        Alternative way to call visit.
        """
        return self.visit(x, *args, **kwargs)

_version = _clingo.__version__.split(".")
if int(_version[0]) >= 5 and int(_version[1]) >= 4:
    External = lambda loc, head, body: _ast.External(loc, head, body, _ast.Function(loc, "false", [], False))
else:
    External = _ast.External
