"""
The telingo module contains functions to translate and solve temporal logic
programs.

Classes:
TelApp -- Main application class.

Functions:
imain -- Function to run the incremetal solving loop.
main  -- Main function starting an extended clingo application.
"""

import sys
from textwrap import dedent

from clingo import ast
from clingo.symbol import Function, Number, SymbolType
from clingo.application import clingo_main, Application

from . import transformers as _tf
from . import theory as _ty


def imain(prg, future_sigs, program_parts, on_model, imin=0, imax=None, istop="SAT"):
    """
    Take a program object and runs the incremental main solving loop.

    For each pair (name, arity) in future_sigs all atoms in the program base
    with the time parameter referring to the future are set to false. For
    example, given (p, 2) and atoms  p(x,1) in step 0, the atom would p(x,1)
    would be set to false via an assumption. In the following time steps, it
    would not be set to False.

    The list program_parts contains all program parts appearing in the program
    in form of triples (root, name, range) where root is either "initial" (time
    step 0), "always" (time steps >= 0), or "dynamic" (time steps > 0) and
    range is a list of integers for which the part has to be grounded
    backwards. Given range [0, 1] and root "always", at each iteration the
    program part would be grounded at horizon and horizon-1. The latter only if
    the horizon is greater than 0.

    Arguments:
    prg           -- Control object holding the program.
    future_sigs   -- Signatures of predicates whose future incarnations have to
                     be set to False.
    program_parts -- Program parts to ground.
    imin          -- Minimum number of iterations.
    imax          -- Maximum number of iterations.
    istop         -- When to stop.
    """
    thy = _ty.Theory()
    step, ret = 0, None
    while ((imax is None or step < imax) and
           (step == 0 or step < imin or (
               (istop == "SAT" and not ret.satisfiable) or
               (istop == "UNSAT" and not ret.unsatisfiable) or
               (istop == "UNKNOWN" and not ret.unknown)))):
        parts = []
        for root_name, part_name, rng in program_parts:
            for i in rng:
                if ((step - i >= 0 and root_name == "always") or
                        (step - i > 0 and root_name == "dynamic") or
                        (step - i == 0 and root_name == "initial")):
                    parts.append((part_name, [Number(step - i), Number(step)]))
        if step > 0:
            prg.release_external(Function("__final", [Number(step-1)]))
            prg.cleanup()
        prg.ground(parts)
        thy.translate(step, prg)
        prg.assign_external(Function("__final", [Number(step)]), True)
        assumptions = []
        for name, arity, positive in future_sigs:
            for atom in prg.symbolic_atoms.by_signature(name, arity, positive):
                if atom.symbol.arguments[-1].number > step:
                    assumptions.append(-atom.literal)
        ret, step = prg.solve(on_model=lambda m: on_model(m, step), assumptions=assumptions), step+1


class TelApp(Application):
    """
    Application object as accepted by clingo.clingo_main().

    Rewrites the incoming temporal logic programs into incremental ASP programs
    and solves them.
    """
    def __init__(self):
        """
        Initializes the application setting the program name.

        See clingo.clingo_main().
        """
        self.program_name = "telingo"
        self.version = "2.1.2"

        self.__imin = 0
        self.__imax = None
        self.__istop = "SAT"
        self.__horizon = 0

    def __on_model(self, model, horizon):
        """
        Prints the atoms in a model grouped by state.

        Arguments:
        model -- The model to print.
        horizon -- The number of states.
        """
        # pylint: disable=unused-argument
        self.__horizon = horizon

    def __parse_imin(self, value):
        """
        Parse imin argument.
        """
        self.__imin = int(value)
        return self.__imin >= 0

    def __parse_imax(self, value):
        """
        Parse imax argument.
        """
        if len(value) > 0:
            self.__imax = int(value)
            return self.__imax >= 0
        self.__imax = None
        return True

    def __parse_istop(self, value):
        """
        Parse istop argument.
        """
        self.__istop = value.upper()
        return self.__istop in ["SAT", "UNSAT", "UNKNOWN"]

    def print_model(self, model, printer):
        table = {}
        for sym in model.symbols(shown=True):
            if sym.type == SymbolType.Function and len(sym.arguments) > 0:
                table.setdefault(sym.arguments[-1].number, []).append(Function(sym.name, sym.arguments[:-1], sym.positive))
        for step in range(self.__horizon+1):
            symbols = table.get(step, [])
            sys.stdout.write(" State {}:".format(step))
            sig = None
            for sym in sorted(symbols):
                if not sym.name.startswith('__'):
                    if (sym.name, len(sym.arguments), sym.positive) != sig:
                        sys.stdout.write("\n ")
                        sig = (sym.name, len(sym.arguments), sym.positive)
                    sys.stdout.write(" {}".format(sym))
            sys.stdout.write("\n")
        return True

    def register_options(self, options):
        """
        See clingo.clingo_main().
        """
        group = "Telingo Options"
        options.add(group, "imin", "Minimum number of solving steps [0]", self.__parse_imin, argument="<n>")
        options.add(group, "imax", "Maximum number of solving steps []", self.__parse_imax, argument="<n>")
        options.add(group, "istop", dedent("""\
            Stop criterion [sat]
                  <arg>: {sat|unsat|unknown}"""), self.__parse_istop)

    def main(self, control, files):
        """
        Implements the incremental solving loop.

        This function implements the Application.main() function as required by
        clingo.clingo_main().
        """
        with ast.ProgramBuilder(control) as bld:
            files = [open(path) for path in files]
            if len(files) == 0:
                files.append(sys.stdin)
            future_sigs, program_parts = _tf.transform([path.read() for path in files], bld.add)

        imain(control, future_sigs, program_parts, self.__on_model, self.__imin, self.__imax, self.__istop)


def main():
    """
    Run the telingo application.
    """
    sys.exit(int(clingo_main(TelApp(), sys.argv[1:])))
