import sys
import clingo
import telingo.transformers as transformers

def imain(prg, future_sigs, program_parts, on_model, imin = 0, imax = None, istop = "SAT"):
    """
    Take a program object and runs the incremental main solving loop.

    Arguments:
    prg           -- Control object holding the program.
    future_sigs   -- Signatures of predicates whose future incarnations have to
                     be set to False.
    program_parts -- Program parts to ground.
    imin          -- Minimum number of iterations.
    imax          -- Maximum number of iterations.
    istop         -- When to stop.

    TODO: explain future_sigs and parts a bit more
    """
    step, ret = 0, None
    while ((imax is None or step < imax) and
           (step == 0 or step < imin or (
              (istop == "SAT"     and not ret.satisfiable) or
              (istop == "UNSAT"   and not ret.unsatisfiable) or
              (istop == "UNKNOWN" and not ret.unknown)))):
        parts = []
        for root_name, part_name, rng in program_parts:
            for i in rng:
                if ((step - i >= 0 and root_name == "static") or
                    (step - i  > 0 and root_name == "dynamic") or
                    (step - i == 0 and root_name == "initial")):
                    parts.append((part_name, [step - i]))
        if step > 0:
            prg.release_external(clingo.Function("__final", [step-1]))
            prg.cleanup()

        prg.ground(parts)
        prg.assign_external(clingo.Function("__final", [step]), True)
        assumptions = []
        for name, arity in future_sigs:
            for atom in prg.symbolic_atoms.by_signature(name, arity):
                if atom.symbol.arguments[-1].number > step:
                    assumptions.append(-atom.literal)
        ret, step = prg.solve(on_model=on_model, assumptions=assumptions), step+1

class Application:
    """
    TODO: document
    """
    def __init__(self, name):
        """
        Initializes the application setting the program name.

        See clingo.clingo_main().
        """
        self.program_name = name

    def __get(self, prg, name, attr, default):
        """
        TODO: Remove and handle --imin, --imax, and --istop using options.
        """
        val = prg.get_const(name)
        return getattr(val, attr) if val is not None else default

    def __on_model(self, model):
        """
        Prints the atoms in a model grouped by state.
        """
        table = {}
        for sym in model.symbols(shown=True):
            if sym.type == clingo.SymbolType.Function and len(sym.arguments) > 0:
                table.setdefault(sym.arguments[-1], []).append(clingo.Function(sym.name, sym.arguments[:-1]))
        sys.stdout.write("Answer: {}\n".format(model.number))
        for step, symbols in sorted(table.items()):
            sys.stdout.write(" State {}:".format(step))
            sig = None
            for sym in sorted(symbols):
                if (sym.name, len(sym.arguments)) != sig:
                    sys.stdout.write("\n ")
                    sig = (sym.name, len(sym.arguments))
                sys.stdout.write(" {}".format(sym))
            sys.stdout.write("\n".format(step))
        return True

    def main(self, prg, files):
        """
        Implements the main control loop.

        This function implements the Application.main() function as required by
        clingo.clingo_main().
        """
        imin   = self.__get(prg, "imin", "number", 0)
        imax   = self.__get(prg, "imax", "number", None)
        istop  = self.__get(prg, "istop", "string", "SAT")

        with prg.builder() as b:
            files = [open(f) for f in files]
            if len(files) == 0:
                files.append(sys.stdin)
            future_sigs, program_parts = transformers.transform([f.read() for f in files], b.add)

        imain(prg, future_sigs, program_parts, self.__on_model, imin, imax, istop)
