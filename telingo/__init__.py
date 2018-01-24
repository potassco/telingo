import sys
import clingo
import telingo.transformers as trans
from textwrap import dedent

class Application:

    def __init__(self, name):
        self.program_name = name

    def __get(self, val, default):
        return val if val != None else default

    def __on_model(self, model):
        """
        TODO: it would be nice to have some other mechanism to print models, e.g., pass an output thingy to the model
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

    def __imain(self, prg):
        imin   = self.__get(prg.get_const("imin"), clingo.Number(0))
        imax   = prg.get_const("imax")
        istop  = self.__get(prg.get_const("istop"), clingo.String("SAT"))

        step, ret = 0, None
        while ((imax is None or step < imax.number) and
               (step == 0 or step < imin.number or (
                  (istop.string == "SAT"     and not ret.satisfiable) or
                  (istop.string == "UNSAT"   and not ret.unsatisfiable) or
                  (istop.string == "UNKNOWN" and not ret.unknown)))):
            parts = []
            parts.append(("base", [step]))
            parts.append(("static", [step]))
            if step > 0:
                prg.release_external(clingo.Function("finally", [step-1]))
                parts.append(("dynamic", [step]))
                prg.cleanup()
            else:
                parts.append(("initial", [0]))
            prg.ground(parts)
            prg.assign_external(clingo.Function("finally", [step]), True)
            ret, step = prg.solve(on_model=self.__on_model), step+1

    def main(self, prg, files):
        prg.add("base", [], dedent("""\
            #program initial(t).
            initially(t).

            #program static(t).
            #external finally(t).
            """))
        with prg.builder() as b:
            dynamic_atoms = set()
            t = trans.ProgramTransformer(clingo.Function("__t"), dynamic_atoms)
            for f in files:
                clingo.parse_program(
                    open(f).read(),
                    lambda stm: b.add(t.visit(stm)))
            if len(files) == 0:
                clingo.parse_program(
                    sys.stdin.read(),
                    lambda stm: b.add(t.visit(stm)))
        self.__imain(prg)
