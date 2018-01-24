import sys
import clingo
import telingo

if __name__ == "__main__":
    """
    TODO: it would be cool if it where possible to replace part of the output
    """
    ret = clingo.clingo_main(telingo.Application(sys.argv[0]), ["-q2"] + sys.argv[1:])
    sys.exit(int(ret))
