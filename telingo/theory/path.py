class Path(object):
    """
    Base class of all path

    Members:
    __rep  -- unique string representation of the path
    """
    def __init__(self, rep):
        """
        Initializes a formula with the given string representation.
        """
        self.__rep  = rep

    @property
    def _rep(self):
        """
        Return the unique string representaiton of the formula.
        """
        return self.__rep

class SkipPath(Path):
    def __init__(self):
        Path.__init__(self, "(&skip)")

class BinaryPath(Path):
    """
    Members:
    _lhs
    _rhs

    """
    def __init__(self, rep, lhs, rhs):
        self._lhs = lhs
        self._rhs = rhs
        Path.__init__(self, rep)

class ChoicePath(BinaryPath):
    
    def __init__(self, lhs, rhs):
        BinaryPath.__init__(self, "({}+{})".format(lhs._rep, rhs._rep), lhs, rhs)

class SequencePath(BinaryPath):
    
    def __init__(self, lhs, rhs):
        BinaryPath.__init__(self, "({};;{})".format(lhs._rep, rhs._rep), lhs, rhs)

class UnaryPath(Path):
    """
    Members:
    __arg
    """
    def __init__(self, rep, arg):
        self.__arg = arg 
        Path.__init__(self, rep)

    @property
    def _arg(self):
        """
        Return the unique string representaiton of the formula.
        """
        return self.__arg

class CheckPath(UnaryPath):
    
    def __init__(self, arg):
        UnaryPath.__init__(self, "({}?)".format(arg._rep), arg)

class KleeneStarPath(UnaryPath):

    def __init__(self, arg):
        UnaryPath.__init__(self, "({}*)".format(arg._rep), arg)
