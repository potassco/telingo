import unittest
import sys
import clingo
import telingo
import telingo.transformers.head as th

class TestCase(unittest.TestCase):
    def assertRaisesRegex(self, *args, **kwargs):
        return (self.assertRaisesRegexp(*args, **kwargs)
            if sys.version_info[0] < 3
            else unittest.TestCase.assertRaisesRegex(self, *args, **kwargs))

def parse_head(s):
    ret = []
    prg = clingo.Control(message_limit=0)
    clingo.parse_program("&tel{{{}}}.".format(s), ret.append)
    return ret[-1].head

def parse_atom(s):
    return parse_head(s).elements[0].tuple[0]

def transform_atom(s, positive=True):
    return str(th.theory_term_to_atom(parse_atom(s), positive))

class TestHead(TestCase):
    def test_atom(self):
        self.assertEqual(transform_atom("a"), "a")
        self.assertEqual(transform_atom("-a"), "-a")
        self.assertEqual(transform_atom("a", False), "-a")
        self.assertEqual(transform_atom("-a", False), "a")
