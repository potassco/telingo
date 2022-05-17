#!/usr/bin/env python

from setuptools import setup
from textwrap import dedent

setup(
    version = '2.1.3',
    name = 'telingo',
    description = 'System to solve dynamic temporal logic programs.',
    long_description = dedent('''\
        Telingo is a solver for temporal programs. It leaverages clingo's input
        language and scripting cababilities to parse and solve programs with
        temporal formulas. As such the input of telingo is valid clingo input
        supporting all clingo language features like for example aggregates;
        only the way programs are grounded and solved is adjusted.
        '''),
    long_description_content_type='text/markdown',
    author = 'Roland Kaminski & Francois Laferriere',
    author_email='kaminski@cs.uni-potsdam.de',
    url='https://github.com/potassco/telingo',
    license = 'MIT',
    install_requires=['clingo>=5.6'],
    packages = ['telingo', 'telingo.theory', 'telingo.transformers'],
    test_suite = 'telingo.tests',
    zip_safe = False,
    entry_points = {
        'console_scripts': [
            'telingo = telingo:main',
        ]
    }
)
