#!/usr/bin/env python

from setuptools import setup

setup(
    version = '2.1.3',
    name = 'telingo',
    description = 'System to solve dynamic temporal logic programs.',
    author = 'Roland Kaminski & Francois Laferriere',
    author_email='kaminski@cs.uni-potsdam.de',
    url='https://github.com/potassco/telingo',
    license = 'MIT',
    install_requires=['clingo'],
    packages = ['telingo', 'telingo.theory', 'telingo.transformers'],
    test_suite = 'telingo.tests',
    zip_safe = False,
    entry_points = {
        'console_scripts': [
            'telingo = telingo:main',
        ]
    }
)

