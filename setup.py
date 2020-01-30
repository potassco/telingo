#!/usr/bin/env python

from setuptools import setup

setup(
    version = '2.0.0',
    name = 'telingo',
    description = 'System to solve dynamic temporal logic programs.',
    author = 'Roland Kaminski & Francois Laferriere',
    license = 'MIT',
    packages = ['telingo', 'telingo.theory', 'telingo.transformers'],
    test_suite = 'telingo.tests',
    zip_safe = False,
    entry_points = {
        'console_scripts': [
            'telingo = telingo:main',
        ]
    }
)

