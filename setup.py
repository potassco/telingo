#!/usr/bin/env python

from setuptools import setup

setup(
    version = '1.0.3',
    name = 'telingo',
    description = 'System to solve temporal logic programs.',
    author = 'Roland Kaminski',
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

