# Telingo

`Telingo` is a solver for temporal programs.

# Usage

```
telingo --help
telingo examples/example1.lp
```

To use `telingo` directly from source run `python -m telingo` from the
project's root directory.

# Installation

Either run `telingo` directly from source or install it by the usual means
provided by Python.  We also provide anaconda packages for easy installation of
all dependencies:

- <https://anaconda.org/potassco/telingo>

## Warning

Currently `telingo` only works with the upcoming 5.3 version of `clingo`. So
for now the work-in-progress (wip) branch of `clingo` has to be used. If
installing with anaconda, make sure to install the development packages of
clingo.

# Input

To refer to an atom in the previous state, the atom has to be prefixed with a
prime, e.g. - `'p(1)`. To refer to an atom in the next state, the atom has to
be suffixed with a prime, e.g. - `p(1)'`. An arbitrary number of primes can be
used. If both leading and trailing primes are used then this is equivalent to
removing the lesser amount of primes from both sides.

Atoms referring to the future are only accepted in heads of normal rules and
constraints. Atoms referring to the past are only accepted in rule bodies (and
negative rule heads).

The following program parts are accepted:

- `#program initial.` which applies only to the first state
- `#program always.` which applies to each state
- `#program dynamic.` which applies to all except the first state
- `#program final.` which applies only to the last state

The following temporal formulas are accepted in constraints and behind default
negation between the braces of theory atoms of form `&tel { ... }` (see the
second example below):

- Boolean Formulas
  - `a & b` (conjunction)
  - `a | b` (disjunction)
  - `a <- b` (left implication)
  - `a -> b` (right implication)
  - `a <> b` (equivalence)
  - `~ a` (negation)
- Formulas referring to the past
  - `< a` (previous)
  - `<: a` (weak previous)
  - `a <* b` (until)
  - `<* b` (always before)
  - `a <? b` (since)
  - `<? b` (eventually before)
- Formulas referring to the future
  - `> a` (next)
  - `>: a` (weak next)
  - `a >* b` (release)
  - `>* b` (always after)
  - `a >? b` (until)
  - `>? b` (eventually after)

## Example I

The following temporal program executes on of the `shoot`, `load`, or `wait`
actions in each time step and updates the `loaded` and `unloaded` fluents
accordingly.

```
#program dynamic.
shoot | load | wait.

loaded :- load.
loaded :- 'loaded, not unloaded.
unloaded :- shoot, 'loaded.
unloaded :- 'unloaded, not loaded.

:- load, 'loaded.

#program initial.
unloaded.
```

By default `telingo` stops unfolding states as soon as an answer set is found.
Running with option `--imin=2` results in the following output:

```
Solving...
Answer: 1
 State 0:
  unloaded
Solving...
Answer: 1
 State 0:
  unloaded
 State 1:
  shoot
  unloaded
SATISFIABLE
```

The output shows that two states have been unfolded on after the other. For the
first answer, there was only one state, the initial situation, where the gun
was unloaded. In the second answer, the second state has been unfolded and the
gun been shot (even though unloaded).

## Example II

The following example modifies the above program to encode that the gun breaks
if there were two shots without loading the gun. Furthermore, its last
integrity constraint selects traces where the loaded gun does not shoot because
it is broken.

```
#program dynamic.
shoot | load | wait.

loaded :- load.
loaded :- 'loaded, not unloaded.
unloaded :- shoot, 'loaded, not broken.
unloaded :- 'unloaded, not loaded.

:- load, 'loaded.

broken :- shoot, not not &tel { <* unloaded & < <? shoot }.
broken :- 'broken.

#program initial.
unloaded.

:- &tel { >*(~loaded | ~shoot) }.
```

Output:

```
Solving...
Solving...
Solving...
Solving...
Solving...
Answer: 1
 State 0:
  unloaded
 State 1:
  shoot
  unloaded
 State 2:
  broken
  shoot
  unloaded
 State 3:
  broken
  load
  loaded
 State 4:
  broken
  loaded
  shoot
SATISFIABLE
```
