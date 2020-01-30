# Telingo

*Telingo* is a solver for temporal programs. It leaverages *clingo*'s input
language and scripting cababilities to parse and solve programs with temporal
formulas. As such the input of *telingo* is valid *clingo* input supporting all
*clingo* language features like for example aggregates; only the way programs
are grounded and solved is adjusted.

# Usage

```
telingo --help
telingo examples/example1.lp
```

To use *telingo* directly from source run `python -m telingo` from the
project's root directory.

# Installation

Either run *telingo* directly from source or install it by the usual means
provided by Python. We also provide anaconda packages for easy installation of
all dependencies:

- <https://anaconda.org/potassco/telingo>

# Input

To refer to an atom in the previous state, the atom name has to be prefixed
with a prime, e.g. - `'p(1)`. To refer to an atom in the next state, the atom
name has to be suffixed with a prime, e.g. - `p'(1)`. An arbitrary number of
primes can be used. If both leading and trailing primes are used then this is
equivalent to removing the lesser amount of primes from both sides.

The `_` can be used as an initially operator. For example `_p` evaluates to
true if `p` holds in the initial state. It can be used wherever past operators
can be used.

Atoms referring to the future are only accepted in heads of normal rules and
constraints. Atoms referring to the past are only accepted in rule bodies (and
negative rule heads).

The following program parts are accepted:

- `#program initial.` which applies only to the first state
- `#program always.` which applies to each state
- `#program dynamic.` which applies to all except the first state
- `#program final.` which applies only to the last state

The following temporal formulas are supported in rule heads and body literals:
- &initial (true in the initial state)
- &final (true in the final state)

The following temporal formulas are accepted in constraints and behind default
negation between the braces of theory atoms of form `&tel { ... }` (see the
second example below). Formulas marked with *[head]* can also be used in `&tel`
atoms in rule heads:

- Boolean formulas
  - `a & b` (conjunction) *[head]*
  - `a | b` (disjunction) *[head]*
  - `a <- b` (left implication)
  - `a -> b` (right implication)
  - `a <> b` (equivalence)
  - `~ a` (negation) *[head]*
- Formulas referring to the past
  - `< a` (previous)
  - `<: a` (weak previous)
  - `a <* b` (trigger)
  - `<* b` (always before)
  - `a <? b` (since)
  - `<? b` (eventually before)
  - `a <; b` (sequence: `a & (< b)`)
  - `a <:; b` (sequence: `a & (<: b)`)
- Formulas referring to the future
  - `> a` (next) *[head]*
  - `>: a` (weak next) *[head]*
  - `a >* b` (release) *[head]*
  - `>* b` (always after) *[head]*
  - `a >? b` (until) *[head]*
  - `>? b` (eventually after) *[head]*
  - `a ;> b` (sequence: `a & (> b)`) *[head]*
  - `a ;>: b` (sequence: `a & (>: b)`) *[head]*
- Other formulas
  - `&true` (Boolean constant true) *[head]*
  - `&false` (`~ &true`) *[head]*
  - `&initial` (`~ < &true`) *[head]*
  - `&final` (`~ > &true`) *[head]*
  - `<< p` (initially: `<* (~ &initial | p)`)
  - `>> p` (finally: `>* (~ &final | p)`)

The elements of `&tel` atoms are treated like conditional literals in *clingo*.
The rule `:- &tel { p(X) : q(X) }.` is equivalent to `:- p(X) : q(X).`. At the
moment conditions are only supported in rule bodies; future *telingo* versions
might add support for conditions in rule heads.

## Example I

The following temporal program executes one of the `shoot`, `load`, or `wait`
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

By default *telingo* stops unfolding states as soon as an answer set is found.
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
integrity constraint selects traces where the loaded gun did not shoot because
it broke.

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

# Dynamic Logic

Dynamic formulas are accepted in constraints and behind default
negation between the braces of theory atoms of form `&del { ... }`   

Dynamic formulas are constructed by the box (always) and diamond (eventually) operators: 

* `.>*` (infix) for box operator, so that [p] q becomes p .>* q
* `.>?` (infix) for diamond operator, so that \<p> q becomes p .>?  q

Path expressions are formed with: 

* `*` (prefix) Kleene star
* `?` (prefix) test
* `+` (infix)  disjunction
* `;;`(infix)  sequence
* `&true` = \top 

**The path expression is required to be in [normal form](https://www.cs.uni-potsdam.de/wv/publications/DBLP_conf/lpnmr/CabalarDS19.pdf).**

**Examples:**   
* `&del{*(?a ;; &true) .>? b} ` for `<(a?;T)*>b`   
* `&del{?a + ?b .>* c}` for `[a?+b?]c`
