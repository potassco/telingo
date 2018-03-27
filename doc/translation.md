# The Translation

The translations below rewrite formulas with future operators in the head into
programs where all future operators occur negatively. These programs can then
be translated to telingo programs using the usual means. Below, I factor out
the rules but a Tseitin translation would also be possible.

## next

The program

    #program initial.

    &tel { n > a }.

is classically equivalent to

    #program always.
    % &tel { (a                     | n - __t + s != 0) &
             (~ ~ (n - __t + s) > a | n - __t + s <= 0) &
             (~ ~ (__t - s - n) < a | n - __t + s >= 0) }.
    % where s is the step at which the constraint was grounded (zero here for
    % the initial situation) and n is some integer (or term) and __t is the step
    % counter (the counters and step numbers could also be provided by a
    % predicates)
    % which is strongly equivalent to

    a :- n - __t + s == 0.
      :- not &tel { (n - __t + s) > a }, n - __t + s > 0.
      :- not &tel { (__t - s - n) < a }, n - __t + s < 0.

preveserving the derivation for `a`.

The weak next operator can be translated the same way by just replacing `>` by
`>:`.

The translation could be simplified by providing an `a @ n` operator combining
what is expressed with `n < a` and `n > a` above.

Note that this translation could be simplified in certain situations but it is
needed in full generality if combined with the translations for the operators
below.

## eventually

The program

    #program initial.
    &tel { >? (a & b) }.

is equivalent to

    #program dynamic.
    c :- 'c.
    c :- 'a, 'b.

    #program always.
    % &tel { ~ ~ c | a | ~ ~ > >? (a & b) }.
    % which is strongly equivalent to

    b :- not c, not &tel { > >? (a & b) }.

## until

The program

    #program initial.
    &tel { a >? b }.

is unpacked for three steps to see where this is going:

    &tel { b0 | (a0 & (b1 | (a1 & (b2 | (a2 & > (a >? b)))))) }.

    &tel { b0 | a0 }.
    &tel { b0 | b1 | a1 }.
    &tel { b0 | b1 | b2 | a2 }.
    &tel { b0 | b1 | b2 | > (a >? b) }.

The following program is equivalent to the above:

    #program dynamic.
    c :- 'c.
    c :- 'b.

    #program always.
    % &tel { ~ ~ c | b | (a & ~ ~ > (a >? b) ) }.
    % which is strongly equivalent to

    b | a :- not c.
    b     :- not c, not &tel { > (a >? b) }.

## always

The program

    #program initial.
    &tel { >* (a | b) }.

is (strongly) equivalent to

    #program always.
    % &tel { a | b }.
    % which is strongly equivalent to

    a | b.

The simplest operator of all. Shifting is only necessary for disjunctions. Even
strong equivalence is preserved here.

## release

The program

    #program initial.
    &tel { a >* b }.

is unpacked for three steps to see where this is going:

    &tel { b0 & (a0 | (b1 & (a1 | (b2 & (a2 | > (a >* b)))))) }.

    &tel { b0 }.
    &tel { a0 | b1 }.
    &tel { a0 | a1 | b2 }.
    &tel { a0 | a1 | a2 | > (a >* b) }.

The following program again starts at step zero:

    #program dynamic.
    c :- 'c.
    c :- 'a.

    #program always.
    % &tel { ~ ~ c | (b & (a | ~ ~ > (a >* b))) }.
    % which is strongly equivalent to

    b :- not c.
    a :- not c, not &tel { > (a >* b) }.

