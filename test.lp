#program always.
:- requested(X), not &tel { >? attended(X) }.

#program dynamic.
fail :- shoot, unloaded, &tel { <? (<shoot & <unloaded) }.

#program dynamic.

shoot | load | wait.

loaded   :- load.
loaded   :- loaded', not unloaded.
unloaded :- loaded', shoot, not fail.
unloaded :- unloaded', not loaded.

:- load, loaded'.

#program always.

&tel { >? fail } :- shoot, &tel { (<* unloaded) & (<? < shoot) }.

:- not loaded.
:- not shoot.

#program initial.
unloaded.
