#program always.

q(0) :- &initial.

q(X+1) :- 'q(X), not &initial.
r(X) :- 'r(X), not &initial.

r(X) :- q(X).

:- #sum { X : r(X) } < 10, &final.
