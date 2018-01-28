q(0) :- __initial.

q(X+1) :- 'q(X), not __initial.
r(X) :- 'r(X), not __initial.

r(X) :- q(X).

:- #sum { X : r(X) } < 10, __final.
