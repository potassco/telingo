#const n=4.

disk(1..n).
peg(a;b;c).
init_on(1..n,a).
goal_on(1..n,c).

on(D,P) :- init_on(D,P).


