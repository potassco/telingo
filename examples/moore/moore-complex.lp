#const n=23.

#program initial.

process(a;b).
local(0;1).
instruction(0..2).

% Each process P executes:
% 0   assign c to r(P)
% 1   add c to r(P)
% 2   assing r(P) to C

holds(c,1).
holds(r(P),0) :- process(P).

#program dynamic.

{fetch(P,I): _instruction(I)} 1 :- _process(P).
fetch(P) :- fetch(P,I).
:- fetch(P,I), not _local(I), fetch(Q), P!=Q.
:- #count{P:fetch(P)}=0.


change(r(P),C  ) :- fetch(P,0), 'holds(c,C).
change(r(P),R+C) :- fetch(P,1), 'holds(c,C), 'holds(r(P),R), R+C <= n.
change(r(P),n+1) :- fetch(P,1), 'holds(c,C), 'holds(r(P),R), R+C >  n.
change(c   ,R  ) :- fetch(P,2), 'holds(r(P),R).

holds(F,V) :- change(F,V).
holds(F,V) :- 'holds(F,V), not change(F,_).

:- fetch(P,I), &tel{< <? fetch(P)}, not &tel { < (~fetch(P) <? fetch(P,I')) : I'=(I+2)\3 }.
:- fetch(P,I), not &tel{< <? fetch(P)}, I!=0.

#program final.
:- not _testing, not holds(c,n).

#show fetch/2.
#show holds/2.
