#const n=19.

#program initial.

process(a;b).
local(0;1).
instruction(0..2).

% Each process P executes:
% 0   assign c to r(P)
% 1   add c to r(P)
% 2   assing r(P) to C
%
% i(P)=I points to the next instruction I of process P to execute

holds(i(P),0) :- process(P).
holds(c,1).
holds(r(P),0) :- process(P).

#program dynamic.

%1 {fetch(P): _process(P)} 1.
{fetch(P,I):_instruction(I)} 1 :- _process(P).
fetch(P) :- fetch(P,I).
:- fetch(P,I), not _local(I), fetch(Q), P!=Q.
:- #count{P:fetch(P)}=0.

change(i(P),(I+1)\3) :- fetch(P), 'holds(i(P),I).
change(r(P),C  )     :- fetch(P), 'holds(i(P),0), 'holds(c,C).
change(r(P),R+C)     :- fetch(P), 'holds(i(P),1), 'holds(c,C), 'holds(r(P),R), R+C <= n.
change(r(P),n+1)     :- fetch(P), 'holds(i(P),1), 'holds(c,C), 'holds(r(P),R), R+C >  n.
change(c   ,R  )     :- fetch(P), 'holds(i(P),2), 'holds(r(P),R).

holds(F,V) :- change(F,V).
holds(F,V) :- 'holds(F,V), not change(F,_).

#program final.
:- not _testing, not holds(c,n).

#show fetch/1.
#show holds/2.
