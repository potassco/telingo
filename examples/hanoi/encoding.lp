#program dynamic.

% Move a disk to some peg
1 {move(D,P) : _disk(D), _peg(P)} 1.
move(D) :- move(D,P).

% Effects of moves
on(D,P) :- move(D,P).
on(D,P) :- 'on(D,P), not move(D).

% Check moves
blocked(D-1,P) :- 'on(D,P).
blocked(D-1,P) :- blocked(D,P), _disk(D).
:- move(D,P), blocked(D-1,P).
:- move(D), 'on(D,P), blocked(D,P).
:- _disk(D), not 1 {on(D,P)} 1.

#program final.
:- _goal_on(D,P), not on(D,P), not _testing.

#show move/2.
#show on/2.
