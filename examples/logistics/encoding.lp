#program initial.

vehicle(A) :- airplane(A).
vehicle(T) :- truck(T).
location(L) :- in_city(L,_).

#program dynamic.

% Inertia for "at" with trucks (they cannot be outside their city)
at(T,L) :- 'at(T,L), not -at(T,L), _truck(T).
-at(T,L) :- at(T,M), _in_city(M,C), _in_city(L,C), L!=M, _truck(T).

% Inertia for at with airplanes (they are only in airports)
at(A,L) :- 'at(A,L), not -at(A,L), _airplane(A).
-at(A,L) :- at(A,M), _airport(L), L!=M, _airplane(A).

% Inertia for packages
at(P,L) :- 'at(P,L), not -at(P,L), _package(P).
-at(P,L) :- at(P,M), _location(L), L!=M, _package(P).

%%%%%%%%%%% Loading objects / unloading objects

loaded(P) :- in(P,V).

can_load(P,V) :- _package(P), 'at(P,L), _vehicle(V), 'at(V,L), not 'in(P,V), not 'loaded(P).
in(P,V) :- load(P,V).

can_unload(P,V) :- _package(P), 'in(P,V).

% Frame axiom for "in"
in(P,V) :- 'in(P,V), not unload(P,V).

%%%%%%%%%%% Moving vehicles

can_move(T,L) :- _truck(T), 'at(T,M), _in_city(M,C), _in_city(L,C), L!=M.
can_move(A,L) :- _airplane(A), 'at(A,M), _airport(L), L!=M.
at(V,L) :- move(V,L).
moved(V) :- move(V,_).

{load(P,V):can_load(P,V); unload(P,V): can_unload(P,V) } :- _vehicle(V).
cargo(V) :- load(P,V).
cargo(V) :- unload(P,V).
0 {move(V,L): can_move(V,L)} 1 :-  _vehicle(V), not cargo(V).

#program always.
%:- at(O,L), at(O,M), L!=M.
at(P,L) :- in(P,V), at(V,L).

% Control rule: if we move a vehicle, it keeps unmoved until some cargo is done
:- _vehicle(V), moved(V), not &tel{ > (~moved(V) >? cargo(V)) }.

#program final.
:- _goal_at(P,L), not at(P,L), not _testing.
:- _goal_at(P,L), loaded(P),   not _testing.


