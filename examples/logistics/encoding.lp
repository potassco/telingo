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

%%%%%%%%%%% Loading objects

{ load(P,V) } :- _package(P), 'at(P,L), _vehicle(V), 'at(V,L), not 'in(P,V), not 'loaded(P).
:- { load(P,V) } > 1, _package(P).

in(P,V) :- load(P,V).
loaded(P) :- in(P,V).

%%%%%%%%%%% Unloading objects

{ unload(P,V) } :- _package(P), 'in(P,V).

% Frame axiom for "in"
in(P,V) :- 'in(P,V), not unload(P,V).

%%%%%%%%%%% Moving vehicles

{ move(T,L) } :- _truck(T), 'at(T,M), _in_city(M,C), _in_city(L,C), L!=M.
{ move(A,L) } :- _airplane(A), 'at(A,M), _airport(L), L!=M.
:- { move(V,L) } > 1, _vehicle(V).

cargo(V) :- load(P,V).
cargo(V) :- unload(P,V).
:- move(V,L), cargo(V).

at(V,L) :- move(V,L).
moved(V) :- move(V,_).

#program always.

at(P,L) :- in(P,V), at(V,L).

% Control rule: if we move a vehicle, it keeps unmoved until some cargo is done
:- _vehicle(V), moved(V), not &tel{ > (~moved(V) >? cargo(V)) }.

#program final.
:- _goal_at(P,L), not at(P,L), not _testing.
:- _goal_at(P,L), loaded(P),   not _testing.

#defined in/3.
#defined load/3.
#defined loaded/2.
#defined move/3.
#defined moved/2.
#defined testing/1.
#defined unload/3.
