#program always.

item(fox;beans;goose).
route(river_bank,far_bank). route(far_bank,river_bank).
eats(fox,goose). eats(goose,beans).

#program initial.

% Initially, everything is at the river bank
at(farmer,river_bank).
at(X,river_bank) :- item(X).

#program dynamic.

% Choose moving exactly one item
0 {move(X):item(X)} 1.

% The farmer is always moving
move(farmer).

% Effect axiom for moving
at(X,B) :- 'at(X,A), move(X), route(A,B).

% Items not moved stay where they are
at(X,A) :- 'at(X,A), not move(X).

% The farmer cannot move item X if it is at the opposite bank
:- move(X), item(X), 'at(farmer,A), not 'at(X,A).

#program always.

% Neither farmer nor items can be at both banks
:- at(X,A), at(X,B), A<B.

% If an item eats anther items, we cannot leave them alone
:- eats(X,Y), at(X,A), at(Y,A), not at(farmer,A).

#program final.

% Finally, everything has to be at the far bank
:- at(X,river_bank).

#show move/1.
#show at/2.
