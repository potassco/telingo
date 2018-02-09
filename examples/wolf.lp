#program always.

item(w;c;s).
opp(l,r). opp(r,l).
eats(w,s). eats(s,c).

#program initial.

at(b,l).
at(X,l) :- item(X).   % Everything at the left bank

#program dynamic.

% Effect axiom for moving item X
at(X,A) :- 'at(X,B), m(X), opp(A,B). 

% The boat is always moving
at(b,A) :- 'at(b,B), opp(A,B).

% Inertia
at(X,A) :- 'at(X,A), not at(X,B), opp(A,B).

% Choose moving at most one item
0 {m(X):item(X)} 1.

#program always.

% Executability: we cannot move item X if at the opposite bank
:- m(X), 'at(b,A), 'at(X,B), opp(A,B). 

% Unique value constraint: X cannot be at both banks
%:- at(X,A), at(X,B), A!=B.

% If eats(X,Y), we cannot leave them alone
:- eats(X,Y), at(X,A), at(Y,A), opp(A,B), at(b,B).

#program final.

:- { at(X,l) } > 0.

#show m/1.
