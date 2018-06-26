#program always.

location(door;window;middle).

#program initial.

at(monkey,door).
at(box,window).
-onbox.
-banana.

#program dynamic.

 at(X,L) :- 'at(X,L), not -at(X,L).
-at(X,L) :- at(X,M), location(L), L!=M.
 onbox :-  'onbox, not -onbox.
-onbox :- -'onbox, not  onbox.
 banana :- 'banana, not -banana.
-banana :- -'banana, not banana.

1 {walkto(X): location(X); pushto(X): location(X); climb; grasp} 1.

at(monkey,X) :- walkto(X).
:- walkto(X), 'onbox.
:- walkto(X), 'at(monkey,X).

at(monkey,X) :- pushto(X).
at(box,X) :- pushto(X).
:- pushto(X), 'onbox.
:- pushto(X), 'at(monkey,Y), 'at(box,Z), Y!=Z.
:- pushto(X), 'at(monkey,X).

banana :- grasp.
:- grasp, -'onbox.
:- grasp, 'at(monkey,X), X!=middle.

onbox :- climb.
:- climb, 'onbox.
:- climb, 'at(monkey,X), 'at(box,Y), X!=Y.

#program final.

:- not banana.

#show at/2.
#show onbox/0.
#show banana/0.
#show climb/0.
#show grasp/0.
#show walkto/1.
#show pushto/1.
