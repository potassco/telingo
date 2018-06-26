% From AIPS competition aipslog01.pddl
% https://github.com/SoarGroup/Domains-Planning-Domain-Definition-Language/tree/master/pddl
% length parallel 9

city(pgh;bos;la).
#program initial.

% Each city has a central, an airport, a post office and a truck initially there

in_city((central(C);airport(C);po(C)),C):- city(C).
truck(truck(C)) :- city(C).
at(truck(C),po(C)) :- city(C).

airport(airport(C)) :- city(C).

package(pack1;pack2;pack3).
at(P,po(pgh)) :- package(P).

airplane(plane1;plane2).
at((plane1;plane2),airport(pgh)).

goal_at(pack1,po(bos)).
goal_at(pack2,po(la)).
goal_at(pack3,po(bos)).

#show load/2.
#show unload/2.
#show move/2.

%%%% A test execution
%testing.
%:- not &tel{
%   &initial
% > load(pack2,truck(pgh))
% > move(truck(pgh),airport(pgh))
% > unload(pack2,truck(pgh))
% > load(pack2,plane1)
% > move(plane1,airport(bos))
% > unload(pack2,plane1)
% & &final
%}.