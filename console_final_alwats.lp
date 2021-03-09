% SAT (Setp 3) 

% *******************  RULES
%{a(0)}.
__initial(0).
{l_4}. % Choice for theory added manually
:- not l_4.
:- l_4, not a(0).
:- a(0), not l_4.
%:- l_4, not #true.
:- l_4, not l_4.
:- not l_4, l_4.
%{a(1)}.
{l_9}.
:- l_9, not a(1).
:- a(1), not l_9.
%:- l_9, not #true.
:- not l_9.
%:- not #true, l_9.
%{a(2)}.
{l_13}.
:- l_13, not a(2).
:- a(2), not l_13.
%:- l_13, not #true.
:- not l_13.
%:- not #true, l_13.
% ******************* Literals from Tsaiten reduction
% l_4 := &tel(0){(>*a)}
% l_9 := (>*(a()))
% l_13 := (>*(a()))
