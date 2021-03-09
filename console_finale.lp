% SAT (Setp 3) 

% *******************  RULES
%{a(0)}.
__initial(0).
{l_4}. % Choice for theory added manually
:- not l_4.
:- not l_4, a(0).
% :- not a(0), not free, l_4.
% :- not l_4, free.
% :- l_4, not l_4.
% :- not l_4, l_4.
%{a(1)}.
{l_9}.
:- not l_9, a(1).
% :- not a(1), not free, l_9.
% :- not l_9, free.
% :- free, not l_9.
% :- not free, l_9.
%{a(2)}.
{l_13}.
:- not l_13, a(2).
:- not a(2), not #false, l_13.
%:- not l_13, #false.
% :- free, not l_13.
% :- not free, l_13.
% ******************* AUX LITERALS
% l_4 := &tel(0){(>?a)}
% l_9 := (>?(a()))
% l_13 := (>?(a()))

% a(2).
% a(1).
% a(0).