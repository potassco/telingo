% None (Setp 2) 

% *******************  RULES
%{a(up,0)}.
__initial(0).
{l_4}. % Choice for theory added manually
:- not l_4.
:- l_4, not l_4.
:- not l_4, l_4.
:- not l_4.
%:- not #true, l_4.
%{a(up,1)}.
:- not a(up,1).
%:- not #true, a(up,1).
% *******************
% l_4 := &del(0){((&true).>?a(up))}
