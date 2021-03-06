#program always.
% #external a(up).
{a(up)}.
% {a(down)}.
#program initial.
:- not &del{ &true .>? a(up)}.
% :- not &del{ &true .>? a(down)}.
