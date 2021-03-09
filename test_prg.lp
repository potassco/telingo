% RUN python telingo/program_observer.py 3 test_out.lp test_prg.lp
#program always.
{a}.
#program initial.
:- not &tel{ >? a}.
