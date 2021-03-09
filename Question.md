
Hi! I have some `telingo` questions. 
I want to have some baseline to benchmark my automaton approach for `del`. So I thought it would be an interesting exercise to try to get the final program after the translation of `telingo` and use this to compare it to my approach. I wanted to try this also to get more insight before taking up the issue for the changes regarding the new AST. 

To get the program I added an Observer and constructed the program myself as rules and literals are being added and then I put all rules together.

My first issue was that it expected to have a truth value for propositions appearing in the theory atom, but I want to have a translation independent of the instance... My idea for this was to add externals but since that made not change I added choices for the atoms.

```
#program always.
{a}.
#program initial.
:- not &tel{ > a}.
```

calling `imain` with `imin=0` and `imax=3` `istop="UNKNOWN"`(Because I want the program at a fixed horizon which is `imax`), I get the following program after commenting out the choices and adding a choice for the theory atom (which in my case is always after `:- not`)


```
% SAT (Setp 3) 

% *******************  RULES
%{a(0)}.
__initial(0).
{l_4}. % Choice for theory added manually
:- not l_4.
:- l_4, not free.
:- not l_4, free.
%{a(1)}.
:- free, not a(1).
:- not free, a(1).
%{a(2)}.
% ******************* AUX LITERALS
% l_4 := &tel(0){(>a)}
```

The `free` atom is representing `_clingo.TruthValue.Free`. So for the externals I am printing literals as the last value assigned to their external or the new literal for auxiliary formulas. Since this was not giving me the answer I went deeper in the code... One of my main issues is that I don't follow the last case of the translation of the next (https://github.com/potassco/telingo/blob/master/telingo/theory/body.py) lines 467 to 472. Why is the literal assigned to Free? 

So far my search lead me to look in how the data for each step is set, where I saw that nothing is added to the set of literals, but instead a  the literal of the data is just directly modified. I made method and called it instead of this direct assignments, with the intention of using the initial literal as representative for the equivalences instead of the external literals:

```
def append_literal(self, literal):
    self.literals.add(literal)
    if self.literal is None:
        self.literal = min(self.literals)

    # Old version       self.literal = literal
```

If I do this and remove the assignment of the literal to a free external, I get a program closer to what I was looking for:

```
% SAT (Setp 3) 

% *******************  RULES
%{a(0)}.
__initial(0).
{l_4}. % Choice for theory added manually
:- not l_4.
:- l_4, not l_4.
:- not l_4, l_4.
%{a(1)}.
:- l_4, not a(1).
:- not l_4, a(1).
%{a(2)}.
% ******************* AUX LITERALS
% l_4 := &tel(0){(>a)}
```

But this does not follow to more complex formulas and all my tries to make it work have failed. 
My idea was to try not to bother you with this experiment but I would appreciate some insight, first on weather this is possible (or maybe there was already a more straight forward way to do it that I didn't see). I feel my biggest issue is understanding this use of externals (I only get their use for the final step which will change when done incrementally). 


Some more examples in case you want to follow up how it looks for eventually. 
```
#program always.
{a}.
#program initial.
:- not &tel{ >? a}.
```
Fail because the literal that is never assigned to free makes the eventually to be required in all steps. 
```
% SAT (Setp 3) 

% *******************  RULES
%{a(0)}.
__initial(0).
{l_4}. % Choice for theory added manually
:- not l_4.
:- not l_4, a(0).
:- not a(0), not #false, l_4.
%:- not l_4, #false.
:- l_4, not l_4.
:- not l_4, l_4.
%{a(1)}.
{l_9}.
:- not l_9, a(1).
:- not a(1), not #false, l_9.
%:- not l_9, #false.
%:- #false, not l_9.
:- not #false, l_9.
%{a(2)}.
{l_13}.
:- not l_13, a(2).
:- not a(2), not #false, l_13.
%:- not l_13, #false.
%:- #false, not l_13.
:- not #false, l_13.
% ******************* AUX LITERALS
% l_4 := &tel(0){(>?a)}
% l_9 := (>?(a()))
% l_13 := (>?(a()))
```

If I keep the assignment of the external to free and ignore the free rules I get:

```
% SAT (Setp 3) 

% *******************  RULES
%{a(0)}.
__initial(0).
{l_4}. % Choice for theory added manually
:- not l_4.
:- not l_4, a(0).
% :- not a(0), not free, l_4.
% :- not l_4, free.
:- l_4, not l_4.
:- not l_4, l_4.
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
```

Which seams closer but forces `a(2)`.