#program always.

% Choose to either shoot or load the gun
shoot | load.

% Propagate action effects
loaded   :- load.
unloaded :- shoot, not fail.

% Frame axioms
loaded   :-   'loaded, not unloaded.
unloaded :- 'unloaded, not   loaded.

% If we make two shots with a gun that was never loaded, then it will eventually fail.
% (Note the necessary double negation, which is a limitation of the current telingo implementation.)
&tel { >? fail } :- not not &tel { shoot & < <? shoot & <* unloaded }.

#program final.

% select traces where shooting a gun failed
:- not &tel { shoot & < loaded & loaded }.


