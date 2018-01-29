#program dynamic.
shoot | load | wait.

loaded :- load.
loaded :- 'loaded, not unloaded.
unloaded :- shoot, 'loaded, not broken.
unloaded :- 'unloaded, not loaded.

:- load, 'loaded.

% determine if we failed to shoot
failed :- 'failed.
failed :- loaded, shoot.

% two unloaded shots will break the gun
fail_shot1 :- unloaded, shoot.
fail_shot1 :- 'fail_shot1.

fail_shot2 :- 'fail_shot1, unloaded, shoot.
fail_shot2 :- 'fail_shot2.

broken :- fail_shot2.

#program final.
% select traces where the gun broke
:- not failed.

#program initial.
unloaded.
