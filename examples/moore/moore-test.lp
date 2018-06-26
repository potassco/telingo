%%%% A test execution
#program initial.
testing.
:- not &tel{
   &initial
 ;> fetch(a)
 ;> fetch(a)
 ;> fetch(b)
 ;> fetch(b)
 ;> fetch(a)
  & &final
}.
