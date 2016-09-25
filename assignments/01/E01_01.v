Require Import P01.

Check 
(conj test_factorial1
(test_factorial2))
:
(factorial 3) = 6 /\
(factorial 5) = 10 * 12.
