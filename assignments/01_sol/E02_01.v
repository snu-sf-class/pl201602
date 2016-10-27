Require Import P02.

Check 
(conj test_blt_nat1
(conj test_blt_nat2
(test_blt_nat3)))
:
(blt_nat 2 2) = false /\
(blt_nat 2 4) = true /\
(blt_nat 4 2) = false.
