Require Import P05.



Check 
(conj test_hd_opt1
(test_hd_opt2))
:
hd_opt [1;2] = Some 1 /\
hd_opt  [[1];[2]]  = Some [1].

