Require Import P06.



Check 
(conj test_alternate1
(conj test_alternate2
(conj test_alternate3
(test_alternate4))))
:
alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6] /\
alternate [1] [4;5;6] = [1;4;5;6] /\
alternate [1;2;3] [4] = [1;4;2;3] /\
alternate [] [20;30] = [20;30].

