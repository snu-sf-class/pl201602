Require Import P01.



Check rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.

