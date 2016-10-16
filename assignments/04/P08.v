Require Export P03.



Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof. exact FILL_IN_HERE. Qed.

