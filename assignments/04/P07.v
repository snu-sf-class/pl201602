Require Export P02.



Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - exact FILL_IN_HERE. 
  - exact FILL_IN_HERE.
Qed.

