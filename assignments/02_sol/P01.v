Require Export D.


Theorem plus_zero : forall n : nat, n = n + 0.
Proof.
induction n. reflexivity. simpl. rewrite <- IHn.  reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. 
intros.
induction n.
- simpl. apply plus_zero.
- simpl. rewrite IHn. apply plus_n_Sm.
Qed.
