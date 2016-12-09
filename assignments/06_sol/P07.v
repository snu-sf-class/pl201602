Require Export P06.

Theorem le_trivial: forall n1 n2,
    n1 <= n1 + n2.
Proof.
intros.
induction n2.
- rewrite <- plus_n_O. constructor.
- rewrite <- plus_n_Sm. constructor. assumption.
Qed.

Theorem plus_comm: forall n1 n2,
    n1 + n2 = n2 + n1.
Proof.
intros.
induction n1.
- rewrite <- plus_n_O. reflexivity.
- rewrite <- plus_n_Sm. simpl. rewrite IHn1. reflexivity.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
unfold lt.
induction m.
- intros. inversion H.
- intros.
  inversion H.
  + split.
    * rewrite <- plus_Sn_m.
      apply le_trivial.
    * rewrite plus_n_Sm.
      rewrite plus_comm.
      apply le_trivial.
  + apply IHm in H1.
    inversion H1.
    split.
    * constructor. assumption.
    * constructor. assumption.
Qed.
