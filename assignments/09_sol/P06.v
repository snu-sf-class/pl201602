Require Export P05.



Theorem hoare_skip_weakest : forall Q, 
  is_wp Q SKIP Q.
Proof.
unfold is_wp.
split.
- unfold hoare_triple.
  intros.
  inversion H.
  subst. assumption.
- unfold "->>".
  unfold hoare_triple.
  intros.
  apply H with (st := st).
  constructor. assumption.
Qed.

Theorem hoare_seq_weakest : forall P Q R c1 c2, 
  is_wp P c1 Q ->
  is_wp Q c2 R ->
  is_wp P (c1 ;; c2) R.
Proof.
Hint Constructors ceval.
unfold is_wp.
intros P Q R c1 c2 [H11 H12] [H21 H22].
split.
- apply hoare_seq with (Q := Q); assumption.
- intros P' P'H.
  unfold hoare_triple in *.
  apply H12.
  intros.
  eapply H22.
  + intros. eauto.
  + unfold assert_implies in *. eauto.
Qed.

