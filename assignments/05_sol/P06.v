Require Export P05.



Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
intros.
split.
- intros.
  inversion H.
  destruct H0.
  + left. exists x. assumption.
  + right. exists x. assumption.
- intros.
  destruct H.
  inversion H.
  + exists x. left. assumption.
  + inversion H.
exists x. right. assumption.
Qed.
