Require Export P03.



Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
intros.
split.
- intros.
  destruct H.
  split. left. assumption. left. assumption.
  destruct H.
  split. right. assumption. right. assumption.
- intros.
  inversion H.
  inversion H0. 
    + left. assumption.
    + inversion H1.
      left. assumption.
      right. split ; assumption.
Qed.

