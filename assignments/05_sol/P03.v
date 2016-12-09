Require Export P02.



Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
intros.
unfold not.
intros.
apply H in H1.
apply H0 in H1.
assumption.
Qed.

