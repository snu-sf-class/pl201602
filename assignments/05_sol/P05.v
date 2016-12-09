Require Export P04.



Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
 intros.
 unfold not.
intros.
inversion H0.
assert (Hx := H x).
apply H1 in Hx.
assumption.
Qed.