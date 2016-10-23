Require Export P04.



Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. exact FILL_IN_HERE. Qed.

