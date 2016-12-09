Require Export P04.



(** **** Exercise: 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
intros.
induction H.
- simpl. assumption.
- simpl. constructor. assumption.
Qed.

