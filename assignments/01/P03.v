Require Export P02.

(** **** Problem #3 : 2 stars (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
