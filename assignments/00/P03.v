Require Export P02.

(** **** Problem #3: 2 stars (blt_nat) *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Use [Fixpoint] to define it. *)

Fixpoint blt_nat (n m : nat) : bool :=
  FILL_IN_HERE.

Example test_blt_nat1:             (blt_nat 2 2) = false.
exact FILL_IN_HERE. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
exact FILL_IN_HERE. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
exact FILL_IN_HERE. Qed.
(** [] *)
