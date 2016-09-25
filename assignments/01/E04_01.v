Require Import P04.

Check zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
