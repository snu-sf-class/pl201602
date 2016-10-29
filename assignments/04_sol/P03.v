Require Export P02.



(** Addition of two natural numbers: *)

Definition c_plus (n m : c_nat) : c_nat :=
  fun (X:Type) f x => n X f (m X f x).

Example c_plus_1 : c_plus c_zero c_one = c_one.
Proof. reflexivity. Qed.

Example c_plus_2 : c_plus c_two c_three = c_plus c_three c_two.
Proof. reflexivity. Qed.

Example c_plus_3 :
  c_plus (c_plus c_two c_two) c_three = c_plus c_one (c_plus c_three c_three).
Proof. reflexivity. Qed.

