Require Export P03.



(** Multiplication: *)

Definition c_mult (n m : c_nat) : c_nat :=
  fun (X:Type) f x => n X (m X f) x.

Example c_mult_1 : c_mult c_one c_one = c_one.
Proof. reflexivity. Qed.

Example c_mult_2 : c_mult c_zero (c_plus c_three c_three) = c_zero.
Proof. reflexivity. Qed.

Definition c_plus (n m : c_nat) : c_nat :=
  fun (X:Type) f x => m X f (n X f x).

Example c_mult_3 : c_mult c_two c_three = c_plus c_three c_three.
Proof. reflexivity. Qed.

