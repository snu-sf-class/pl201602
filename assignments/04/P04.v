Require Export P03.


(** Multiplication: *)

Definition c_mult (n m : c_nat) : c_nat :=
  FILL_IN_HERE.

Example c_mult_1 : c_mult c_one c_one = c_one.
Proof. exact FILL_IN_HERE. Qed.

Example c_mult_2 : c_mult c_zero (c_plus c_three c_three) = c_zero.
Proof. exact FILL_IN_HERE. Qed.

(** Oct. 20 : You have to copy definition of c_plus here from P03.v. **)

Example c_mult_3 : c_mult c_two c_three = c_plus c_three c_three.
Proof. exact FILL_IN_HERE. Qed.

