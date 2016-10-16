Require Export P01.



Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  y = z.
Proof. exact FILL_IN_HERE. Qed.

