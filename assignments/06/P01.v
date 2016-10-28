Require Export D.



Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof. exact FILL_IN_HERE. Qed.

