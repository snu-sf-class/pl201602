Require Import P01.



Check evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).

