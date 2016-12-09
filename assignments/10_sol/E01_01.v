Require Import P01.


Check eval__multistep : forall t n,
  t \\ n -> t ==>* C n.

