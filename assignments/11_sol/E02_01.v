Require Import P02.


Check progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

