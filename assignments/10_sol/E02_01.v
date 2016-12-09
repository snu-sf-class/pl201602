Require Import P02.


Check step__eval : forall t t' n,
     t ==> t' ->
     t' \\ n ->
     t \\ n.

