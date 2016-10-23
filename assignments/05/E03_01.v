Require Import P03.



Check contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).

