Require Import P03.



Check halve_type: empty |- halve \in TArrow TNat TNat.

Check halve_10: tapp halve (tnat 10) ==>* tnat 5.

Check halve_11: tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.


