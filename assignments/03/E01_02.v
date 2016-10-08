Require Import P01.



Check split_map: forall X Y (l: list (X*Y)),
   fst (split l) = map fst l.

