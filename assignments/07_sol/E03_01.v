Require Import P03.



Check optimize_0plus_b_example1:
  optimize_0plus_b (BEq 
     (AMult (APlus (ANum 0) (APlus (ANum 0) (ANum 3)))
            (AMinus (ANum 5) (APlus (ANum 0) (ANum 1))))
     (APlus (ANum 2)
            (APlus (ANum 0)
                   (APlus (ANum 0) (ANum 1)))))
  = (BEq (AMult (ANum 3) (AMinus (ANum 5) (ANum 1)))
         (APlus (ANum 2) (ANum 1))).

Check optimize_0plus_b_sound : forall st b,
  beval st (optimize_0plus_b b) = beval st b.

