Require Export P02.



(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] transformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  FILL_IN_HERE.

Example optimize_0plus_b_example1:
  optimize_0plus_b (BEq 
     (AMult (APlus (ANum 0) (APlus (ANum 0) (ANum 3)))
            (AMinus (ANum 5) (APlus (ANum 0) (ANum 1))))
     (APlus (ANum 2)
            (APlus (ANum 0)
                   (APlus (ANum 0) (ANum 1)))))
  = (BEq (AMult (ANum 3) (AMinus (ANum 5) (ANum 1)))
         (APlus (ANum 2) (ANum 1))).
Proof. exact FILL_IN_HERE. Qed.  

Theorem optimize_0plus_b_sound : forall st b,
  beval st (optimize_0plus_b b) = beval st b.
Proof. exact FILL_IN_HERE. Qed.

