Require Export P05.



(** **** Problem #2 : 3 stars, advanced (alternate) *)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  FILL_IN_HERE.

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. exact FILL_IN_HERE. Qed.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
Proof. exact FILL_IN_HERE. Qed.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
Proof. exact FILL_IN_HERE. Qed.
Example test_alternate4:        alternate [] [20;30] = [20;30].
Proof. exact FILL_IN_HERE. Qed.

