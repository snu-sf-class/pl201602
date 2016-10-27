Require Export D.



(** **** Problem #7 : 2 stars (split) *)
(** The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
  FILL_IN_HERE.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. exact FILL_IN_HERE. Qed.

Theorem split_map: forall X Y (l: list (X*Y)),
   fst (split l) = map fst l.
Proof.
  exact FILL_IN_HERE.
Qed.

