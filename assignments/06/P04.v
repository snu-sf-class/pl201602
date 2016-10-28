Require Export P03.



(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)

Theorem excluded_middle_to_double_negation_elimination:
  excluded_middle -> double_negation_elimination.
Proof. exact FILL_IN_HERE. Qed.

Theorem double_negation_elimination_to_excluded_middle:
  double_negation_elimination -> excluded_middle.
Proof. exact FILL_IN_HERE. Qed.

