Require Export P03.



(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
intros.
unfold is_wp.
split.
- eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold "->>".
  auto.
- unfold "->>".
  intros.
  unfold hoare_triple in H.
  unfold assn_sub.
  apply (H st).
  constructor.
  reflexivity. assumption.
Qed.

