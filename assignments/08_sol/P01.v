Require Export D.



(** **** Exercise: 4 stars (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

Lemma two_equals_three: t_update empty_state X 1 X = 2 -> False.
Proof.
unfold t_update.
rewrite <- beq_id_refl.
intros.
inversion H.
Qed.

Theorem hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.
Proof.
  exists (APlus (AId X) (ANum 1)).
  unfold not.
  intros.
  simpl in H.
  assert (H' := H empty_state (t_update empty_state X 1)).
  simpl in H'.
  apply two_equals_three in H'.
  - assumption.
  - eapply E_Ass.
    reflexivity.
  - constructor.
Qed.
