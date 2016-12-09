Require Export P09.



Theorem loop_never_stops : forall st st' c,
    ~((WHILE BTrue DO c END) / st \\ st').
Proof.
intros st st' c contra. unfold loop in contra.
remember (WHILE BTrue DO c END) as loopdef eqn:Heqloopdef.
induction contra ; try inversion Heqloopdef.
subst. simpl in H. inversion H.
subst. apply IHcontra2. apply Heqloopdef.
Qed.

(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** Complete the [WHILE] case of the following proof. *)

Check CAss_congruence.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).

      (** (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)

    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  - (* CWHILE *)
    remember (fold_constants_com c) as c'.
    assert (Hbsound := fold_constants_bexp_sound b).
    remember (fold_constants_bexp b) as b'.
    destruct b' ; try (apply CWhile_congruence with (c1 := c) (c1' := c') in Hbsound ; assumption ; assumption).
    + (* BTrue *) 
      unfold cequiv.
      intros. split.
      * intros H.
        apply CWhile_congruence with (c1 := c) (c1' := c) in Hbsound.
        apply Hbsound in H. apply loop_never_stops in H. inversion H.
        apply refl_cequiv.
      * intros.
        apply loop_never_stops in H. inversion H.
    + (* BFalse *)
      apply CWhile_congruence with (c1 := c) (c1' := c) in Hbsound.
      * unfold cequiv.
        intros. split.
        ** intros H. apply Hbsound in H. inversion H.
           *** subst. apply E_Skip.
           *** simpl in H2. inversion H2.
        ** intros H. inversion H. subst. apply Hbsound. apply E_WhileEnd. reflexivity.
      * apply refl_cequiv.
Qed.

