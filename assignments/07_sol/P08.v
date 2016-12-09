Require Export P07.



(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
intros.
unfold cequiv.
split.
- intros.
  inversion H2 ; subst ; rewrite H in H8.
  apply H0 in H9. eapply E_IfTrue ; assumption.
  apply H1 in H9. eapply E_IfFalse ; assumption.
- intros.
  inversion H2 ; subst ; rewrite <- H in H8.
  apply H0 in H9. eapply E_IfTrue ; assumption.
  apply H1 in H9. eapply E_IfFalse ; assumption.
Qed.