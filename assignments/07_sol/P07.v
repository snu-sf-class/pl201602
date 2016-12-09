Require Export P06.



(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
intros.
unfold cequiv.
split ; intros ; inversion H1 ; apply H in H4 ; apply H0 in H7.
- eapply E_Seq. apply H4. apply H7.
- eapply E_Seq. apply H4. apply H7. 
Qed.