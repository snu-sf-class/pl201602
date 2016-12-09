Require Export P01.



(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if_wp]: *)

Lemma Y_noteq_Z: Y<>Z.
Proof. unfold not. intros. inversion H. Qed.
Lemma X_noteq_Z: X<>Z.
Proof. unfold not. intros. inversion H. Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
eapply hoare_consequence_pre. 
- apply hoare_if_wp.
  apply hoare_asgn.
  apply hoare_asgn.
- unfold assn_sub.
  unfold assert_implies.
  simpl.
  split.
  + intros.
    unfold t_update.
    simpl.
    apply le_plus_minus.
    apply leb_complete in H0.
    assumption.
  + intros.
    unfold t_update.
    simpl.
    reflexivity.
Qed.

