Require Export P10.



Lemma aeval_opt0plus_aplus:forall st e1 e2,
e1 <> (ANum 0)
-> e2 <> (ANum 0)
-> aeval st (optimize_0plus_aexp (APlus e1 e2)) = aeval st (APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)).
Proof.
unfold not.
intros.
destruct e1 eqn:Heqe1 ; (* When e1 is not ANum *)
    try (destruct e2 eqn:Heqe2 ; try (simpl ; reflexivity) ;
         destruct n; try reflexivity; simpl; omega).
  - destruct n ; try reflexivity. (* 0 + a => a *)
    + destruct e2 eqn:Heqe2 ; try (simpl ; reflexivity).
      destruct n0 ; try reflexivity ; simpl ; omega.
Qed.

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
unfold atrans_sound.
unfold aequiv.
(* fail tactic aborts immediately if any goal is left *)
induction a ; try (simpl ; auto ; fail).
- intros.
  + (* Goal : aeval st (APlus a1 a2) = aeval st (optimize_0plus_aexp (APlus a1 a2)) *)
    destruct a1 eqn:Heqa1.
    * (* Goal : aeval (APlus (ANum n) a2) = *)
      (* aeval st (optimize_0plus_aexp (APlus (ANum n) a2)) *)
      destruct n. 
      ++ simpl. rewrite IHa2. reflexivity.
      ++ destruct a2 eqn:Heqa2 ; 
            try (simpl ; reflexivity); (* a2 = AId *)
            try (simpl ; simpl in IHa2 ; auto ; fail). (* a2 = APlus, AMinus, AMult *)
         ** (* Goal : aeval st (APlus (ANum (S n)) (ANum n0)) = 
                      aeval st (optimize_0plus_aexp (APlus (ANum (S n)) (ANum n0))) *)
            destruct n0; simpl; omega.
    * (* Goal : aeval st (APlus (AId i) a2) = *)
      (* aeval st (optimize_0plus_aexp (APlus (AId i) a2)) *)
      destruct a2 eqn:Heqa2 ; try (simpl ; simpl in IHa2; auto; fail).
      ++ destruct n ; try (simpl ; omega).
    * (* Goal : aeval st (APlus (APlus a3 a4) a2) = *)
      (* aeval st (optimize_0plus_aexp (APlus (APlus a3 a4) a2)) *)
      rewrite <- Heqa1. rewrite <- Heqa1 in IHa1.
      destruct a2 eqn:Heqa2 ; try
         (rewrite aeval_opt0plus_aplus ; try (unfold not; subst; intro H; inversion H);
          simpl; simpl in IHa2; auto; fail). 

      ++ destruct n; simpl; rewrite Heqa1 in *; rewrite IHa1; try omega; auto.
    * (* Goal : aeval st (APlus (AMinus a3 a4) a2) = 
                aeval st (optimize_0plus_aexp (APlus (AMinus a3 a4) a2)). *)
      rewrite <- Heqa1. rewrite <- Heqa1 in IHa1.
      destruct a2 eqn:Heqa2 ; try
         (rewrite aeval_opt0plus_aplus; try (unfold not; subst; intro H; inversion H);
          simpl; simpl in IHa2; auto; fail).
      ++ destruct n; simpl; rewrite Heqa1 in *; rewrite IHa1 ; try omega ; auto.
    * (* Goal : aeval st (APlus (AMult a3 a4) a2) = 
                aeval st (optimize_0plus_aexp (APlus (AMult a3 a4) a2)). *)
      rewrite <- Heqa1. rewrite <- Heqa1 in IHa1.
      destruct a2 eqn:Heqa2 ; try
         (rewrite aeval_opt0plus_aplus; try (unfold not; subst; intro H; inversion H);
          simpl; simpl in IHa2; auto; fail).
      ++ destruct n; simpl; rewrite Heqa1 in *; rewrite IHa1 ; try omega ; auto.
Qed.
