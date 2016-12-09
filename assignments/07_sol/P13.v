Require Export P12.



Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
Hint Constructors ceval.
unfold ctrans_sound.
unfold cequiv.
split.
- intros H.
  induction H ; 
    try (simpl; eauto ; fail) ; (* SKIP, E_Seq *)
    try (simpl; rewrite optimize_0plus_aexp_sound in H; eauto; fail) ; (* E_Ass *)
    try (simpl; rewrite optimize_0plus_bexp_sound in H; eauto; fail). (* Others *)
- intros H.
  remember (optimize_0plus_com c) as c' eqn:Heqc'.
  generalize dependent Heqc'.
  generalize dependent c.
  induction H as [st | st a1 n x | c1 c2 st st' st'' | st st' b c1 c2 |
                  st st' b c1 c2 | b st c' | st st' st'' b c'] ;
    intros c Heqc';
    destruct c; try (simpl in Heqc'; inversion Heqc'; fail); try (eauto; fail).
  + simpl in Heqc'. inversion Heqc'.
    rewrite H2 in H. rewrite <- optimize_0plus_aexp_sound in H. eauto.
  + simpl in Heqc'. inversion Heqc'.
    apply IHceval1 in H2. apply IHceval2 in H3. eauto.
  + simpl in Heqc'. inversion Heqc'. rewrite H2 in H. 
    rewrite <- optimize_0plus_bexp_sound in H. eauto.
  + simpl in Heqc'. inversion Heqc'. rewrite H2 in H.
    rewrite <- optimize_0plus_bexp_sound in H. eauto.
  + simpl in Heqc'. inversion Heqc'. rewrite H1 in H.
    rewrite <- optimize_0plus_bexp_sound in H. eauto.
  + simpl in Heqc'. inversion Heqc'. rewrite H3 in H.
    rewrite <- optimize_0plus_bexp_sound in H. eauto.
Qed.

