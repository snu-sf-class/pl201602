Require Export P13.

Lemma beq_mynat : forall n, beq_nat n n = true.
Proof.
intros.
induction n ; simpl ; try assumption ; try reflexivity.
Qed.

Lemma beq_id_eq : forall x1 x2, x1 = x2 <-> beq_id x1 x2 = true.
Proof.
intros.
split.
- intros. destruct x1, x2. intros. inversion H. simpl. apply beq_mynat.
- intros. destruct x1, x2.
  generalize dependent n0.
  induction n.
  + intros. simpl in H. destruct n0. reflexivity.  
    inversion H.
  + intros. destruct n0. inversion H. simpl in H. apply IHn in H. inversion H.
 reflexivity.
Qed.

Lemma beq_id_refl : forall x, beq_id x x = true.
Proof.
intros.
apply beq_id_eq.
reflexivity.
Qed.

Lemma t_update_eq: forall i (st:total_map nat) v,
    (t_update st i v) i = v.
Proof.
intros.
unfold t_update.
rewrite beq_id_refl.
reflexivity.
Qed.

Lemma vnu_or: forall i a1 a2,
    var_not_used_in_aexp i (subst_aexp i a1 a2) ->
    var_not_used_in_aexp i a1 \/ var_not_used_in_aexp i a2.
Proof.
induction a2; simpl; intros;
  try (auto; fail);
  try (inversion H;
       apply IHa2_1 in H2; apply IHa2_2 in H3;
       destruct H2; destruct H3; auto;
       right; constructor; assumption).
- destruct (beq_id i i0) eqn:Heqi; auto.
Qed.

Lemma subst_equiv_aevaleq: forall i st a2 a1,
    var_not_used_in_aexp i a1 ->
    aeval st a1 = st i ->
    aeval st (subst_aexp i a1 a2) = aeval st a2.
Proof.
intros i st a2.
induction a2; try reflexivity;
  try (intros; simpl;
       rewrite IHa2_1; try assumption;
       rewrite IHa2_2; try assumption;
       reflexivity).
- intros.
  simpl.
  destruct (beq_id i i0) eqn:Heqi.
  + apply beq_id_eq in Heqi. subst. assumption.
  + reflexivity.
Qed.

Lemma vnu_aevaleq: forall st i v a,
    var_not_used_in_aexp i a ->
    aeval (t_update st i v) a = aeval st a.
Proof.
intros.
induction H; try (simpl; auto).
- destruct (beq_id i Y) eqn:Heqn.
  + apply beq_id_eq in Heqn.
    apply H in Heqn. inversion Heqn.
  + unfold t_update. simpl. rewrite Heqn. reflexivity.
Qed.

Lemma vnu_subst_eq: forall i a1 a2,
    var_not_used_in_aexp i a1 ->
    subst_aexp i a2 a1 = a1.
Proof.
intros.
induction H; 
  try (simpl; reflexivity);
  try (simpl;
       rewrite IHvar_not_used_in_aexp1;
       rewrite IHvar_not_used_in_aexp2;
       reflexivity).
- destruct (beq_id i Y) eqn:Heqn.
  + apply beq_id_eq in Heqn.
    apply H in Heqn.
    inversion Heqn.
  + simpl. rewrite Heqn. reflexivity.
Qed.

Lemma subst_equiv: forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 (subst_aexp i1 a1 a2) ->
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
Proof.
intros.
apply vnu_or in H.
destruct H.
- unfold cequiv.
  split; intros; inversion H0; inversion H3; inversion H6; subst.
  + eapply E_Seq. apply H3.
    apply E_Ass.
    rewrite subst_equiv_aevaleq ; try reflexivity.
    assumption.
    rewrite vnu_aevaleq with (i := i1) (v := aeval st a1); try assumption; try auto.
    rewrite t_update_eq. reflexivity.
  + eapply E_Seq. apply H3. 
    apply E_Ass.
    rewrite subst_equiv_aevaleq ; try reflexivity.
    assumption.
    rewrite vnu_aevaleq with (i := i1) (v := aeval st a1); try assumption ; try auto.
    rewrite t_update_eq. reflexivity.
- apply CSeq_congruence. apply refl_cequiv.
  apply CAss_congruence.
  unfold aequiv.
  rewrite vnu_subst_eq; try reflexivity;
    try assumption. 
Qed.

