Require Export P01.

(** **** Exercise: 3 stars, recommended (t_update_permute)  *)
(** Use [beq_idP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)
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

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
intros.
unfold not in H.
unfold t_update.
apply functional_extensionality.
intros.
destruct (beq_id x1 x, beq_id x2 x) eqn:Heqn ; inversion Heqn.
destruct b ; destruct b0 ; rewrite H1 ; rewrite H2 ; try reflexivity.
- apply beq_id_eq in H1. apply beq_id_eq in H2. rewrite <- H1 in H2. apply H in H2. inversion H2.
Qed.