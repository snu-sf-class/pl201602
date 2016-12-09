Require Export P01.



(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)

Fixpoint beq_list {A} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | h1::t1, h2::t2 => andb (beq h1 h2) (beq_list beq t1 t2)
  | [], h2::t2 => false
  | h1::t1, [] => false
  | [], [] => true
  end.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
intros.
generalize dependent l2.
induction l1.
- intros. destruct l2. split ; reflexivity. simpl. split. intros. inversion H0. intros. inversion H0.
- intros.
  destruct l2.
  + simpl. split ; intros ; inversion H0.
  + assert (H := H a a0).
    inversion H.
    assert (IHl := IHl1 l2).
    inversion IHl.
    split.
    * intros HH.
      simpl in HH.
      remember (beq a a0) as aeqv.
      remember (beq_list beq l1 l2) as beqv.
      destruct aeqv ; destruct beqv ; try simpl in HH ; try inversion HH.
      assert (TT : true = true).
        reflexivity.
      assert (TT2 := TT).
      apply H0 in TT.
      apply H2 in TT2.
      subst. reflexivity.
    * intros HH.
      remember (beq a a0) as aeqv.
      remember (beq_list beq l1 l2) as beqv.
      destruct aeqv ; destruct beqv.
      inversion HH.
      subst.
      simpl. rewrite <- Heqbeqv. rewrite <- Heqaeqv. reflexivity.
      assert (HL2 : l2 = l2). reflexivity.
      inversion HH. apply H3 in H6. inversion H6.
      inversion HH. apply H1 in H5. inversion H5.
      inversion HH. apply H3 in H6. inversion H6.
Qed.
