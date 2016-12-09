Require Export P07.



(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | nil => True
  | h::t => (P h) /\ (All P t)
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T.
  split.
  - induction l.
    + simpl. intros. reflexivity.
    + intros. simpl in H. simpl.
      split. apply H. left. reflexivity.
      apply IHl. intros. apply H. right. apply H0.
  - induction l.
    + intros. simpl in H0. inversion H0.
    + intros. simpl in H0. inversion H0. 
      * simpl in H. inversion H. subst. assumption.
      * apply IHl. simpl in H. inversion H. assumption.
        assumption.
Qed.
