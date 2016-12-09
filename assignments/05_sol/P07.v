Require Export P06.



Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
intros.
split.
- intros.
  generalize dependent y.
  induction l.
  + intros. simpl in H. exfalso. assumption.
  + intros. simpl in H. 
    inversion H.
    * exists a. 
      split. 
      apply H0.  
      simpl. left. reflexivity.
    * apply IHl in H0. 
      inversion H0. 
      exists x. inversion H1. 
      split. assumption. simpl. right. assumption. 
- intros.
  induction l as [ | a l IHl].
  + simpl in H. inversion H. inversion H0. exfalso. assumption.
  + simpl.
    inversion H.
    inversion H0. simpl in H2.
    inversion H2.
      * left. subst. reflexivity.
      * right. apply IHl. exists x. 
        split ; assumption.
Qed.
