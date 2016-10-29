

Require Export P04.



Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
intros X test x l lf.
induction l as [ | x' l' IHl].
- intros H. simpl in H. inversion H.
- simpl. 
  intros.
  remember (test x') as t.
  destruct t.
  + inversion H. rewrite <- H1. symmetry. apply Heqt.
  + apply IHl. assumption.
Qed.

