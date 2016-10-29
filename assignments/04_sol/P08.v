Require Export P03.



Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
intros.
generalize dependent n.
induction l.
- simpl. intros. reflexivity.
- intros. destruct n. 
  + simpl in H. inversion H. 
  + simpl in H. inversion H.
    assert (H2 := H1).
    apply IHl in H1.
    simpl. subst. assumption.
Qed.

