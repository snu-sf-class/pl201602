Require Export P02.



Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros.  destruct m. reflexivity. inversion H.
  - simpl. intros. rewrite <- plus_n_Sm in H. 
    destruct m. inversion H. simpl in H. rewrite <- plus_n_Sm in H.
    inversion H. apply IHn' in H1. subst. reflexivity.
Qed.

