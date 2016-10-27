Require Export P08.



Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
induction l.
- reflexivity.
- simpl. intros. rewrite <- IHl. reflexivity.
Qed.

