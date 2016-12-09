Require Export P01.



Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
intros.
destruct n; destruct m.
left. reflexivity.
left. reflexivity.
right. reflexivity.
simpl in H. inversion H.
 Qed.

