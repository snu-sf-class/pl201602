Require Export D.


Lemma evenb_flip: forall n,
    evenb (S n) = negb (evenb n).
Proof. 
induction n.
- auto.
- simpl. simpl in IHn. rewrite IHn.
  destruct (evenb n) ; auto.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
intros.
induction n.
- exists 0.
  reflexivity.
- destruct IHn.
  destruct (evenb n) eqn:Heqev.
  + exists x. rewrite evenb_flip. rewrite Heqev. simpl. auto.
  + exists (S x). rewrite evenb_flip. rewrite Heqev. simpl. auto.
Qed.

