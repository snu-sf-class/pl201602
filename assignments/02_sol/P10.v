Require Export P09.


Lemma natlist_nil : forall l : natlist,
  l ++ [] = l.
Proof.
intros. induction l. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.

Lemma snoc_append : forall (l1 l2 : natlist) (n : nat),
  snoc (l1 ++ l2) n = l1 ++ (snoc l2 n).
Proof.
intros.
induction l1.
- simpl. reflexivity.
- simpl. rewrite IHl1. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
intros.
induction l1.
- simpl. rewrite natlist_nil. reflexivity.
- simpl. rewrite IHl1. rewrite snoc_append. reflexivity.
Qed.

