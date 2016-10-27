Require Export P07.



(** Hint: You may need to first state and prove some lemma about snoc and rev. *)

Lemma rev_snoc : forall (h:nat) (t:natlist),
  h::(rev t) = rev (snoc t h).
Proof.
intros.
induction t.
- simpl. reflexivity.
- simpl. intros.
  rewrite <- IHt.
  simpl.
  reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
intros.
induction l.
- reflexivity.
- simpl. rewrite <- rev_snoc. rewrite IHl. reflexivity.
Qed.

