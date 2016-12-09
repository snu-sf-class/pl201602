Require Export P14.



(** **** Exercise: 3 stars, optional (inequiv_exercise)  *)
(** Prove that an infinite loop is not equivalent to [SKIP] *)

Lemma inequiv_never_end: forall st st',
  ~ (WHILE BTrue DO SKIP END) / st \\ st'.
Proof.
unfold not.
remember (WHILE BTrue DO SKIP END) as c.
intros.
induction H ; try (inversion Heqc ; fail).
- inversion Heqc. subst. simpl in H. inversion H.
- apply IHceval2 in Heqc. assumption.
Qed.


Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
unfold not.
unfold cequiv.
intros.
assert (H'' := inequiv_never_end empty_state empty_state).
apply H''.
apply H.
constructor.
Qed.

