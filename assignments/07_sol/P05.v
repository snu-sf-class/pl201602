Require Export P04.

Print loop.

(** **** Exercise: 3 stars, recommended (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.
  induction contra ; try inversion Heqloopdef.
  subst. simpl in H. inversion H.
  subst. apply IHcontra2. apply Heqloopdef.
Qed.

