Require Export D.

Fixpoint snoc (l : list nat) (n : nat) : list nat := 
  match l with 
  | nil => [n]
  | h::t => h::(snoc t n)
  end.

Lemma snoc_append : forall (l : list nat) n,
    l ++ [n] = snoc l n.
Proof.
intros.
induction l.
reflexivity.
simpl. rewrite IHl. reflexivity.
Qed.

Lemma rev_snoc : forall (l l': list nat) n, 
    (n :: l) = l' -> rev l' = snoc (rev l) n.
Proof. 
intros.
+ simpl. 
  intros.
  destruct l'.
- inversion H.
- inversion H. subst. simpl. rewrite snoc_append. reflexivity.
Qed.

Lemma rev_snoc2 : forall (l:list nat) n, 
    n::(rev l) = rev (snoc l n).
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite -> snoc_append.
rewrite <- IHl.
simpl.
rewrite -> snoc_append.
reflexivity.
Qed.

Lemma rev_rev : forall (l : list nat), l = rev (rev l).
Proof.
intros.
induction l.
  + simpl. reflexivity.
  + simpl. rewrite -> snoc_append. rewrite <- rev_snoc2. rewrite <- IHl. reflexivity.
Qed.

(** **** Problem #13 : 3 stars (apply_exercise1)  *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l'.
  intros.
  rewrite -> H.
  rewrite <- rev_rev.
  reflexivity.
Qed.
