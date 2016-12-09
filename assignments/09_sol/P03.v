Require Export P02.



(** ** Exercise: Power Series *)

(** **** Exercise: 4 stars, optional (dpow2_down)  *)
(** Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

  X ::= 0;;
  Y ::= 1;;
  Z ::= 1;;
  WHILE X <> m DO
    Z ::= 2 * Z;;
    Y ::= Y + Z;;
    X ::= X + 1
  END

    Write a decorated program for this. *)

Lemma pow_to_add: forall m,
    pow 2 m + pow 2 m = pow 2 (m+1).
Proof.
induction m.
- reflexivity.
- simpl. rewrite <- IHm. omega.
Qed.

Theorem dopw2_down_correct: forall m,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 1;;
  Z ::= ANum 1;;
  WHILE BNot (BEq (AId X) (ANum m)) DO
    Z ::= AMult (ANum 2) (AId Z);;
    Y ::= APlus (AId Y) (AId Z);;
    X ::= APlus (AId X) (ANum 1)
  END
  {{ fun st => st Y = pow 2 (S m) - 1 }}.
Proof.
intros m.
eapply hoare_seq.
eapply hoare_seq.
eapply hoare_seq with
(Q := fun st => st Z = pow 2 (st X) /\ (st Y = 2 * (st Z) - 1)).
eapply hoare_consequence_post.
apply hoare_while.
- eapply hoare_consequence_pre.
  eapply hoare_seq.
  eapply hoare_seq.
  apply hoare_asgn.
  apply hoare_asgn.
  apply hoare_asgn.
  unfold bassn, assn_sub, t_update.
  simpl.
  intros st [[H1 H2] H3].
  split.
  + rewrite H1. rewrite <- plus_n_O. apply pow_to_add.
  + rewrite H2. repeat rewrite <- plus_n_O. omega.
- unfold bassn, assn_sub, t_update.
  simpl.
  intros st [[H1 H2] H3].
  rewrite H2. rewrite H1.
  apply eq_true_negb_classical in H3.
  apply beq_nat_true_iff in H3.
  rewrite H3.
  omega.
- apply hoare_asgn.
- apply hoare_asgn.
- eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.
  unfold bassn, assn_sub, t_update.
  simpl. omega.
Qed.

