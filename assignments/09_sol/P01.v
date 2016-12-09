Require Export D.



(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Lemma fact_discompose: forall x,
  x <> 0 -> fact x = x * fact (x-1).
Proof.
  intros.
  destruct x. 
  - exfalso. apply H. reflexivity.
  - simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Theorem factorial_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
intros.
eapply hoare_consequence.
eapply hoare_seq with (Q := fun st => (st Y * fact (st X)) = fact m).
- eapply hoare_while.
  eapply hoare_consequence_pre.
  eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_asgn.
  unfold bassn.
  unfold assert_implies.
  unfold assn_sub.
  unfold t_update.
  simpl.
  intros st [H1 H2].
  apply negb_true_iff in H2.
  apply beq_nat_false in H2.
  apply fact_discompose in H2.
  rewrite mult_assoc_reverse. rewrite <- H2. assumption.
- apply hoare_asgn.
- unfold assn_sub, t_update.
  intros st H; subst; simpl; omega.
- unfold bassn; simpl; intros st [H1 H2].
  apply eq_true_negb_classical in H2.
  apply Nat.eqb_eq in H2.
  rewrite H2 in H1. simpl in H1. omega.
Qed.

