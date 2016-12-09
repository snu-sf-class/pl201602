Require Export P01.



(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
intros.
eapply hoare_seq.
eapply hoare_seq.
eapply hoare_seq with (Q := (fun st => (st Z = c + st X /\
                                        st Z = c + st X + st Y))).
eapply hoare_seq with (Q := (fun st => (st Z = c + a + st Y))).
- eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_seq.
  apply hoare_asgn.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  + unfold assn_sub, bassn, t_update.
    simpl.
    intros st [H1 H2].
    omega.
  + unfold bassn. simpl.
    intros st [H1 H2].
    apply eq_true_negb_classical in H2.
    apply beq_nat_true_iff in H2.
    omega.
- eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_seq.
  apply hoare_asgn.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  + unfold assn_sub, bassn, t_update.
    simpl.
    intros st [[H1 H2] H3].
    split ; omega.
  + unfold bassn. 
    simpl. 
    intros st [[H1 H2] H3].
    apply eq_true_negb_classical in H3.
    apply beq_nat_true_iff in H3.
    omega.
- apply hoare_asgn.
- apply hoare_asgn.
- eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assn_sub, t_update.
  simpl.
  intros st H1.
  omega.
Qed.

