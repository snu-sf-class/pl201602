Require Export P03.



(** **** Exercise: 3 stars, advanced (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for [X] = [2]
   (the latter is trickier than you might expect). *)

Definition pup_to_n : com :=
  Y ::= (ANum 0) ;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Y ::= APlus (AId Y) (AId X) ;;
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
unfold pup_to_n.
eapply E_Seq.
- apply E_Ass. simpl. reflexivity.
- apply E_WhileLoop with (st' := t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1).
  simpl. reflexivity.
  eapply E_Seq. eapply E_Ass. simpl. reflexivity. eapply E_Ass. simpl. reflexivity.
  apply E_WhileLoop with (st' := t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
  simpl. reflexivity.
  eapply E_Seq.
  eapply E_Ass. simpl. reflexivity.
  eapply E_Ass. simpl. reflexivity.
  apply E_WhileEnd.
  simpl. eauto.
Qed.

