Require Export P02.


Ltac inv X := inversion X; subst; clear X.
Ltac des X := destruct X.
Ltac i := intros.
Ltac ii := repeat intro.
Ltac ss := simpl in *; auto.

Lemma mp: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Lemma mp': forall P Q : Type, (P -> Q) -> P -> Q.
Proof. intuition. Qed.

Ltac hexploit x := eapply mp; [eapply x|].
Ltac hexploit' x := let H := fresh in set (H := x); clear H; eapply mp; [eapply x|].


(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Definition halve : tm :=
  tfix
    (tabs Halve (TArrow TNat TNat)
          (tabs X TNat
                (tif0
                   (tvar X)
                   (tnat 0)
                   (tif0
                      (tpred (tvar X))
                      (tnat 0)
                      (tsucc
                         (tapp (tvar Halve) (tpred (tpred (tvar X))))))))).

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  unfold halve; eauto 10.
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  unfold halve; normalize.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  unfold halve; normalize.
Qed.

Lemma tsucc_multi : forall t t',
  t ==>* t' -> tsucc t ==>* tsucc t'.
Proof.
  i. induction H; ss.
  eapply multi_step; eauto.
Qed.

Lemma tsucc_nat_multi : forall t n,
  t ==>* tnat n -> tsucc t ==>* tnat (S n).
Proof.
  i. eapply multi_trans.
  - apply tsucc_multi. eauto.
  - eauto.
Qed.

Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
  induction n; unfold halve; ss.
  { normalize. }
  rewrite <- plus_n_Sm.
  Ltac multi := eapply multi_step.
  multi.
  { apply ST_AppFix; eauto. }
  multi.
  { apply ST_App1.
    apply ST_AppAbs; eauto.
  }
  multi.
  { apply ST_AppAbs. eauto. }
  multi; [ss; eauto|].
  multi; [ss; eauto|].
  multi; [ss; eauto|].
  multi; [ss; eauto|].
  multi; [ss; eauto|].
  apply tsucc_nat_multi. auto.
Qed.
