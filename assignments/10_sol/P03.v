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


(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  induction t; ss.
  { left. apply v_const. }
  right. des IHt1; cycle 1.
  { des H. eexists. apply ST_Plus1. eauto. }
  inv H. des IHt2; cycle 1.
  { des H. eexists. apply ST_Plus2. eauto. }
  inv H. eexists. apply ST_PlusConstConst.
Qed.

Lemma step_nf_const : forall t,
  step_normal_form t ->
  exists n, t = C n.
Proof.
  i. unfold step_normal_form, normal_form in H.
  induction t; eauto.
  exfalso. apply H.
  hexploit (strong_progress (P t1 t2)); eauto. i.
  des H0; ss. inv H0.
Qed.

(** **** Exercise: 3 stars (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t \\ n.
Proof.
  i. unfold normal_form_of in H. des H.
  apply step_nf_const in H0. des H0.
  eexists. split; eauto.
  induction H; subst.
  - apply E_Const.
  - hexploit IHmulti; eauto. i.
    eapply step__eval; eauto.
Qed.
