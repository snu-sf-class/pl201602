Require Export D.


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


(** **** Exercise: 3 stars (eval__multistep)  *)
(** The key idea behind the proof comes from the following picture:
       P t1 t2 ==>            (by ST_Plus1) 
       P t1' t2 ==>           (by ST_Plus1)  
       P t1'' t2 ==>          (by ST_Plus1) 
       ...                
       P (C n1) t2 ==>        (by ST_Plus2)
       P (C n1) t2' ==>       (by ST_Plus2)
       P (C n1) t2'' ==>      (by ST_Plus2)
       ...                
       P (C n1) (C n2) ==>    (by ST_PlusConstConst)
       C (n1 + n2)              
    That is, the multistep reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_Plus1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_Plus2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PlusConstConst] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

(** To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of [==>*]: that it is reflexive, transitive, and
    includes [==>]. *)

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  i. revert H0. induction H; ss. i. econstructor; eauto.
Qed.

Lemma multi_plus1 : forall t1 t2 n1,
  t1 ==>* C n1 ->
  P t1 t2 ==>* P (C n1) t2.
Proof.
  i. induction H.
  - apply multi_refl.
  - eapply multi_step; eauto.
    apply ST_Plus1. eauto.
Qed.

Lemma multi_plus2 : forall t2 n1 n2,
  t2 ==>* C n2 ->
  P (C n1) t2 ==>* P (C n1) (C n2).
Proof.
  i. induction H.
  - apply multi_refl.
  - eapply multi_step; eauto.
    apply ST_Plus2. eauto.
Qed.

Theorem eval__multistep : forall t n,
  t \\ n -> t ==>* C n.
Proof.
  i. induction H.
  - apply multi_refl.
  - eapply multi_trans; [|eapply multi_trans].
    + apply multi_plus1. apply IHeval1.
    + apply multi_plus2. eauto.
    + eapply multi_step; [|apply multi_refl].
      apply ST_PlusConstConst.
Qed.
