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



(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof.
  i. revert T' TYPED'. induction TYPED; i; inv TYPED'; ss.
  - rewrite H in H2. inv H2. ss.
  - f_equal. eauto.
  - hexploit IHTYPED1; eauto. i. inv H.
    hexploit IHTYPED2; eauto.
  - f_equal; eauto.
  - hexploit IHTYPED; eauto. i. inv H. ss.
  - hexploit IHTYPED; eauto. i. inv H. ss.
  - hexploit IHTYPED1; eauto. i. subst.
    hexploit IHTYPED2; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - hexploit IHTYPED1; eauto. i. inv H.
    hexploit IHTYPED2; eauto.
  - hexploit IHTYPED; eauto. i. inv H. ss.
Qed.

