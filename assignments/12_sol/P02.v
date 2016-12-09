Require Export P01.


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



Lemma value_never_progress : forall t t',
  t ==> t' -> ~ (value t).
Proof.
  induction t; i; intro C; inv C; inv H.
  all: try (eapply IHt; eauto; fail).
  all: try (eapply IHt1; eauto; fail).
  all: try (eapply IHt2; eauto; fail).
Qed.

Lemma preservation_multi : forall t t' T,
  empty |- t \in T ->
  t ==>*t' ->
  empty |- t' \in T.
Proof.
  i. induction H0; ss.
  apply IHmulti. eapply preservation; eauto.
Qed.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  i. apply progress in H as H'.
  intros [C1 C2]. unfold normal_form in C1.
  des H'.
  - (* value t *)
    inv H0; ss. eapply value_never_progress; eauto.
  - (* exists t', t ==> t' *)
    inv H0; ss.
    hexploit preservation; eauto. i.
    hexploit preservation_multi; eauto. i.
    apply progress in H4. des H4; ss.
Qed.
