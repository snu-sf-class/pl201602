Require Export P04.

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


(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  Hint Constructors aval.
  Hint Constructors bstep.
  induction b; eauto; right.
  all: try des (aexp_strong_progress st a); try des H; eauto; subst.
  all: try des (aexp_strong_progress st a0); try des H; eauto; subst.
  all: try (eexists; eauto; fail).
  - des IHb; des H; subst; eauto.
  - des IHb1; des H; des IHb2; des H0; subst; eauto.
Qed.

