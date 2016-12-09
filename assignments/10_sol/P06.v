Require Export P05.


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

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==> c' / st'.
Proof.
  Hint Constructors cstep.
  induction c; eauto; right.
  - des (aexp_strong_progress st a); des H; subst; eauto.
  - hexploit IHc1; eauto. i. des H; subst; eauto.
    des H. des H. eauto.
  - des (bexp_strong_progress st b); des H; subst; eauto.
  - hexploit IHc1; eauto. i.
    hexploit IHc2; eauto. i.
    des H; des H0; subst; eauto.
    all: try (des H; des H; eauto; fail).
    all: try (des e; des H; eauto; fail).
Qed.

