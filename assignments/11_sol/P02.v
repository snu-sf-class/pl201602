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


(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)

(** **** Exercise: 3 stars (finish_progress)  *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  induction HT...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  - (* T_If *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    + (* t1 can take a step *)
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  - (* T_Succ *)
    des IHHT.
    + left. hexploit nat_canonical; eauto.
    + des H. right. eexists. eauto.
  - (* T_Pred *)
    des IHHT.
    + right. hexploit nat_canonical; eauto. i.
      des t1; inv H0.
      * eexists. eauto.
      * eexists. eauto.
    + des H. right. eexists. eauto.
  - (* T_Iszero *)
    des IHHT.
    + right. hexploit nat_canonical; eauto. i.
      des t1; inv H0.
      * eexists. eauto.
      * eexists. eauto.
    + des H. right. eexists. eauto.
Qed.

