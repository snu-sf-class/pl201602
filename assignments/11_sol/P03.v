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


(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term. *)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(** **** Exercise: 2 stars (finish_preservation)  *)
(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    - (* T_Succ *)
      inv HE. hexploit HT; eauto.
  - (* T_Pred *)
    inv HE; eauto. inv HT. eauto.
  - (* T_Iszero *)
    inv HE; eauto.
Qed.

