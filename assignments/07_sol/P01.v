Require Export D.



(** **** Exercise: 2 stars, optional (t_update_shadow)  *)
(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)


Lemma suppl : forall A (b:bool) (v1 v2:A), (if b then v1 else v2) = 
  (if b then v1 else (if b then v1 else v2)).
Proof.
destruct b.
intros. reflexivity.
intros. reflexivity.
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.

Proof. 
intros.
unfold t_update.
apply functional_extensionality.
intros.
destruct (beq_id x x0).
reflexivity. reflexivity.
Qed.