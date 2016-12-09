Require Export P08.



(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
   we distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As often happens, this
   apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma lt_S: forall n m,
    S n < S m -> n < m.
Proof.
intros.
induction m.
- inversion H. inversion H1.
- inversion H. auto.
  apply IHm in H1.
  constructor.
  assumption.
Qed.

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
intros.
induction l.
- inversion H.
- inversion H.
  + rewrite H0 in *.
    exists [], l.
    reflexivity.
  + apply IHl in H0.
    inversion H0.
    inversion H1.
    exists (a::x0).
    exists x1.
    simpl.
    rewrite H2.
    reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| rp_base: forall x l, In x l -> repeats (x::l)
| rp_next: forall x l, repeats l -> repeats (x::l)
.

Theorem len_plus: forall (X:Type) (l1:list X) (l2:list X),
    length (l1++l2) = length l1 + length l2.
Proof.
intros.
induction l1.
- reflexivity.
- simpl. rewrite IHl1. auto.
Qed.

Theorem in_case_diff:forall (X:Type) (x:X) (x2:X) (l1 l2:list X),
  In x2 (l1++x::l2) -> x <> x2 -> In x2 (l1++l2).
Proof.
intros.
induction l1.
- simpl. simpl in H. destruct H.
  + apply H0 in H. inversion H.
  + assumption.
- simpl. simpl in H.
  destruct H.
  + auto.
  + right. auto.
Qed.


(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
   { simpl. intros. inversion H1. }
   {
     intros l2.
     intros H_excluded.
     unfold excluded_middle in *.
     intros H1 H2.
     assert (H' := H_excluded (In x l1')).
     destruct H'.
     - apply rp_base. assumption.
     - apply rp_next.
       destruct (in_split X x l2).
       + apply H1.
         constructor. reflexivity.
       + inversion H0.
         apply IHl1' with (l2 := x0++x1).
         * assumption.
         * intros.
           destruct (H_excluded (x = x2)) eqn:Heqxx2.
           ++ rewrite <- e in H4. apply H in H4. inversion H4.
           ++ apply in_case_diff with (x := x).
              rewrite <- H3. apply H1.
              simpl. right. assumption. assumption.
         *  rewrite H3 in H2.
            rewrite len_plus in H2.
            simpl in H2.
            rewrite len_plus.
            rewrite <- plus_n_Sm in H2.
            apply lt_S. assumption.
   }
Qed.

