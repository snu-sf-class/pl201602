Require Export P03.



(** **** Problem : 3 stars (mult_comm) *)

Lemma mult_comm : forall n m: nat,
  n * m = m * n.
Proof.
intros.
induction n.
- rewrite <- mult_n_O. reflexivity.
- simpl. rewrite -> IHn. rewrite <- mult_n_Sm.
rewrite plus_comm. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.  
intros.
rewrite mult_comm.
rewrite mult_comm with (n := n) (m := p).
rewrite mult_comm with (n := m) (m := p).
induction p.
- simpl. reflexivity. 
- simpl. rewrite -> IHp.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  rewrite plus_assoc with (n := m) (m := p * n) (p := p * m).
  rewrite plus_assoc with (n := p * n) (m := m) (p := p * m).
  rewrite plus_comm with (n := m) (m := p * n).
  reflexivity.
Qed.

