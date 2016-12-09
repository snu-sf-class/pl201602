Require Export P11.



Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
unfold btrans_sound.
unfold bequiv.
intros.
induction b ; simpl; try reflexivity; (* BTrue, BFalse *)
  try (rewrite optimize_0plus_aexp_sound;
       rewrite optimize_0plus_aexp_sound with (a := a0);
  auto; fail); (* BEq, BLe *)
  try (simpl; rewrite IHb; auto); (* BNot *)
  try (simpl; rewrite IHb1 ; rewrite IHb2 ; auto). (* BAnd *)
Qed.

