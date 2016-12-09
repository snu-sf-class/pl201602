Require Export P04.


Lemma IFB_split: forall P Q b c1 c2,
    {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} ->
    {{fun st => P st /\ (beval st b = true)}} c1 {{Q}} /\
    {{fun st => P st /\ (beval st b = false)}} c2 {{Q}}.
Proof.
intros.
split.
- unfold hoare_triple.
  intros st st' HC [HP HB].
  unfold hoare_triple in H.
  apply H with (st := st) (st' := st'); try assumption.
  apply E_IfTrue; assumption.
- intros st st' HC [HP HB].
  eauto.
  unfold hoare_triple in H.
  apply H with (st := st) (st' := st'); try assumption.
  apply E_IfFalse; assumption.
Qed.

Theorem hoare_if_weakest : forall P1 P2 Q b c1 c2, 
  is_wp P1 c1 Q ->
  is_wp P2 c2 Q ->
  is_wp (fun st => (beval st b = true -> P1 st) /\ (beval st b = false -> P2 st)) 
        (IFB b THEN c1 ELSE c2 FI) Q.
Proof.
unfold is_wp.
unfold assert_implies.
intros P1 P2 Q b c1 c2 [H1 W1] [H2 W2].
split.
- unfold hoare_triple.
  intros st st' H [C1 C2].
  inversion H.
  + subst.
    apply C1 in H7.
    apply (H1 st st') in H8; assumption.
  + apply (H2 st st') in H8; auto.
- intros P' P'H st H.
  apply IFB_split in P'H as [PH1 PH2].
  split.
  + intros.
    apply (W1 (fun st => P' st /\ beval st b = true) PH1).
    eauto.
  + intros.
    apply (W2 (fun st => P' st /\ beval st b = false) PH2).
    eauto.
Qed.

