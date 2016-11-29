(** **** SNU 4190.310, 2016 Spring *)

(** Assignment 08 *)
(** Due: 2016/12/07 23:59 *)

(* Important: 
   - Do NOT import other files.

   - You are NOT allowed to use the [admit] tactic.

   - You are ALLOWED to use any tactics including:
     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.
*)

Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Maps.
Require Export Imp.
Require Export Hoare.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Theorem hoare_if_wp : forall P1 P2 Q b c1 c2,
  {{P1}} c1 {{Q}} ->
  {{P2}} c2 {{Q}} ->
  {{fun st => (beval st b = true -> P1 st) /\ (beval st b = false -> P2 st) }} 
    (IFB b THEN c1 ELSE c2 FI) 
  {{Q}}.
Proof.
  intros Q1 Q2 Q b c1 c2 HTrue HFalse st st' HE [HQ1 HQ2].
  inversion HE; subst; eauto. 
Qed.

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Fixpoint pow (b n: nat) : nat :=
  match n with
  | 0 => 1
  | S n' => b * pow b n'
  end.

