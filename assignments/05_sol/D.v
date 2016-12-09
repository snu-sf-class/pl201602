(** **** SNU 4190.310, 2016 Spring *)

(** Assignment 05 *)
(** Due: 2016/10/31 23:59 *)

(* Important: 
   - Do NOT import other files.

   - You are NOT allowed to use the [admit] tactic.

   - You are NOT allowed to use the following tactics.
     [tauto], [intuition], [firstorder], [omega].

   - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.
*)

Require Import Tactics.
Require Import List.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) :=
  match l with
    | []  => []
    | h :: t => (f h) :: (map f t)
  end.
