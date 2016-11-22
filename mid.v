(** **** SNU 4190.310, 2016 Spring *)

(** Mid Exam *)
(** 2016/04/16 18:00 *)

(** Important: 

    - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.

    - You are NOT allowed to use the following tactics.

      [tauto], [intuition], [firstorder], [omega].

    - Here is the list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [apply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [auto]
      [repeat]
      [try]
      [;]
**)

Require Import Arith NPeano.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Fixpoint repeat_ntimes (n: nat) {X:Type} (f:X->X) (x:X) : X :=
  match n with
  | 0 => x
  | S n' => f (repeat_ntimes n' f x)
  end.

Definition c_nat := forall X : Type, (X -> X) -> X -> X.

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"?  The answer is actually simple: just return the
    argument untouched. *)

Definition c_zero : c_nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it.  Thus: *)

Definition c_one : c_nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Similarly, [two] should apply [f] twice to its argument: *)

Definition c_two : c_nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)

Definition c_three : c_nat := @repeat_ntimes 3. 

Definition c_n (n: nat) : c_nat := @repeat_ntimes n.

(** Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)

(**
  Definition of [list] 
 **)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app X t l2)
  end.

Arguments app {X} l1 l2.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Check (3 :: ([0; 1] ++ [])).

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Fixpoint insert (n: nat) l :=
  match l with
  | nil => [n]
  | h::t => if leb n h then n::l else h::insert n t
  end.

Fixpoint sort l :=
  match l with
  | nil => nil
  | h::t => insert h (sort t)
  end.

Fixpoint choose n k :=
  match n with
  | 0 => 1
  | S n' => 
    match k with
    | 0 => 1
    | S k' => if ltb k' n' then choose n' k + choose n' k' else 1
    end
  end.

Fixpoint fact n :=
  match n with
  | 0 => 1
  | S n' => n * fact n'
  end.

(**
  You may need the following lemmas.
 **)

Check Nat.add_comm.
Check Nat.add_assoc.
Check Nat.add_sub.
Check Nat.add_0_l.
Check Nat.add_0_r.
Check Nat.add_succ_l.
Check Nat.add_succ_r.

Check Nat.sub_0_l.
Check Nat.sub_0_r.
Check Nat.sub_diag.
Check Nat.sub_succ_l.
Check Nat.sub_succ_r.

Check Nat.mul_comm.
Check Nat.mul_assoc.
Check Nat.mul_1_l.
Check Nat.mul_1_r.
Check Nat.mul_add_distr_l.
Check Nat.mul_add_distr_r.
Check Nat.mul_sub_distr_l.
Check Nat.mul_sub_distr_r.
Check Nat.mul_cancel_l.

Check Nat.succ_le_mono.
Check Nat.lt_0_succ.
Check Nat.lt_le_trans.
Check Nat.lt_irrefl.
Check Nat.le_trans.
Check Nat.le_max_l.
Check Nat.le_max_r.
Check Nat.max_spec.

(*=========== 3141592 ===========*)

(** Easy: [Homework Assignment] *)
(** Use the tactics you have learned so far to prove the following 
    theorem about boolean functions. *)

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

(*=========== 3141592 ===========*)

(** Easy: [Homework Assignment]

   (* See the definition of [double] *)

   (** Use induction to prove this simple fact about [double]: *)
**)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check double_plus : forall n, double n = n + n .

(*=========== 3141592 ===========*)

(** Medium: [Homework Assignment]
 *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.

(*=========== 3141592 ===========*)

(** Medium: [Homework Assignment]

    Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity].
**)

(** Successor of a natural number: *)

Definition c_succ (n : c_nat) : c_nat :=
  FILL_IN_HERE.

(** Addition of two natural numbers: *)

Definition c_plus (n m : c_nat) : c_nat :=
  FILL_IN_HERE.

Example c_succ_1 : c_succ c_zero = c_one.
Proof. exact FILL_IN_HERE. Qed.

Example c_succ_2 : c_succ c_one = c_two.
Proof. exact FILL_IN_HERE. Qed.

Example c_succ_3 : c_succ c_two = c_three.
Proof. exact FILL_IN_HERE. Qed.

Example c_plus_1 : c_plus c_zero c_one = c_one.
Proof. exact FILL_IN_HERE. Qed.

Example c_plus_2 : c_plus c_two c_three = c_plus c_three c_two.
Proof. exact FILL_IN_HERE. Qed.

Example c_plus_3 :
  c_plus (c_plus c_two c_two) c_three = c_plus c_one (c_plus c_three c_three).
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check c_succ_1 : c_succ c_zero = c_one.

Check c_succ_2 : c_succ c_one = c_two.

Check c_succ_3 : c_succ c_two = c_three.

Check c_plus_1 : c_plus c_zero c_one = c_one.

Check c_plus_2 : c_plus c_two c_three = c_plus c_three c_two.

Check c_plus_3 :
  c_plus (c_plus c_two c_two) c_three = c_plus c_one (c_plus c_three c_three).

(*=========== 3141592 ===========*)

(** Hard: [Homework Assignment]
    Prove the following theorem.
 **)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.

(*=========== 3141592 ===========*)

(** Easy:
    Define a function [square_sum] satisfying:

      square_sum n = 1^2 + 2^2 + ... +n^2

 **)

Fixpoint square_sum (n: nat) : nat :=
  FILL_IN_HERE.

Example square_sum_example1: square_sum 5 = 55.
Proof. exact FILL_IN_HERE. Qed.

Example square_sum_example2: square_sum 10 = 385.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check square_sum_example1: square_sum 5 = 55.

Check square_sum_example2: square_sum 10 = 385.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Lemma app_tail_cancel: forall X (l1 l2: list X) a
    (EQ: l1 ++ [a] = l2 ++ [a]),
  l1 = l2.
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check app_tail_cancel: forall X (l1 l2: list X) a
    (EQ: l1 ++ [a] = l2 ++ [a]),
  l1 = l2.

(*=========== 3141592 ===========*)

Inductive sorted: list nat -> Prop :=
(* FILL_IN_HERE *)
.

Example sorted_example1: sorted [1; 3; 4; 4; 5].
Proof. exact FILL_IN_HERE. (* repeat (constructor; auto). *) Qed.

Example sorted_example2: sorted [2; 2; 3; 6].
Proof. exact FILL_IN_HERE. (* repeat (constructor; auto). *) Qed.

Example sorted_non_example1: sorted [1; 3; 2] -> False.
Proof. exact FILL_IN_HERE.
  (*
  intros. 
  repeat match goal with 
   | [H: sorted _ |- _]  => inversion_clear H; subst 
   | [H: _ <= _ |- _] => inversion_clear H; subst 
  end.
  *)
Qed.

(*
Fixpoint insert (n: nat) l :=
  match l with
  | nil => [n]
  | h::t => if leb n h then n::l else h::insert n t
  end.

Fixpoint sort l :=
  match l with
  | nil => nil
  | h::t => insert h (sort t)
  end.
*)

(* Hint: 

  Fixpoint leb (n m : nat) {struct n} : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leb n' m'
            end
  end

  Use [Search About leb] 
*)

Lemma sort_sorted: forall l, sorted (sort l).
Proof.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)

Check sorted_example1: sorted [1; 3; 4; 4; 5].

Check sorted_example2: sorted [2; 2; 3; 6].

Check sorted_non_example1: sorted [1; 3; 2] -> False.

(*-- Check --*)

Check sort_sorted: forall l, sorted (sort l).

(*=========== 3141592 ===========*)

(** Very hard:
    Prove the following theorem.
 **)

(*
Fixpoint fact n :=
  match n with
  | 0 => 1
  | S n' => n * fact n'
  end.
*)

(* Hint: 

   Using the function [choose] will be very useful.

   Fixpoint choose n k :=
     match n with
     | 0 => 1
     | S n' => 
       match k with
       | 0 => 1
       | S k' => if ltb k' n' then choose n' k + choose n' k' else 1
       end
     end.

   Definition ltb n m := leb (S n) m.

   Use [Search About leb] and [SearchAbout ltb] 

*)

Lemma fact_decompose : forall n k
    (LE: k <= n),
  exists m, fact n = m * fact k * fact (n-k).
Proof. exact FILL_IN_HERE. Qed.

(*-- Check --*)

Check fact_decompose : forall n k
    (LE: k <= n),
  exists m, fact n = m * fact k * fact (n-k).
