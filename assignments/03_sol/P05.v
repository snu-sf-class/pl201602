Require Export P04.



(** **** Problem #2 : 1 star, optional (hd_opt_poly) *)
(** Complete the definition of a polymorphic version of the
    [hd_opt] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
  match l with
  | nil => None
  | h::t => Some h
  end.

(** Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt2 :   hd_opt  [[1];[2]]  = Some [1].
Proof. reflexivity. Qed.

