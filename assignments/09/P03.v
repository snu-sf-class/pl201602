Require Export P02.



(** ** Exercise: Power Series *)

(** **** Exercise: 4 stars, optional (dpow2_down)  *)
(** Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

  X ::= 0;;
  Y ::= 1;;
  Z ::= 1;;
  WHILE X <> m DO
    Z ::= 2 * Z;;
    Y ::= Y + Z;;
    X ::= X + 1
  END

    Write a decorated program for this. *)

Theorem dopw2_down_correct: forall m,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 1;;
  Z ::= ANum 1;;
  WHILE BNot (BEq (AId X) (ANum m)) DO
    Z ::= AMult (ANum 2) (AId Z);;
    Y ::= APlus (AId Y) (AId Z);;
    X ::= APlus (AId X) (ANum 1)
  END
  {{ fun st => st Y = pow 2 (S m) - 1 }}.
Proof. exact FILL_IN_HERE. Qed.

