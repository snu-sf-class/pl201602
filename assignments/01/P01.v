Require Export D.

(** **** Problem #1: 1 star (factorial) *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. 

    Note that plus and multiplication are already defined in Coq.
    use "+" for plus and "*" for multiplication.
*)

Eval compute in 3 * 5.
Eval compute in 3+5*6.

Fixpoint factorial (n:nat) : nat := 
  FILL_IN_HERE.

Example test_factorial1:          (factorial 3) = 6.
Proof. exact FILL_IN_HERE. Qed.
Example test_factorial2:          (factorial 5) = 10 * 12.
Proof. exact FILL_IN_HERE. Qed.
