Require Import P03.



Check dopw2_down_correct: forall m,
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

