Require Import P14.



Check subst_equiv: forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 (subst_aexp i1 a1 a2) ->
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

