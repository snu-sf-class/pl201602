Require Export P14.



(** **** Exercise: 3 stars, optional (inequiv_exercise)  *)
(** Prove that an infinite loop is not equivalent to [SKIP] *)

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof. exact FILL_IN_HERE. Qed.

