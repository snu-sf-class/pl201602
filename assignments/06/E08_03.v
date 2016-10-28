Require Import P08.



Check subseq_app: forall X (l1 l2 l3: list X)
    (SUB: subseq l1 l2),
  subseq l1 (l2++l3).

