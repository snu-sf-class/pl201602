Require Import P05.



Check loop_never_stops : forall st st',
  ~(loop / st \\ st').

