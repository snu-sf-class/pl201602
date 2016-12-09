Require Import P06.


Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==> c' / st'.


