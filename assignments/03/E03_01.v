Require Import P03.



Check nil_app : forall X:Type, forall l:list X,
  app [] l = l.

