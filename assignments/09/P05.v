Require Export P04.



Theorem hoare_if_weakest : forall P1 P2 Q b c1 c2, 
  is_wp P1 c1 Q ->
  is_wp P2 c2 Q ->
  is_wp (fun st => (beval st b = true -> P1 st) /\ (beval st b = false -> P2 st)) 
        (IFB b THEN c1 ELSE c2 FI) Q.
Proof.
  exact FILL_IN_HERE.
Qed.

