Require Export P04.



Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  exact FILL_IN_HERE. Qed.

