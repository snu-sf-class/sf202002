Require Export P06.



(** Use induction to prove this simple fact about [evenb]: *)
Print evenb.

Lemma evenb_S : forall n, evenb (S n) = negb (evenb n) .
Proof.
  exact FILL_IN_HERE.
Qed.

