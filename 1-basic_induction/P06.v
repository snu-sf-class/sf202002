Require Export P05.



(** Use induction to prove this simple fact about [double]: *)
Print double.

Lemma double_plus : forall n, double n = n + n .
Proof.
  exact FILL_IN_HERE.
Qed.

