Require Export P02.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{c1 ; c2}> <{c1' ; c2'}>.
Proof.
  exact FILL_IN_HERE.
Qed.
