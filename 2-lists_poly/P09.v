Require Export P08.


Lemma In_app_iff : forall A (l:list A) (l':list A) (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  exact FILL_IN_HERE.
Qed.

