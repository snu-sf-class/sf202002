Require Export D.

Lemma factorial_correct: forall (m: nat),
    {{ X = m }}
  Y := 1 ;
  while ~(X = 0)
  do
     Y := Y * X ;
     X := X - 1
  end
    {{ Y = fact m }}.
Proof.
  exact FILL_IN_HERE.
Qed.

