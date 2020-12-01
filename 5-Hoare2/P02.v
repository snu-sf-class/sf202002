Require Export P01.

Lemma min_correct: forall (a b: nat),
  {{ True }}
  X := a;
  Y := b;
  Z := 0;
  while ~(X = 0) && ~(Y = 0) do
    X := X - 1;
    Y := Y - 1;
    Z := Z + 1
  end
  {{ Z = min a b }}.
Proof.
  exact FILL_IN_HERE.
Qed.

