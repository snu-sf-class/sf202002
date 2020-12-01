Require Export P02.

Lemma power_series_correct: forall (m: nat),
  {{ True }}
    X := 0;
    Y := 1;
    Z := 1;
    while ~(X = m) do
      Z := 2 * Z;
      Y := Y + Z;
      X := X + 1
    end
  {{ Y = power_series 2 m }}.
Proof.
  exact FILL_IN_HERE.
Qed.

