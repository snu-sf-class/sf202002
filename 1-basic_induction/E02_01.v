Require Import P02.



Check orb_false_elim2: forall b c : bool,
    orb b c = false -> c = false.

