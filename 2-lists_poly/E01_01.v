Require Import P01.

Example test_remove_all1: remove_all 5 [2;1;5;4;1] = [2;1;4;1].
Proof. reflexivity. Qed.
Example test_remove_all2: remove_all 5 [2;1;4;1] = [2;1;4;1].
Proof. reflexivity. Qed.
Example test_remove_all3: remove_all 1 [2;1;4;5;1;4] = [2;4;5;4].
Proof. reflexivity. Qed.
Example test_remove_all4: remove_all 5 [2;1;5;4;5;1;4;5;1;4] = [2;1;4;1;4;1;4].
Proof. reflexivity. Qed.

