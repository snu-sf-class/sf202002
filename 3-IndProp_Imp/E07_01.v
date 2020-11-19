Require Import P07.

Local Opaque aeval beval.

Example test_bevalR1: bevalR (BNot BTrue) false.
Proof. do 20 try econstructor; try eapply my_bevalR1. Qed.
Example test_bevalR2: bevalR (BEq (APlus (ANum 2) (ANum 1)) (ANum 3)) true.
Proof. do 20 try econstructor; try eapply my_bevalR2. Qed.
Example test_bevalR3: bevalR (BAnd (BLe (AMult (ANum 3) (ANum 1))
                                        (AMinus (ANum 1) (ANum 3)))
                                   BTrue) false.
Proof. do 20 try econstructor; try eapply my_bevalR3. Qed.
