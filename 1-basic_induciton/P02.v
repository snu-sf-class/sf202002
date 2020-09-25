Require Export P01.



(** **** Exercise: 2 stars, standard (orb_false_elim2)  

    Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

Theorem orb_false_elim2 : forall b c : bool,
  orb b c = false -> c = false.
Proof.
  exact FILL_IN_HERE.
Qed.

