Require Export P06.

(* Write a relation [bevalR] in the same style as
   [aevalR], and prove that it is equivalent to [beval]. *)

(* Don't use aeval and beval when define bevalR (only use aevalR). *)

Inductive bevalR: bexp -> bool -> Prop :=
  (* FILL_IN_HERE *)
.

(** If your definition can't proof these examples using "do 20 try econstructor", **)
(** comment out and write your proofs in following area. **)

(*
Example my_bevalR1: bevalR (BNot BTrue) false.
Proof. do 20 try econstructor. Qed.
Example my_bevalR2: bevalR (BEq (APlus (ANum 2) (ANum 1)) (ANum 3)) true.
Proof. do 20 try econstructor. Qed.
Example my_bevalR3: bevalR (BAnd (BLe (AMult (ANum 3) (ANum 1))
                                        (AMinus (ANum 1) (ANum 3)))
                                   BTrue) false.
Proof. do 20 try econstructor. Qed.
*)


Check aeval_iff_aevalR.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  exact FILL_IN_HERE.
Qed.
