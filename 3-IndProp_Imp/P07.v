Require Export P06.

(* Write a relation [bevalR] in the same style as
   [aevalR], and prove that it is equivalent to [beval]. *)

(* Don't use aeval and beval when define bevalR (only use aevalR). *)

Inductive bevalR: bexp -> bool -> Prop :=
  (* FILL_IN_HERE *)
.

Check aeval_iff_aevalR.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  exact FILL_IN_HERE.
Qed.
