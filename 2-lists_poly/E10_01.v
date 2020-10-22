Require Import P10.


Check excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).

