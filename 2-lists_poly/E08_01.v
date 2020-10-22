Require Import P08.


Check contrapositive : forall (P Q : Prop),
    (P -> Q) -> (~Q -> ~P).

