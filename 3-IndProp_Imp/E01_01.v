Require Import P01.

Check ev_sum_not : forall n m, ev n -> ~ ev m -> ~ ev (n + m).

