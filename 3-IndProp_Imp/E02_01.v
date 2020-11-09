Require Import P02.



Check ev_ev__ev : forall n m,
  ev (n+m) -> ev m -> ev n.

