Require Import P02.



Check app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.

