Require Import P04.



Check andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.

