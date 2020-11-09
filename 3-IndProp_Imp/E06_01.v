Require Import P06.


Check optimize_1mult_sound: forall a,
  aeval (optimize_1mult a) = aeval a.

