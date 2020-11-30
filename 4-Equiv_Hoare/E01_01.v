Require Import P01.

Check loop_never_stops : forall st st',
    ~(st =[ loop ]=> st').

