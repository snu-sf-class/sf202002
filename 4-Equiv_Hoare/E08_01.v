Require Import P08.

Check hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X := a {{ fun st => st X = aeval st a}}.

