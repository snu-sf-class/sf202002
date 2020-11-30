Require Import P10.

Check if_minus_plus :
  {{fun st => True}}
  if (BLe (AId X) (AId Y))
    then (Z := AMinus (AId Y) (AId X))
    else (Y := APlus (AId X) (AId Z))
  end
  {{fun st => st Y = st X + st Z}}. 

