Inductive light : Set :=
  | Blue   : light
  | Yellow : light
  | Red    : light.

Definition next x :=
  match x with
    | Blue   => Yellow
    | Yellow => Red
    | Red    => Blue
  end.

Check next Yellow.
Eval compute in next Yellow.