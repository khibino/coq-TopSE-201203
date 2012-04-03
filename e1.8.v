Fixpoint fact n :=
  match n with
    | O    => 1
    | S n' => n * fact n'
  end.

Definition v := fact 5.
Eval compute in v.