
Fixpoint length {A:Set} (xs : list A) :=
  match xs with
    | Nil => 0
    | x :: xs' => 1 + length xs'
  end.
