Require Import List.

Fixpoint foo (xs : list nat) : list nat :=
  match xs with
    | nil => nil
    | x :: xs' => x :: foo (rev xs')
  end.

(* Error: Only structural decreasing is supported for a non-Program Fixpoint *)
