Require Import List.
Require Import Recdef.

(* length 関数でわかる長さについて measure *)

Function foo (xs : list nat) {measure length xs} : list nat :=
  match xs with
    | nil => nil
    | x :: xs' => x :: foo (rev xs')
  end.
