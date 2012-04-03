type nat =
| O
| S of nat

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
  | O -> m
  | S p -> S (plus p m)

(** val mult : nat -> nat -> nat **)

let rec mult n m =
  match n with
  | O -> O
  | S p -> plus m (mult p m)

(** val foo : nat -> nat -> nat **)

let foo x y =
  plus (mult x x) y

