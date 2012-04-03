
(* 1.25 *)
Require Import Arith.
Require Import List.

Theorem injection_example : forall (a : nat) (xs : list nat), 1::xs = a::xs -> 1 <= a.
Proof.
  intros a xs.
  intro H.
  injection H.
  intro Ha.
  rewrite Ha.
  apply le_refl.
Qed.