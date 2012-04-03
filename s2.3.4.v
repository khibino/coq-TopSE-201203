(* Require Import ZArith. *)
(* Open Scope Z_scope. *)
(* ... *)

(* Open Scope nat_scope. *)

Lemma congruence_demo :
  forall (f : nat -> nat -> nat) (g h : nat -> nat) (x y z : nat),
    (forall a, g a = h a) ->
    f (g x) (g y) = z ->
    g x = 2 ->
    f 2 (h y) = z.
Proof. congruence. Qed.

Lemma congruence_demo' :
  forall (f g : nat -> nat),
    (forall a, f a = g a) -> f (g (g 2)) = g (f (f 2)).
Proof. congruence. Qed.

