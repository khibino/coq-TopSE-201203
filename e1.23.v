
(* Require Import Omega. *)

(* 1.23 1.24 *)
Theorem eq2 : forall x a b, (x = a + b) -> (x + 5 = a + b + 5).
Proof.
  intros x a b.
  (* omega. *)
  intro H.
  (* rewrite H. *)
  rewrite <- H.
  reflexivity.
Qed.
