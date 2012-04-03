Require Import List.

(* length *)
Check (length (1::2::nil)).

Theorem zero_length_nil : forall {A : Set} (xs : list A),
                            length xs = 0 -> xs = nil.
  intros A xs.

  induction xs.
  simpl.
  reflexivity.

  simpl.
  discriminate.
Qed.
