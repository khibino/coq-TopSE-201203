Require Import List.
(* Require Import Arith. *)

Definition length_tl :
  forall (A : Type) (xs : list A), {n : nat | n = length xs}.
Proof.
  intros A xs.

  refine (
      let fix iter n ys :=
          match ys with
            | nil      => n
            | _ :: ys' => iter (S n) ys'
          end
      in exist _ (iter 0 xs) _
    ).

  info assert (Hiter: forall ys n, iter n ys = n + iter 0 ys).
  info (induction ys; simpl).

  apply plus_n_O.

  intro n.
  rewrite (IHys (S n)), (IHys 1).
  apply plus_n_Sm.

  induction xs; simpl.
  reflexivity.

  rewrite <- IHxs.
  apply Hiter.
Qed.
