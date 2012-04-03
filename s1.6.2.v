Require Import ZArith.

Open Scope Z_scope.

Definition money := Z.

Record state := {
               receivable : money;
               billing    : money;
               received   : money;
               earnings   : money
             }.

Definition balance (s : state) : Prop :=
  match s with
    | {| billing := b; receivable := r1; received := r2; earnings := e |}
      =>  b = (r1 + r2 - e)
  end.


Definition receive (x : money) (s : state) : state :=
  {| receivable := receivable s - x;
     billing    := billing s;
     received   := received s + x;
     earnings   := earnings s
  |}.

  (* match s with *)
  (*     | {| billing := b; receivable := r1; received := r2; earnings := e |} *)

Definition receive_invariant :
  forall n s, balance s -> balance (receive n s).
Proof.
  intros n s.

  simpl.
  rewrite Zplus_assoc.
  rewrite Zplus_comm.
  rewrite Zplus_assoc.
  rewrite Zplus_minus.
  destruct s.
  (* simpl. *)
  intro H.
  apply H.
Qed.

(* rewrite Zplus_comm. *)
(* rewrite Zplus_assoc. *)

(* rewrite Zminus_plus_distr *)
(* rewrite Zminus_plus_simpl_r *)

Definition sell (x : money) (s : state) : state :=
  {| receivable := receivable s;
     billing    := billing s - x;
     received   := received s;
     earnings   := earnings s + x
  |}.

Theorem sell_invariant :
  forall n s, balance s -> balance (sell n s).
Proof.
  intros n s.

  simpl.
  rewrite Zminus_plus_distr.
