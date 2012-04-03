(* 問1 *)
Theorem ex1 : forall x, x = 1 -> x + 1 = 2.
Proof.
  intros x H.
  rewrite H.
  reflexivity.
Qed.


(* 問2 *)
(* 1.9 *)
Inductive list (A : Set) : Set :=
  | Nil  : list A
  | Cons : A -> list A -> list A.

(* 1.10 *)
Implicit Arguments Nil  [A].
Implicit Arguments Cons [A].

(* 1.11 *)
Infix "::" := Cons (at level 60, right associativity).

(* 1.12 *)
Fixpoint length {A : Set} (xs : list A) :=
  match xs with
    | Nil      => 0
    | x :: xs' => 1 + length xs'
  end.

(* 1.13 *)
Fixpoint app {A : Set} (xs ys : list A) :=
  match xs with
    | Nil      => ys
    | x :: xs' => x :: app xs' ys
  end.

(* 1.14 *)
Infix "++" := app (at level 60, right associativity).

Fixpoint map_succ (xs : list nat) : list nat :=
  match xs with
    | Nil      => Nil
    | x :: xs' => (x + 1) :: map_succ xs'
  end.

(* 問3 *)
Theorem map_succ_length : forall (xs : list nat),
                            length (map_succ xs) = length xs.
Proof.
  intros xs.
  induction xs.

  reflexivity.

  simpl.
  rewrite IHxs.
  reflexivity.
Qed.

(* おまけ *)
(* map_succ して map_pred で戻る *)

Fixpoint map_pred (xs : list nat) : list nat :=
  match xs with
    | Nil      => Nil
    | x :: xs' => (x - 1) :: map_pred xs'
  end.

Require Import Arith.

Theorem map_succ_pred : forall (xs : list nat),
                          map_pred (map_succ xs) = xs.
Proof.
  intros xs.
  induction xs.

  simpl.
  reflexivity.

  unfold map_succ.
  unfold map_pred.
  rewrite plus_comm.
  rewrite minus_plus.
  fold map_pred.
  fold map_succ.
  rewrite IHxs.
  reflexivity.
Qed.
