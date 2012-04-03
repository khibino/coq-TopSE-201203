(* 1.9 *)
Inductive list (A : Set) : Set :=
  | Nil  : list A
  | Cons : A -> list A -> list A.

Definition myNil   := Nil nat.
Definition myListE := Cons nat 1 (Cons nat 3 (Nil nat)).

Check myNil.
Print myNil.

Check myListE.
Print myListE.

(* 1.10 *)
Implicit Arguments Nil  [A].
Implicit Arguments Cons [A].

(* 1.11 *)
Infix "::" := Cons (at level 60, right associativity).

Check (1::Nil).

(* Check Nil. *)
Check (@Nil bool).

(* Definition myNil2   := Nil. *)
Definition myListE2 := 1 :: 3 :: Nil.

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

(* 練習問題 *)
(* 問 3.1 *)
Fixpoint rev {A : Set} (xs : list A) :=
  match xs with
    | Nil      => Nil
    | x :: xs' => rev xs' ++ x :: Nil
  end.

Definition myListRev := rev (myListE ++ myListE).
Eval compute in myListRev.
Definition myListRev2 := @rev nat (myListE ++ myListE ++ myListE).
Eval compute in myListRev2.

(* 問 3.2 *)
Fixpoint sum (xs : list nat) :=
  match xs with
    | Nil      => 0
    | x :: xs' => x + sum xs'
  end.

(* 1.5.1 *)
Theorem zero_length_nil : forall {A : Set} (xs : list A),
                            length xs = 0 -> xs = Nil.
  intros A xs.

  destruct xs.
  simpl.
  reflexivity.

  simpl.
  discriminate.
Qed.


(* 1.28 *)
Theorem app_length : forall {A : Set} (xs ys : list A),
                       length (xs ++ ys) = length xs + length ys.
Proof.
  intros A xs ys.
  induction xs.
  simpl.
  reflexivity.

  simpl.
  rewrite IHxs.
  reflexivity.
Qed.

(* 練習問題 *)
(* 問4.2 *)
Theorem app_assoc : forall {A:Set} (xs ys zs : list A),
                      xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
  intros A xs ys zs.
  induction xs.
  simpl.
  reflexivity.

  simpl.
  rewrite IHxs.
  reflexivity.
Qed.

(* 問4.3 *)
Theorem app_nil : forall {A:Set} (xs: list A),
                    xs ++ Nil = xs.
Proof.
  intros A xs.
  induction xs.
  simpl.
  reflexivity.

  simpl.
  rewrite IHxs.
  reflexivity.
Qed.

(* IH  Inductive Hypothesis *)


(* 問4.4 *)
Theorem app_rev : forall {A:Set} (xs ys: list A),
                    rev (xs ++ ys) = rev ys ++ rev xs.
Proof.
  intros A xs ys.
  induction xs.

  simpl.
  rewrite app_nil.
  reflexivity.

  simpl.
  rewrite IHxs.
  rewrite <- app_assoc.
  reflexivity.
Qed.


(* 問4.5 *)
Theorem rev_rev : forall {A:Set} (xs: list A),
                    rev (rev xs) = xs.
Proof.
  intros A xs.
  induction xs.

  simpl.
  reflexivity.

  simpl.
  rewrite app_rev.
  simpl.
  rewrite IHxs.
  reflexivity.
Qed.


Require Import Arith.

(* おまけ *)
Theorem rev_length : forall {A:Set} (xs: list A),
                       length (rev xs) = length xs.
Proof.
  intros A xs.
  induction xs.

  simpl.
  reflexivity.

  simpl.
  rewrite app_length.
  simpl.
  rewrite IHxs.
  rewrite plus_comm.
  reflexivity.
Qed.

Require Import Recdef.

(* length 関数でわかる長さについて measure *)

Function foo (xs : list nat) {measure length xs} : list nat :=
  match xs with
    | Nil => Nil
    | x :: xs' => x :: foo (rev xs')
  end.
Proof.
  intros xs x xs'.
  intro Hcons.

  simpl.
  rewrite rev_length.
  apply lt_n_Sn.
Qed.
