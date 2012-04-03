Require Import List.

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
                    xs ++ nil = xs.
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
