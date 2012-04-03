(* lt_dec : forall n m : nat, {n < m} + {~ n < m} *)
Require Import Arith.



(* Lemma even_odd_dec : forall n, n -> {even n} + {odd n}. *)

Definition max m n :=
  if lt_dec m n then n else m.

(*
 unfold は値の定義を展開
 destruct は型の定義を展開
 *)

Theorem max_lv : forall m n, m <= max m n.
Proof.
  intros m n.
  unfold max.
  destruct (lt_dec m n) as [ l | _ ].
  (* destruct lt_dec. *)

  apply lt_le_weak.
  apply l.

  apply le_refl.
Qed.

(* < の bool 版 *)
Fixpoint lt_bool m n :=
  match m, n with
    | _, 0   => false
    | 0, S _ => true
    | S m', S n' => lt_bool m' n'
  end.

(* lt_bool と < が同値であることを証明 *)
Lemma lt_bool_spec : forall m n, m < n <-> lt_bool m n = true.
Proof.
  induction m; destruct n.

  (* case: 0, 0 *)
  split.
  intro H. inversion H.
  discriminate.

  (* case: 0, S _ *)
  split.
  reflexivity.

  intros _. apply lt_0_Sn.

  (* case: S _, 0 *)
  split.
  intro H. inversion H.

  discriminate.

  (* case: S _, S _ *)
  split.
  simpl. intro H. apply lt_S_n in H. apply IHm. apply H.

  simpl. intro H. apply IHm in H. apply lt_n_S. apply H.
Qed.

Definition max' m n := if lt_bool m n then n else m.

Theorem max'_le : forall m n, m <= max' m n.
Proof.
  intros m n; unfold max'.
  case_eq (lt_bool m n); auto.
  intro H.
  apply lt_bool_spec in H.
  apply lt_le_weak.
  apply H.
Qed.
