Lemma solving_by_reflexivity : 2 + 3 = 5.
Proof. auto. Qed.

Lemma solving_by_apply :
  forall (P Q : nat -> Prop),
    (forall n, Q n -> P n) -> (forall n, Q n) -> P 2.
Proof. auto. Qed.

Lemma solving_conj_goal :
  forall (P : nat -> Prop) (F : Prop),
    (forall n, P n) -> F -> F /\ P 2.
Proof. auto. Qed.

Lemma solving_disj_goal : forall (F F' : Prop), F -> F \/ F'.
Proof. auto. Qed.

Lemma solving_conj_hyp :
  forall (F F' : Prop), F /\ F' -> F.
Proof. intros F F' H. destruct H. auto. Qed.

Lemma solving_disj_hyp :
  forall (F F' : Prop), F \/ F' -> F' \/ F.
Proof. intros F F' H. destruct H; auto. Qed.

Lemma solving_conj_hyp' :
  forall (F F' : Prop), F /\ F' -> F.
Proof. tauto. Qed.

Lemma solving_disj_hyp' :
  forall (F F' : Prop), F \/ F' -> F' \/ F.
Proof. tauto. Qed.

Require Import Arith.

Hint Resolve Le.le_refl.

(* mult_le_compat_1 を arith データベースに追加 *)
Hint Resolve mult_le_compat_l : arith.

(* ex. ...   auto with arith. *)
