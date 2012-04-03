(* 1.15 1.16 1.17 1.18 1.19 1.20 *)
Theorem first_theorem : forall P: Prop, P -> P.
Proof.
  (* intro P. *)
  (* intro Hp. *)
  intros P Hp.
  apply Hp.
Qed.

Theorem x_le_y_tauto : forall (x y : nat), x < y -> x < y.
Proof.
  intros x y.
  apply first_theorem.
Qed.

(* 問4.1 *)
Theorem p_q_p : forall P Q : Prop, P -> Q -> P.
Proof.
  intros P Q.
  (* intros Hp Hq. *)
  intros Hp _.
  apply Hp.
Qed.

Definition p_q_p' :=
  (fun (P Q : Prop) (Hp : P) (_ : Q) => Hp)
  : forall P Q : Prop, P -> Q -> P.
