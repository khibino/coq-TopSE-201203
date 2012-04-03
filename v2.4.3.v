Ltac intro_rewrite_clear :=
  let H := fresh "H" in
    (* let rw := (fun x => rewrite x) in でも同じ *)
    let rw x := (rewrite x) in
      intro H; rewrite H; clear H.



Lemma dup_lemma : forall P, P -> P -> P.
Proof . auto. Qed.

Ltac dupn n :=
  match n with
    | 0     => idtac
    | S 0   => idtac
    | S ?n' => apply dup_lemma; [|dupn n']
  end.

Ltac my_tauto :=
  repeat match goal with
           | H: ?P |- ?P => apply H
           | |- True => apply I
           | |- _ /\ _ => split
           | |- _ -> _ => intro
           | H: False  |- _  => destruct H
           | H: _ /\ _ |- _ => destruct H
           | H: _ \/ _ |- _ => destruct H
                                        (* P -> Q と P から Qを作る *)
           | H1: ?P -> ?Q, H2: ?P |- _ => specialize (H1 H2)
         end.

Ltac destruct_if :=
  match goal with
    | |- if ?x then _ else _ => case_eq x; intro
                                             (* それ以外は何もしない *)
    | _ => idtac
  end.
