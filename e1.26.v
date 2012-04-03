Fixpoint fact n :=
  match n with
    | O    => 1
    | S n' => n * fact n'
  end.

(* 1.26 1.27 *)
Theorem fact5 : fact 5 = 120.
Proof.
  simpl.
  reflexivity.
Qed.