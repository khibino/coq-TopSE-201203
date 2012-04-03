Inductive light : Set :=
  | Blue   : light
  | Yellow : light
  | Red    : light.

Definition next x :=
  match x with
    | Blue   => Yellow
    | Yellow => Red
    | Red    => Blue
  end.

Check next Yellow.
Eval compute in next Yellow.

Theorem light_cycles : forall (l : light), next (next (next l)) = l.
Proof.
  intros l.
  destruct l.
  (* Blue *)
  simpl.
  reflexivity.

  (* Yellow *)
  simpl.
  reflexivity.

  (* Red *)
  simpl.
  reflexivity.
Qed.
