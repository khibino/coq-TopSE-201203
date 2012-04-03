Require Import Omega.

Lemma omega_demo : forall (x y z : nat),
                     (x + y = z + z) -> (x - y <= 4) -> (x - z <= 2).
Proof. intros. omega. Qed.

Lemma omega_demo' : forall (x y : nat),
                      (x + 5 <= y) -> (y - x < 3) -> False.
Proof. intros. omega. Qed.
