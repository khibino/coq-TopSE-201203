Require Import ZArith.
Open Scope Z_scope.

Lemma ring_demo : forall (x y z : Z),
                    x * (y + z) - z * 3 * x = x * y - 2 * x * z.
Proof.
  intros. ring.
Qed.

