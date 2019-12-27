Require Import PeanoNat Le Lt Plus.
Local Open Scope nat_scope.

Local Open Scope nat_scope.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
    intros.
    apply Nat.succ_le_mono. apply H.
Qed.
    
  