Require Import PeanoNat Le Lt Plus.
Local Open Scope nat_scope.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
intros n m p Hnm Hmp1.
  unfold lt in Hnm.

  assert (S n <= S p).
  apply le_trans with m.
  assumption.
  assumption.

  apply le_S_n.
  assumption.
Qed.