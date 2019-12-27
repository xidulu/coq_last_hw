Inductive even : nat -> Prop :=
    | ev_0 : even 0
    | ev_SS : forall n, even n -> even (S (S n)).

Theorem ev_8 : even 8.
Proof.
apply ev_SS.
apply ev_SS.
apply ev_SS.
apply ev_SS.
apply ev_0.
Qed.