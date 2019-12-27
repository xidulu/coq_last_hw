Definition relation (X:Type) := X -> X -> Prop.

Definition transitive {X:Type} (R:relation X) :=
  forall a b c : X, R a b -> R b c -> R a c.


Theorem le_transitive: transitive le.
  Proof.
    unfold transitive. intros. induction H0.
    - apply H.
    - apply le_S. apply IHle.
  Qed.


Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    - apply le_S. apply Hnm. 
    - apply le_S. apply IHHm'o.
Qed.