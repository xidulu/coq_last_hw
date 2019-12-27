Definition or_comm_aux P Q (H : P \/ Q) : Q \/ P :=
  match H with
  | or_introl H0 => or_intror H0
  | or_intror H0 => or_introl H0
  end.

Definition or_comm : forall P Q , P \/ Q -> Q \/ P :=
fun (P Q : Prop) (PorQ : P \/ Q) =>
match PorQ with
| or_introl P_holds => or_intror P_holds
| or_intror Q_holds => or_introl Q_holds
end.