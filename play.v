Lemma leibniz_equality : forall(X : Type) (x y: X),
 x = y -> forall P : X -> Prop, P x -> P y.
Proof.
intros. rewrite H in H0. assumption.
Qed.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| all_nil  : all X P nil
| all_cons : forall (x:X) (xs:list X), P x -> all X P xs -> all X P (x::xs)
.

