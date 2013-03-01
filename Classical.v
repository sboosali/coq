

Inductive and (P Q : Prop) : Prop  :=
 | conj : P -> Q -> and P Q
.

Notation "P /\ Q" := (and P Q) : type_scope.


Inductive or (P Q : Prop) : Prop  :=
 | orl : P -> or P Q
 | orr : Q -> or P Q
.

Notation "P \/ Q" := (or P Q) : type_scope.



Inductive False : Prop := .
(* nothing can prove False .  False is a inductive/type/proposition with no constructor/value/proof *)

Inductive True : Prop := truth : True.

Theorem Truth : True.
Proof. apply truth. Qed.
(*
apply :proof
true witnesses True
true proves proposition True
true is of type True
*)


Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. assumption. Qed.



Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).



Theorem peirce_to_classic : peirce -> classic.
unfold classic. unfold peirce. unfold not. 
intro H. intro P. intro A. (* CONTRAPOSITIVE *)

Theorem classicals :
(*
peirce <-> classic <-> excluded_middle <-> de_morgan_not_and_not <-> implies_to_or. 
*)