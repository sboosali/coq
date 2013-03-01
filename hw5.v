Require Import Cases.
Definition admit {T:Type} : T. Admitted.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.
Definition even (n:nat) : Prop := 
  evenb n = true.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(* 1. Explain why proving the following lemma the "obvious" way gets stuck. *)
Lemma even__even_broken: forall n : nat, even n -> ev n.
Proof. induction n. Admitted.
(*
you must induct on the proof of evenness (where 'next' is 'S (S _)'), not on the even number (where 'next' is 'S'). "ev n" can prove "ev (S (S n))" but not "ev (S n)".
*)

(* SearchAbout *)

(*
"ev -> even" is easy because we induct on ev
"even -> ev" is hard

*)

Lemma even__iff__even_SS : forall n,
even (S (S n)) <-> even n.
Proof. intros. split.

Case "<-". intros. inversion H. assumption.

Case "->". intros. induction n.
auto. inversion H. apply H1.

Qed.

Lemma ev_implies_even : forall n : nat,
ev n -> even n.
intros. induction H.
reflexivity.
apply even__iff__even_SS. assumption.
Qed.

Lemma even_not_odd : forall n,
even n -> ~(even (S n)).
unfold not. intros. induction n.
inversion H0.
apply IHn; assumption.
Qed.

Lemma odd_not_even : forall n,
~(even (S n)) -> even n.
intros. induction n.
reflexivity.
rewrite even__iff__even_SS in H.
apply H in IHn. contradiction.
intros A. apply H.
inversion A as [A1].
unfold even.

Admitted.

(* 2. Complete the following proof instead. *)
Lemma even__even : forall n : nat,
(even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof. intro. apply and_comm. split.

Case "n". intros. induction n.

inversion H.

apply ev_SS. rewrite even__iff__even_SS in H.
admit.


Case "S n". admit.
Qed.

(* cant do it *)

(* 3. Construct a proof object demonstrating the following proposition. *)
Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
fun (P Q R : Prop) (pq : P /\ Q) (qr : Q /\ R) => 
(* take proof of P from PQ and proof of Q from QR to make a proof of PR *)
conj
 match pq with conj p q => p end
 match qr with conj q r => r end
.


(* 4. Distributing or over and *)
(* This one is provided from the notes... *)
Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR. Qed.

(* Prove the reverse direction... *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
intros. inversion H as [[HP | HQ] [HP' | HR]].
left. assumption.
left. assumption.
left. assumption.
right. split; assumption.
Qed. 

(* ...and give a *short* proof of the if-and-only-if *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. split.
 apply or_distributes_over_and_1.
 apply or_distributes_over_and_2.
Qed.

(* 5. Facts about not and or *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~ Q -> ~ P).
Proof.
unfold not. intros P Q. intros A B C.
apply B. apply A. apply C.
Qed.

Theorem not_both_true_and_false : forall P:Prop, ~(P /\ ~ P).
Proof.
intros P H. unfold not in *. inversion H.
apply (H1 H0).
Qed.

(* Why does the following lemma get stuck? *)
Lemma broken : forall (P Q:Prop),
  (P -> Q) -> (~ P -> False) -> Q.
Proof.
  intros. apply H. unfold not in *. Admitted.
(* we just cant prove P. its on the left of the hypotheses. if we try the contrapositive, we just get the same *)


(* 6. Tricky!  The following five statements are often 
      considered as characterizations of classical logic.  We can't
      prove them in Coq, but we can add any of them as an unproven
      axiom if we want to work in classical logic.  

      For credit in this problem, prove that "de_morgan_not_and_not"
      and "excluded_middle" are equivalent.

      For extra credit, prove that all five definitions are 
      equivalent.  If you try this part:
        Hint 1: You can prove this equivalence in just five
                implications.
        Hint 2: Follow the ordering of the definitions below.
*)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition classic := forall P:Prop,
  ~~P  ->  P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P/\~Q)  ->  P\/Q.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q)  ->  (~P\/Q).

Theorem peirce_implies_classic : peirce -> classic.
unfold peirce, classic. intros Peirce P.
unfold not at 2. intro NN. apply (Peirce P False). intro N.
contradiction.
Qed.

Theorem classic_implies_demorgan : classic -> de_morgan_not_and_not.
unfold classic, de_morgan_not_and_not.
intro Classic. intros P Q. unfold not.
intro nan. apply Classic. unfold not.
intro nor. apply nan. 
split.
 intro. apply nor. left. assumption.
 intro. apply nor. right. assumption.
Qed.

Theorem demorgan_implies_exclude : de_morgan_not_and_not -> excluded_middle.
unfold de_morgan_not_and_not, excluded_middle.
intros Demogran P. apply Demogran. unfold not. intro.
inversion H. contradiction.
Qed.

Theorem exclude__implies__imply_is_or : excluded_middle -> implies_to_or.
unfold excluded_middle, implies_to_or.
intros EM. intros P Q H.
Check EM P.
remember (EM P) as either_or. inversion either_or as [T|F].
(* syntax for "inversion (EM P)" ? *)
Case "P is true". right. apply (H T).
Case "P is false". left. assumption.
Qed.


Theorem O2I : forall P Q : Prop,
 (P -> False) \/ Q -> (P -> Q).
Proof. intros. inversion H. contradiction. assumption.
Qed.

(*
Theorem __classical__or_iff_implies : forall P Q : Prop,
 classic ->
 ((P -> Q)  <->  (P -> False) \/ Q).
Proof. intros.
apply classic_implies_demorgan in H.
apply demorgan_implies_exclude in H.
apply exclude__implies__imply_is_or in H.
split. apply H. apply O2I.
Qed.
*)

Theorem __classical__or_iff_implies : forall P Q : Prop,
 ((P -> Q)  <->  (P -> False) \/ Q).
Admitted.

Theorem imply_is_or__implies__peirce : implies_to_or -> peirce.
unfold implies_to_or, peirce, not.
intros I2O. intros P Q. intros H.

remember H as H'. clear HeqH'.
apply I2O in H.
assert (OiffI := __classical__or_iff_implies).
rewrite (OiffI P Q) in H.

destruct H as [A|B].
(* rewrite de_morgan_not_and_not in A. *)

(*
rewrite (I2O P Q) in L. 
apply H. intro HP.
apply I2O in H. destruct H as [L|R]. 
*)

Case "hard". (* admit. dammit, the last one *)
admit.


Case "easy". assumption.
Admitted.

(* remember (I2O (P->Q) P H) as A. clear HeqA. inversion A as [L|R].
Case "P left". apply H. 
 remember (P -> Q) as PiQ. clear HeqPiQ. apply PiQ in L.
Case "P right". assumption.
*)























(* 7. Forall and exists, in classical logic *)
Theorem forall__not_exists_not : 
  forall (X:Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof. (* This should be a *short* proof *)
unfold not. intros X P A E.
 inversion E. apply H. apply A.
Qed.


Theorem not_exists_not__forall : excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof. unfold excluded_middle. unfold not.
intros EM. intro X. intro P. intro NN. intro x.

assert (P x \/ (P x -> False)). apply EM.
inversion H as [L|R].

assumption.

assert False. apply NN. exists x.
assumption.
contradiction.

Qed.


(* Theorem not_exists__forall_not : excluded_middle ->
  forall (X : Type) (P : X -> Prop), 
    ~ (exists x, P x) -> (forall x, ~ P x).
Proof.
unfold excluded_middle. unfold not. intros EM X P E w H.
apply E. exists w. assumption.
Qed.
*)













(* 8. Multi-place relations *)
Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(* The relation R above relates triples of numbers.  Which of the
   following two terms are provable?

   R 1 1 2
   R 2 2 6 *)
Goal R 1 1 2. apply c3. apply c2. apply c1. Qed.

(* If we dropped the constructor c5 from the definition of R, would
   the set of provable propositions change?  Why? (1-sentence answer)
 *)
(* ANSWER no because "apply c5. apply c2." is just "apply c3." when m <> n (and does nothing otherwise) *)

(* If  we dropped the constructor c4, would the set of provable
   propositions change?  Why?  (1-sentence answer) *)
(* ANSWER no because  "apply c5." undoes "apply c2. apply c3." *)

(* In words, describe what common relationship between numbers is 
   expressed by R. *)
(* "m, n and o are related by R iff m+n=o." nice. *)
