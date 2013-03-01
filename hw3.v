Require Import Coq.Lists.List.



Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.







Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "m ++ n" := (app m n) (at level 60, right associativity).

(* WARMUP: Understanding inductive definitions *)
Module Warmup.
(* Consider the following two inductively defined types. *)
Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Which of the following are well-typed elements of grumble X for some type X? *)

(* FILL IN HERE
bool : Set
the constructors need explicit type params
*)
Print bool.
(*Check d (b a 5).*)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(*Check e bool (b c 0).*)
Check c.


(* Consider the following inductive definition: *)
Inductive baz : Type :=
   | baz_x : baz -> baz
   | baz_y : baz -> bool -> baz.

(* How many values are there of type baz? *)
(* FILL IN HERE 
0
there is no basecase i.e. 0-ary constructor
*)
End Warmup.

(* Writing polymorphic functions *)
Module PolyFun.
(** The function [split_list] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split_list].  Make sure it passes the given unit tests. *)

Check pair.
Check prod. (* "X * Y" *)
Check cons.
Check list.

Fixpoint pair_append {X Y:Type} (x : X) (y : Y) (xsys: (list X) * (list Y))
: (list X) * (list Y) :=
match xsys with
  | (xs,ys) => (x::xs,y::ys)
end.

Fixpoint split_list {X Y:Type} (l:list (X * Y)) 
: (list X) * (list Y) :=
match l with
  | nil => ([],[])
  | (x,y)::xys => pair_append x y (split_list xys)
end.

Example test_split_1:
  split_list [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity.  Qed.
Example test_split_2:
  split_list [(Some 1,1),(Some 2,2),(Some 3, 6),(None, 24)] 
    = ([Some 1,Some 2,Some 3,None],[1,2,6,24]).
Proof. reflexivity.  Qed.

End PolyFun.

(* Proving polymorphic lemmas *)
Module PolyProofs.

(* Note: We're using Coq's predefined map and rev functions;
   you may want to SearchAbout them to find out what exists.
   Don't use the existing map_rev as the entirety of your proof! *)

Theorem map_distributes_append : forall (A B : Type) (f : A -> B), forall (xs ys : list A), 
map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
intros A B f.
induction xs as [|x xs]. reflexivity.
simpl. intro ys. rewrite<- IHxs. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros X Y f.
induction l. reflexivity.
simpl. rewrite<- IHl. apply map_distributes_append.
Qed.

Require Import EqNat.
Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None 
    | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

(* Explain the type of the theorem below, then prove it.
   1. Why do we not have to write explicit type annotations for 
      X, n and l?
type inference

   2. What (in general) is the type of None?
None : option X
or
None : {X:type} option X
or
exists X:type . None : option X
or
something like that

   3. What type does coq give the expression 'None' in the theorem below, and why?
Check None.  =>  None : option ?91
because length and index are polymorphic
*)

(* FILL IN HERE *)
Theorem index_off_end : forall X n l, 
length l = n -> @index X (S n) l = None.
Proof.
  (* FILL IN HERE *)
(* can i swap quantifiers to do strong induction on 'l' forall 'n' *)
intros. generalize dependent n.
induction l as [|x xs]. reflexivity.
simpl. intros. subst.
apply IHxs. reflexivity.
Qed.


End PolyProofs.

(* Use inversion to complete these proofs -- the proofs should be very short *)
Module Inversion.
Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
intros. inversion H. reflexivity.
Qed.

Example nonempty_nil : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* FILL IN HERE *)
intros.
inversion H.
Qed.

End Inversion.

Module StrengtheningInduction.
Import PolyProofs.
(* Carry out this proof by induction on m. 
   Use [generalize dependent] to re-generalize variables
   that you don't initially want in the context *)



SearchAbout le.
Require Import Plus.
Check le_plus_l.


Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  (* FILL IN HERE *)
induction n as [|n].
 Case "n = 0". simpl. destruct m.
  SCase "m = 0". reflexivity. 
  SCase "m = S m". assert (H := (le_plus_l (S m) (S m))). intro A. rewrite<- A in H. inversion H.

 Case "n = S n". destruct m.
  SCase "m = 0". intro A. inversion A. (* inversion what how? *)
  SCase "m = S m". intro H. inversion H.
  rewrite plus_comm in H1. symmetry in H1. rewrite plus_comm in H1. inversion H1.
  assert (A := eq_S n m). (* apply IHn then A *)
  intros. apply A in IHn. exact IHn. symmetry. exact H2.
Qed.

(* 
apply (le_plus_l n n).
generalize dependent n. 
*)

(* Now prove this by induction on l. Why? we already did. *)
Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index (S n) l = None.
Proof.
  (* FILL IN HERE *)
intros. apply index_off_end. assumption.
Qed.


Theorem pred_both : forall x y,
x > 0 -> y > 0 -> 
x = y -> pred x = pred y.
intros. destruct x.
 inversion H.
 subst. reflexivity.
Qed.

SearchAbout app.
(* Prove this by induction on l1, without using app_length. AW CMON MAN *)
Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* FILL IN HERE *)
(*
prove by the multiset (or set) properties of lists
i.e.
the properties of lists that hold when made a multiset (or set)
i.e.
the properties of lists that dont depend on order (nor duplicates)

e.g.
length xs++ys = length ys++xs
because multisets ignore order
multiset xs++ys = multiset ys++xs
or because addition commutes
length xs++ys = length ys + length xs

list < multiset < set
*)

induction l1 as [|y ys]. 

Case "l1 = []".
 intros. rewrite app_nil_l. rewrite app_nil_l in H. simpl in H. assumption.

Case "l1 = y::ys". 
 intros. simpl. simpl in H.
 assert (A := IHys l2 x (pred n)).
 assert (B := (eq_S (S (length (ys ++ l2))) (pred n))).
 apply B in A. rewrite NPeano.Nat.succ_pred_pos in A. exact A.
 SCase "assertion". rewrite<- H. apply Lt.lt_0_Sn.
 SCase "assertion". rewrite<- H. reflexivity.
Qed.

End StrengtheningInduction.  
