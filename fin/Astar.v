Require Import Omega.
Require Import NPeano.

(* autocomplete
SearchAbout

*)

(* --------------------------------------------------- *)
(* Helpers *)

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


Require Import Arith.

Require Import Bool.
Open Scope bool_scope.
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.
Notation " x == y " := (beq_nat x y)
(at level 50, no associativity) : bool_scope.
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.
(* Notation " x <= y " := (ble_nat x y) *)
(* (at level 70, no associativity) : bool_scope. *)


Require Import List.
Require Import Coq.Lists.List.
Open Scope list_scope.
Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..) : list_scope.

Fixpoint elem {X:Type} {eq:X->X->bool} (x:X) (ys:list X) : bool :=
match ys with
| [] => false
| y::ys => if eq x y then true else @elem X eq x ys
end.
Definition elem_nat := @elem nat beq_nat.
Eval simpl in elem_nat 0 [3,2,1].
Eval simpl in elem_nat 1 [3,2,1].


(* --------------------------------------------------- *)
(* Graph *)

CoInductive Node := | node : nat -> list (Node * nat) -> Node.
(* directed weighted connected locally-finite graph *)
Definition leaf := node 0 [].

CoFixpoint x1 := node 1 [(x2,1), (x3,2)]
with       x2 := node 2 [(x1,1), (x3,1), (x4,1)]
with       x3 := node 3 [(x1,2), (x2,1), (x5,2)]
with       x4 := node 4 [(x2,1), (x3,1), (x5,1)]
with       x5 := node 5 [(x3,2), (x6,1)]
with       x6 := node 6 [(x5,1)]
with       x0 := node 0 [(x0,1)].

Definition id (x:Node) : nat := match x with (node n _) => n end.
Definition edges (x:Node) := match x with (node _ ys) => ys end.
Definition children (x:Node) := map (@fst Node nat) (edges x).
Definition beq_node (x:Node) (y:Node) : bool := beq_nat (id x) (id y).
Definition elem_node := @elem Node beq_node.
Eval simpl in node (id x1) (edges x1). (* == A *)
Eval compute in children x1.

Definition child (y:Node) (x:Node) : bool := elem_node y (children x).
Eval compute in child x2 x1.
Notation "y 'child' x" := (child y x) (at level 10, no associativity) : node_scope.
Open Scope node_scope.
Eval compute in x2 child x1.

Fixpoint get {A:Type} {B:Type} {beq:A->A->bool} (key:A) (val:B) (kvs : list (A * B)) : B :=
match kvs with
| (k,v)::kvs => if beq k key then v else @get A B beq key val kvs
| [] => val
end.
Definition get_edge key kvs := @get Node nat beq_node key 0 kvs.
Eval compute in get_edge x1 [(x2,1), (x3,2)] == 0.
Eval compute in get_edge x2 [(x2,1), (x3,2)] == 1.
Eval compute in get_edge x3 [(x2,1), (x3,2)] == 2.

(* todo weight outs Maybe (None if y is not a child of x) *)
Definition weight (x:Node) (y:Node) : nat := get_edge y (edges x).
Eval compute in weight x1 x4 == 0.
Eval compute in weight x1 x2 == 1.
Eval compute in weight x1 x3 == 2.

(* --------------------------------------------------- *)
(* Path *)

Definition elem_edge := @elem (Node*nat) (fun xw yv =>
let (x,w):=xw in let (y,v):=yv in beq_node x y && beq_nat w v).

(* Reflexive Transitive closure of child Definition *)
Inductive path : Node -> Node -> Type :=
| r_path : forall (x:Node), path x x
| t_path : forall (x:Node) (y:Node) (z:Node),
 y child x = true -> path y z -> path x z.

Fixpoint path_length {a b:Node} (p:path a b) : nat :=
match p with
| r_path _ => 0
| t_path x y z _ path_yz => weight x y + path_length path_yz
end.

Definition path12 : path x1 x3 :=
t_path x1 x2 x3 eq_refl (t_path x2 x3 x3 eq_refl (r_path x3)).
Print path12.
(* apply (t_path A B C)... apply (t_path B C C)... constructor. *)
(* Theorems are opaque, Definitions are transparent *)
(* take Theorem to Definition: define with Theorem (e.g. using automatic theorem proving tactics), then copypaste Proof object into Definition *)
Eval compute in path_length path12.

(*todo prove arbitrary transitivity *)

(* --------------------------------------------------- *)
(* f = g + h *)

Fixpoint g' (xys:list Node) :=
match xys with
| (x::ys) =>
 match ys with
 | (y::_) => weight x y + g' ys
 | [] => 0
 end
| _ => 0
end.
(* astar grows path by cons i.e. backwards *)
Function g (path:list Node) : nat := g' (rev path).
Eval compute in g [x3,x2,x1] == 2.
Eval compute in g [x5,x3,x1] == 4.

Function f (h:Node->nat) (xs:list Node) :=
match xs with
| x::xs => g (x::xs) + h x (* path cost + heuristic *)
| _ => 0 (* never *)
end.

(* the path cost function "g" is the same for all graphs *)
(* the heuristic "h" must be consistent wrt some graph (assumed in proofs with "f", not in definition of "f") *)
(* any A* shares "f" and "g", while "h" and "goal" are params *)

Definition consistent (h:Node->nat) :=
forall (x:Node) (y:Node), y child x = true
-> h x <= weight x y + h y.

Lemma g_homomorphic : 
forall (ys:list Node) (y:Node) (x:Node) (xs:list Node),
y child x = true ->
g (ys ++ [y,x] ++ xs) = g (ys ++ [y]) + g [y,x] + g ([x] ++ xs).
Proof. intros xs x y ys Child.
Admitted.

Lemma g_adds_weight : (* strictly *)
forall (xs:list Node) (x:Node) (y:Node), 
y child x = true ->
g (y::x::xs) = g (x::xs) + weight x y.
Proof. intros xs x y Child.
assert (y::x::xs = [y,x]++xs).
 auto. rewrite H. clear H.
assert (weight x y = g [y,x]).
 unfold g. unfold g'. simpl. omega. rewrite H. clear H.
assert ([y,x] ++ xs = [] ++ [y,x] ++ xs).
 apply app_nil_l. rewrite H. clear H.
assert (g (x :: xs) + g [y, x] = g [y, x] + g (x :: xs)).
 apply plus_comm. rewrite H. clear H.
assert (g [y, x] + g (x :: xs) = (g ([]++[y]) + g [y, x] + g (x :: xs))).
 auto. rewrite H. clear H.
apply (g_homomorphic [] y x xs); auto.
Qed.


Lemma f_is_monotonic : (* weakly *)
forall (xs:list Node) (x:Node) (y:Node), 
y child x = true ->
forall (h:Node->nat), consistent h ->
(f h) (x::xs) <= (f h) (y::x::xs).
(* by definition. f x = g x + h x *)
(* by definition. g y = g x + w x y *)

Proof. intros xs x y Child h Consistent. unfold f.
assert (g (y::x::xs) = g (x::xs) + weight x y) as G.
 apply (g_adds_weight xs x y Child).
 rewrite G.
rewrite<- plus_assoc.
rewrite<- (Nat.add_le_mono_l (h x) (weight x y + h y) (g (x::xs))).
apply Consistent; assumption.
Qed.


Lemma g_increases :
forall (xs:list Node) (x:Node) (y:Node),
y child x = true -> weight x y > 0 ->
forall (h:Node->nat), consistent h ->
g (x::xs) < g (y::x::xs).
Proof. intros xs x y Child Positive h Consistent.
pose proof (g_adds_weight xs x y Child) as W.
omega. Qed.


(* use as fixpoint decreasing argument *)
(* either [f_max - f => 0] or [h => 0] *)
Lemma f_increases_or_h_decreases :
forall (xs:list Node) (x:Node) (y:Node),
y child x = true -> weight x y > 0 ->
forall (h:Node->nat), consistent h ->
(f h) (x::xs) < (f h) (y::x::xs)  \/  h y < h x.
Proof. intros xs x y Child Positive h Consistent.
pose proof (f_is_monotonic xs x y Child h Consistent) as F.

unfold f in *. 
Admitted.


(* --------------------------------------------------- *)
(* e.g. *)

Function eg_h (x:Node) : nat :=
match id x with
 | 1 => 2
 | 2 => 2
 | 3 => 1
 | 4 => 1
 | 5 => 0
 | 6 => 0
 | _ => 0
end.

Function eg_goal (x:Node) : bool := id x == 5. (* x5 is goal *)


(* --------------------------------------------------- *)
(* Lemmas *)

Lemma split_tuple : forall (A B : Type) (xy : A*B) (x:A) (y:B),
xy = (x,y) -> (fst xy) = x /\ (snd xy) = y. Admitted.

Lemma elem_implies_nonempty :
forall (A:Type) (eq:A->A->bool) (x:A) (ys:list A),
@elem A eq x ys = true
->
(ys = [] -> False).
Proof. intros A eq x ys In Empty.
subst. compute in In. inversion In. Qed.


(* --------------------------------------------------- *)
(* astar *)

(* put into priority queue *)
Fixpoint put {A:Type} (f:A->nat) (x:A) (ys:list A) : list A :=
match ys with
| [] => [x]
(* like queue on same priority i.e. first in first out *)
| (y::ys) => if ble_nat (f y) (f x)
             then y :: put f x ys
             else x :: y :: ys
end.
Definition I {A:Type} (x:A) : A := x.
(* base case *)
Eval simpl in put I 1 [].
(* put lesser before *)
Eval simpl in put I 1 [2].
(* put same after *)
Eval simpl in put (fun _ => 0) 2 [1].
(* put greater after *)
Eval simpl in put I 2 [1].

SearchAbout list.
Definition puts {A:Type} (f:A->nat) (xs:list A) (ys:list A) : list A 
:= fold_left (fun ys x => put f x ys) xs ys.
Eval simpl in puts I [1,2,4,5] [3].
Eval simpl in puts (fun _ => 0) [2] [1].

Inductive Maybe (A:Type) :=
| None : Maybe A
| Just : A -> Maybe A.
Arguments None [A].
Implicit Arguments Just [A].
Check None.
Check Just 0.

Definition Nodes := list Node.

(* A* on an infinite graph with no goal node will run forever.
   if A* is made to yield goals (like a generator), it runs forever.
   even on a graph with a node, A* runs in finite but unbounded time.
   thus, the Fixpoint A* decreases on some halting paramaeter.

   to simplify proofs, A* here only returns the node (or nothing),
   but it could be extended to return the path to the node.

   store (x, gx, hx) in priority queue with priority fx=gx+hx

   open ~ todo  .  closed ~ done
*)

Fixpoint astar {h:Node->nat} {goal:Node->bool}
(i:nat) (open:list (list Node)) (closed:list Node)
: list Node * list Node :=      (* todo list (forall x y, path x y) *)
let f := f h in
match i with
| O => ([] , closed)
| S i =>
 match open with
 | [] => ([] , closed)
 | xs::open => match xs with | [] => ([] , closed) | x::xs =>
 (* skip *)
 if elem_node x closed then @astar h goal i open closed
 (* return goal *)
 else if goal x then ((x::xs) , (x::closed))
 (* recur *)
 else @astar h goal i (puts f (map (fun y => y::x::xs) (children x)) open) (x::closed)
end end end.

Definition eg_astar i G := 
let (path,seen) := @astar eg_h eg_goal i [[G]] []
in (map id (rev path), map id seen).
Eval compute in eg_astar 10 x1.


(* Theorem astar_is_monotonic : *)
(* forall (x:Node) (y:Node) (z:Node), path x y -> path x z -> *)
(* forall (h:Node->nat) (goal:Node->bool), consistent h -> *)
(* forall (K:nat) (p c:list Node), (y::p, c) = @astar h goal K [[x]] [] -> *)
(* forall (K':nat) (p' c':list Node), (z::p', c') = @astar h goal K' [[x]] [] -> *)
(* (f h) (y::p) <= (f h) (z::p') *)
(* -> *)


Theorem astar_is_optimal :
forall (x:Node) (z:Node) (p:path x z),
forall (h:Node->nat) (goal:Node->bool) (K:nat), consistent h ->
forall (zs ys:list Node), (z::zs, ys) = @astar h goal K [[x]] []
->
g (z::zs) <= path_length p.

Proof. intros x z p h goal K Consistent zs ys A.
Admitted.

(* --------------------------------------------------- *)
(* astar is sound *)

(* figure this out first *)
Fixpoint find y xs :=
match xs with
| [] => []
| x::xs => if x==y then [x] else find y xs
end.
Goal forall x y xs, [x] = find y xs -> x==y = true.
intros. generalize dependent x.
induction xs; intros. inversion H.
simpl in H. destruct (a==y) eqn:AeqY.
inversion H. subst. auto. auto.
Qed.


Theorem astar_is_sound :
forall (a:Node) (z:Node),
forall (h:Node->nat) (goal:Node->bool) (K:nat), consistent h ->
forall (zs ys:list Node), (z::zs, ys) = @astar h goal K [[a]] []
->
goal z = true.

Proof. intros a z h goal K Consistent zs ys A.
(* match match if if *)
(* if goal z then (z::_, _) *)
(* compute in A. *)
unfold astar in *. simpl in A.

Admitted.



(* --------------------------------------------------- *)
(* astar is complete *)

Lemma astar_visits_every_node : 
forall (x:Node) (y:Node), path x y ->
(forall x y, weight x y > 0) ->
forall (h:Node->nat) (goal:Node->bool), consistent h
->
exists (K:nat) (xs:list Node) (ys:list Node),
@astar h goal K [[x]] [] = (xs,ys)  /\  elem_node y ys = true.

Proof. intros x y Path Positive h goal Consistent.
(* uses

*)
Admitted.


(* ----------------------- *)

Lemma astar_pops_goal :
forall (x:Node) (z:Node),
(forall x y, weight x y > 0) ->
forall (h:Node->nat) (goal:Node->bool), consistent h ->
forall (K:nat) (seen:list Node),
elem_node z seen = true
->
exists xs, @astar h goal K [[x]] [] = (z::xs, seen).

Proof. intros x z Positive h goal Consistent K seen Seen.
assert (seen = [] -> False) as Nonempty. intro Empty.
 apply (elem_implies_nonempty Node beq_node z seen Seen Empty).
unfold astar.
Admitted.

(* ----------------------- *)

Theorem astar_is_complete :
(* graph *)
forall (x:Node) (z:Node), path x z ->
(forall x y, weight x y > 0) ->
(* params *)
forall (h:Node->nat) (goal:Node->bool), consistent h ->
(* only one goal *)
(forall y:Node, goal y = true <-> beq_node y z = true)
->
exists (K:nat) (xs:list Node),
fst (@astar h goal K [[x]] []) = z::xs.

Proof. intros x z Path Positive h goal Consistent One.

(* A* visits every node, the goal in particular *)
pose proof (astar_visits_every_node x z Path Positive h goal Consistent) as H.
elim H; intro K; clear H; intro H.
elim H; intro zs; clear H; intro H.
elim H; intro ys; clear H; intro H. 
destruct H as [Astar Seen].
exists K.

(* A* returns the goal if it visits the goal *)
pose proof (astar_pops_goal x z Positive h goal Consistent K ys Seen) as G.
elim G; intro xs; clear G; intro G.
assert (fst (@astar h goal K [[x]] []) = z :: xs) as G'.
apply split_tuple in G. 
elim G; intro G'; clear G; intro G. assumption.
exists xs. assumption.

Qed.
