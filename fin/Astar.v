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
forall (x:Node) (G:Node), path G x (* forall nodes in graph *)
-> forall y:Node, y child x = true
-> h x <= weight x y + h y.

Theorem f_is_monotonic :
forall (xs:list Node) (x:Node) (y:Node), 
y child x = true -> weight x y > 0 ->
forall (h:Node->nat), consistent h ->
(f h) (x::xs) <= (f h) (y::x::xs).
(* by definition. f x = g x + h x *)
(* by definition. g y = g x + w x y *)
Proof. intros xs x y Child Positive h Consistent.
unfold f. unfold g. Admitted.
(* rewrite<- plus_assoc. *)
(* rewrite<- (Nat.add_le_mono_l (h x) (weight x y + h y) gx). *)
(* apply Consistent; auto; constructor. *)
(* Qed. *)
(* unfold Consistent; omega. *)

(* --------------------------------------------------- *)
(* e.g. *)

Function h (x:Node) : nat :=
match id x with
 | 1 => 2
 | 2 => 2
 | 3 => 1
 | 4 => 1
 | 5 => 0
 | 6 => 0
 | _ => 0
end.

Definition f' := f h.

Function goal (x:Node) : bool := id x == 5. (* x5 is goal *)

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

Fixpoint astar {f:list Node -> nat} {goal:Node->bool}
(i:nat) (open:list (list Node)) (closed:list Node)
: list Node * list Node :=
match i with
| O => ([] , closed)
| S i =>
 match open with
 | [] => ([] , closed)
 | xs::open => match xs with | [] => ([] , closed) | x::xs =>
 (* skip *)
 if elem_node x closed then @astar f goal i open closed
 (* return goal *)
 else if goal x then (rev (x::xs) , (x::closed))
 (* recur *)
 else @astar f goal i (puts f (map (fun y => y::x::xs) (children x)) open) (x::closed)
end end end.

Definition eg_astar i G := 
let (path,seen) := @astar f' goal i [[G]] []
in (map id path, map id seen).
Eval compute in eg_astar 10 x1.



(* --------------------------------------------------- *)
(* astar is sound *)



(* --------------------------------------------------- *)
(* astar is complete *)

(*
define. g x = |path G x|
define. h y <= h x + d x y
prove. f y >= f x
prove. must pop all {x|f(x)=n} before pop any {x|f(x)>n}
prove. forall n |{x|f(x)=n}| < ∞
define. f ~> g ~> path
*)

(* in graph -> A* out *)
(*
A* will pop every node of some f-value (= f_max) or less in finite time.
in particular, a goal node (with some path) z has some f(z) = g(z) + h(z) (where h is just a function and g depends on the path). this, as a function of the nodes with smaller or equal f-values, bounds the number of steps that A* must take before getting to z.

the problem is that since f is only monotonic. i.e. f(y) >= f(x) implies that f(y) may equal f(x); however, each time a child y of node x is pushed onto the priority queue with priortity f(y), since the weights of the graph are strictly positive, g(y) > g(x), and for f(y) = f(x), then it must be that h(y) < h(x); h is nonnegative, so after finitely many such steps, h will decrease to zero, and then g must increase until it is the f_max.

for this, i could define an A* Fixpoint that decreases on the f-value. however, since there are a few arguments that may decrease:
f_max - f_curr  ==>  0
f_max - g_curr  ==>  0
h_curr          ==>  0

g always increases, but either f increases or h decreases, and i think i need to prove this non-structural recursion terminates (like you do with mergesort).

i thought of proving an easier theorem, that BFS is complete (perhaps strengthening the assumptions with knowing the maximum breadth), as an instance of my definition of A*.

BFS is A* with
h _ = 0
w _ _ = 1

thus
f = g + h = g = depth

but i ran out of time
*)

(* --------------------------------------------------- *)
(* etc *)
Print Grammar constr.


