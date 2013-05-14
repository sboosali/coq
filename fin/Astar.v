Require Import Omega.
Require Import NPeano.

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

CoFixpoint A := node 1 [(B,1), (C,2)]
with       B := node 2 [(A,1), (C,1), (D,1)]
with       C := node 3 [(A,2), (B,1), (E,2)]
with       D := node 4 [(B,1), (C,1), (E,1)]
with       E := node 5 [(C,2), (F,1)]
with       F := node 6 [(E,1)]
with       Z := node 0 [(Z,1)].

Definition id (x:Node) : nat := match x with (node n _) => n end.
Definition edges (x:Node) := match x with (node _ ys) => ys end.
Definition children (x:Node) := map (@fst Node nat) (edges x).
Definition beq_node (x:Node) (y:Node) : bool := beq_nat (id x) (id y).
Definition elem_node := @elem Node beq_node.
Eval simpl in node (id A) (edges A). (* == A *)
Eval compute in children A.

Definition child (y:Node) (x:Node) : bool := elem_node y (children x).
Eval compute in child B A.
Notation "y 'child' x" := (child y x) (at level 10, no associativity) : node_scope.
Open Scope node_scope.
Eval compute in B child A.

Fixpoint get {A:Type} {B:Type} {beq:A->A->bool} (key:A) (val:B) (kvs : list (A * B)) : B :=
match kvs with
| (k,v)::kvs => if beq k key then v else @get A B beq key val kvs
| [] => val
end.
Definition get_edge key kvs := @get Node nat beq_node key 0 kvs.
Eval compute in get_edge A [(B,1), (C,2)] == 0.
Eval compute in get_edge B [(B,1), (C,2)] == 1.
Eval compute in get_edge C [(B,1), (C,2)] == 2.

Definition weight (x:Node) (y:Node) : nat := get_edge y (edges x).
Eval compute in weight A D == 0.
Eval compute in weight A B == 1.
Eval compute in weight A C == 2.


(* --------------------------------------------------- *)
(* Path *)

Definition elem_edge := @elem (Node*nat) (fun xw yv =>
let (x,w):=xw in let (y,v):=yv in beq_node x y && beq_nat w v).

(* Reflexive Transitive closure of child Definition *)
Inductive path : Node -> Node -> Type :=
| r_path : forall (x:Node), path x x
| t_path : forall (x:Node) (y:Node) (z:Node),
 y child x = true -> path y z -> path x z.
Theorem pathAC : path A C. Proof with auto.
apply (t_path A B C)... apply (t_path B C C)... constructor. Qed.
Print pathAC.

Fixpoint path_length {a b:Node} (p:path a b) : nat :=
match p with
| r_path _ => 0
| t_path x y z _ path_yz => weight x y + path_length path_yz
end.
Eval compute in path_length pathAC.

(*todo prove arbitrary transitivity *)


(* --------------------------------------------------- *)
(* f = g + h *)

(* Definition consistent {x:Node} (h :Node->nat) := forall y wxy, *)
(* elem_edge (y,wxy) (edges x) = true -> h x <= wxy + h y = true. *)

Definition consistent (h:Node->nat) (G:Node) :=
forall x:Node, path G x (* forall nodes in graph *)
-> forall y:Node, y child x = true
-> h x <= weight x y + h y.

(* prove that  f y >= f x *)
Theorem f_is_monotonic :
forall (x:Node) (y:Node), y child x = true ->
forall (gx:nat) (h:Node->nat), consistent h x ->
gx + h x <= gx + weight x y + h y.
(* by definition. f x = g x + h x *)
(* by definition. g y = g x + w x y *)
Proof. intros x y Child gx h Consistent.
rewrite<- plus_assoc.
rewrite<- (Nat.add_le_mono_l (h x) (weight x y + h y) gx).
apply Consistent; auto; constructor.
Qed.
(* unfold Consistent; omega. *)

(* --------------------------------------------------- *)
(* astar *)

Fixpoint put (xgh:Node*nat*nat) (ys:list (Node*nat*nat)) : list (Node*nat*nat) :=
match xgh with (x,gx,hx) =>
match ys with
| [] => [(x,gx,hx)]
| (y,gy,hy)::ys => if ble_nat (gy+hy) (gx+hx)
                   then (y,gy,hy) :: put (x,gx,hx) ys
                   else (x,gx,hx) :: (y,gy,hy) :: ys
end end.
Eval simpl in put (B,1,2) [(A,2,1),(C,2,2)].
Eval simpl in put (A,1,1) [(B,2,1),(C,1,2)].
Eval simpl in put (C,2,2) [(A,2,1),(B,1,2)].

Fixpoint puts (gx:nat) (h:Node->nat) (yws:list (Node*nat)) (q:list (Node*nat*nat)) : list (Node*nat*nat) :=
match yws with
| [] => q
| (y,w)::ys => puts gx h ys (put (y, gx + w, h y) q)
end.
Eval simpl in puts 1 (fun _ => 0) [(B,0),(C,1),(D,2)] [(A,0,0),(E,2,2)].

Fixpoint diff (ys:list (Node*nat)) (zs:list Node) :=
match ys with
| [] => []
| (y,w)::ys => if elem_node y zs then diff ys zs else (y,w) :: diff ys zs
end.
Eval simpl in diff [(A,0),(B,0),(C,0)] [B,C,D].

Definition Nodes := list Node.

(* astar Node    [(Node,nat,nat)]  [Node]      [Node] *)
(* astar node    open               closed      goals *)
(* astar current [(x,g(x),h(x))...] nodes-found goals-found *)

(* Inductive Maybe : Type -> Type := *)
(* | None : forall (A:Type), Maybe A *)
(* | Just : forall (A:Type), A -> Maybe A. *)
Inductive Maybe (A:Type) :=
| None : Maybe A
| Just : A -> Maybe A.
Implicit Arguments None [A].
Implicit Arguments Just [A].

(* A* on an infinite graph with no goal node will run forever.
   if A* is made to yield goals (like a generator), it runs forever.
   even on a graph with a node, A* runs in finite but unbounded time.
   thus, the Fixpoint A* decreases on some halting paramaeter.

   to simplify proofs, A* here only returns the node (or nothing),
   but it could be extended to return the path to the node.

   store (x, gx, hx) in priority queue with priority fx=gx+hx
*)
Fixpoint astar {h:Node->nat} {goal:Node->bool}
(i:nat) (open:list (Node*nat*nat)) (closed:list Node) : Maybe Node :=
match i with
| O => None
| S i =>
 match open with
 | [] => None
 | ((x,gx,hx)::open) => 
 (* skip *)
 if elem_node x closed then @astar h goal i open closed
 (* return goal *)
 else if goal x then Just x
 (* recur *)
 else @astar h goal i (puts gx h (edges x) open) (x::closed)
 end
end.

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

Function goal (x:Node) : bool := id x == 5. (* E *)

Eval compute in @astar h goal 10 [(A,0,h A)] [].




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