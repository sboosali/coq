(*
*** Local Variables: ***
*** coq-prog-name: "coqtop -I . -emacs -impredicative-set"
***** End: ***
in my .bashrc
alias="coqtop -I . -emacs -impredicative-set"
*)

(* Add Rec LoadPath "NodeBasics". *)
(* Print LoadPath. *)
(* Require NodeBasics.Digraphs. *)
(* Check NodeBasics.Digraphs.Digraph. *)

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
Notation " x <= y " := (ble_nat x y)
(at level 70, no associativity) : bool_scope.

Require Import List.
Open Scope list_scope.
Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..) : list_scope.
Fixpoint elem_nat (x:nat) (ys:list nat) : bool :=
match ys with
| [] => false
| y::ys => if x==y then true else elem_nat x ys
end.
Eval simpl in elem_nat 0 [3,2,1].
Eval simpl in elem_nat 1 [3,2,1].

SearchAbout list.
(* CoInductive Node := graph : nat -> list Node -> Node. *)
(* coinductive graph with inductive list 
-> possibly infinite but locally finite graph
-> degree of graph is unbounded but finite
*)
(* CoFixpoint g1 := graph 1 [g2, g3] *)
(* with       g2 := graph 2 [g0] *)
(* with       g3 := graph 3 nil *)
(* with       g0 := graph 0 [g0]. *)

CoInductive Node := node : nat -> list (Node * nat) -> Node.
(* directed weighted connected graph *)

Definition leaf := node 0 [].

CoFixpoint A := node 1 [(B,1), (C,2)]
with       B := node 2 [(A,1), (C,1), (D,1)]
with       C := node 3 [(A,2), (B,1), (E,2)]
with       D := node 4 [(B,1), (C,1), (E,1)]
with       E := node 5 [(C,2), (F,1)]
with       F := node 6 [(E,1)]
with       Z := node 0 [(Z,1)].

Function id (G:Node) : nat := match G with (node n _) => n end.
Function next (G:Node) := match G with (node _ ys) => ys end.
Eval simpl in (node (id A) (next A)). (* == A *)

Function h (G:Node) : nat := (*let (n, _) := G in*)
match id G with
 | 1 => 2
 | 2 => 2
 | 3 => 1
 | 4 => 1
 | 5 => 0
 | 6 => 0
 | _ => 0
end.

Function goal (G:Node) : bool := id G == 5.

Fixpoint put (xgh:Node*nat*nat) (ys:list (Node*nat*nat)) : list (Node*nat*nat) :=
match xgh with (x,gx,hx) =>
match ys with
| [] => [(x,gx,hx)]
| (y,gy,hy)::ys => if gy+hy <= gx+hx 
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

Fixpoint elem_node (x:Node) (ys:list Node) : bool :=
match ys with
| [] => false
| y::ys => if id x == id y then true else elem_node x ys
end.
Eval simpl in elem_node Z [C,B,A].
Eval simpl in elem_node A [C,B,A].

Fixpoint diff (ys:list (Node*nat)) (zs:list Node) :=
match ys with
| [] => []
| (y,w)::ys => if elem_node y zs then diff ys zs else (y,w) :: diff ys zs
end.
Eval simpl in diff [(A,0),(B,0),(C,0)] [B,C,D].

Definition Nodes := list Node.

(* astar Node   [(Node,nat,nat)]  [Node]     [Node] *)
(* astar node    open               closed      goals *)
(* astar current [(x,g(x),h(x))...] nodes-found goals-found *)
Inductive astar 
{h:Node->nat} {goal:Node->bool}
: Node -> list (Node*nat*nat) -> Nodes -> Nodes
-> Type
:=
(* "| halt" would be identity, thus implicit *)

(* base case *)
| init  : forall x:Node,
  astar x [(x, 0, h x)] [] []

(* might remove, simplifies computation but complicates induction *)
| skip : forall (x:Node) (open:list (Node*nat*nat)) (closed:Nodes) (goals:Nodes),
 elem_node x closed = true
 -> forall (z:Node) (gx:nat) (hx:nat), astar z ((x,gx,hx)::open) closed goals
 -> astar z open closed goals

| pop : forall (x:Node) (open:list (Node*nat*nat)) (closed:Nodes) (goals:Nodes),
 forall (z:Node) (gx:nat) (hx:nat), astar z ((x, gx, hx)::open) closed goals
 -> astar x (puts gx h (diff (next x) closed) open) closed goals

(* just liek pop, except for [goal x = true] and [(x::goals)] *)
| yield : forall (x:Node) (open:list (Node*nat*nat)) (closed:Nodes) (goals:Nodes),
 goal x = true
 -> forall (z:Node) (gx:nat) (hx:nat), astar z ((x, gx, hx)::open) closed goals
 -> astar x (puts gx h (diff (next x) closed) open) closed (x::goals)
 
.


