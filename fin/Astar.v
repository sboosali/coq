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

Fixpoint elem {X:Type} {eq:X->X->bool} (x:X) (ys:list X) : bool :=
match ys with
| [] => false
| y::ys => if eq x y then true else @elem X eq x ys
end.
Definition elem_nat := @elem nat beq_nat.
Eval simpl in elem_nat 0 [3,2,1].
Eval simpl in elem_nat 1 [3,2,1].


(* --------------------------------------------------- *)

CoInductive Node := | node : nat -> list (Node * nat) -> Node.
(* directed weighted connected finite graph *)
Definition leaf := node 0 [].

CoFixpoint A := node 1 [(B,1), (C,2)]
with       B := node 2 [(A,1), (C,1), (D,1)]
with       C := node 3 [(A,2), (B,1), (E,2)]
with       D := node 4 [(B,1), (C,1), (E,1)]
with       E := node 5 [(C,2), (F,1)]
with       F := node 6 [(E,1)]
with       Z := node 0 [(Z,1)].

(* Inductive Node := | node : nat -> list (Node * nat) -> Node. *)
(* Function A := node 1 [(B,1)] *)
(* with B := node 2 [(A,1)]. *)

Definition id (x:Node) : nat := match x with (node n _) => n end.
Definition edges (x:Node) := match x with (node _ ys) => ys end.
Definition children (x:Node) := map (@fst Node nat) (edges x).
Definition beq_node (x:Node) (y:Node) : bool := beq_nat (id x) (id y).
Definition elem_node := @elem Node beq_node.
Eval simpl in node (id A) (edges A). (* == A *)
Eval compute in children A.


(* --------------------------------------------------- *)


Definition elem_edge := @elem (Node*nat) (fun xw yv =>
let (x,w):=xw in let (y,v):=yv in beq_node x y && beq_nat w v).

Definition child (y:Node) (x:Node) : bool := elem_node y (children x).
Eval compute in child B A.

(* reflexive transitive closure of child *)
Inductive path : Node -> Node -> Type :=
| r_path : forall x:Node, path x x
| d_path : forall (x:Node) (y:Node), child y x = true -> path x y
| t_path : forall (x:Node) (y:Node) (z:Node),
 path x y -> path y z -> path x y
.

Definition consistent {x:Node} (h :Node->nat) := forall y wxy,
elem_edge (y,wxy) (edges x) = true -> h x <= wxy + h y = true.

Function h (x:Node) : nat := (*let (n, _) := G in*)
match id x with
 | 1 => 2
 | 2 => 2
 | 3 => 1
 | 4 => 1
 | 5 => 0
 | 6 => 0
 | _ => 0
end.

Function goal (x:Node) : bool := id x == 5.

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
Inductive astar 
{start:Node} {h:Node->nat} {goal:Node->bool}
: Node -> list (Node*nat*nat) -> Nodes -> Nodes
-> Type :=

(* base case *)
| init : astar start [(start, 0, h start)] [] []

(* nullop recursion*)
| skip : forall x y gy hy open closed goals,
 elem_node y closed = true
 -> astar x ((y, gy, hy)::open) closed goals
 -> astar y open closed goals

(* default recursion *)
| pop : forall x y gy hy open closed goals,
 goal y = false
 -> astar x ((y, gy, hy)::open) closed goals
 -> astar y (puts gy h (edges y) open) (y::closed) goals

(* output recursion *)
| yield : forall x y gy hy open closed goals,
 goal y = true
 -> astar x ((y, gy, hy)::open) closed goals
 -> astar y (puts gy h (edges y) open) (y::closed) (y::goals)

.

Check astar_rect.
Check astar_ind.
Check astar_rec.


(* --------------------------------------------------- *)

(* easier *)
(* init : [] *)
(* yield : [] => [y] *)
(* init => ... => yield *)
Theorem astar_is_sound :
forall start h goal x open closed goals y,
@astar start h goal x open closed (y::goals) -> goal y = true.

Proof. 
intros start h goal x open closed goals y. intro A.
remember open. remember closed. remember (y::goals).
generalize dependent open.
generalize dependent closed.
generalize dependent goals.

induction A.
Case "init". intros. inversion Heql0.
Case "skip". intros. eapply IHA; eauto. (* induction puts the thing i want (goal y = true) in the induction hypothesis. how does coq do this? that assumption only in yield *)
Case "pop". intros. eapply IHA; eauto.
Case "yield". intros. inversion Heql0. subst. assumption.
Qed.

