(** * Prop: Propositions and Evidence *)

Require Import Coq.Arith.Plus.
Require Import Cases.

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions 
    ([forall x, P]).

    In this chapter we take a deeper look at the way propositions are
    expressed in Coq and at the structure of the logical evidence that
    we construct when we carry out proofs.  

    Some of the concepts in this chapter may seem a bit abstract on a
    first encounter.  We've included a _lot_ of exercises, most of
    which should be quite approachable even if you're still working on
    understanding the details of the text.  Try to work as many of
    them as you can, especially the one-starred exercises. 

*)
(* ##################################################### *)
(** * Inductively Defined Propositions *)

(** This chapter will take us on a first tour of the
    propositional (logical) side of Coq.  As a running example, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  The rules with no premises above the line are
    called _axioms_.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty) *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(* FILL IN HERE *)
(* two "minimal" proofs and infinite proofs. 3+5, 5+3, 3+5+0, ... *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  Each of the remaining lines
    embodies one of the rules for [beautiful] numbers.

    We can use Coq's tactic scripting facility to assemble proofs that
    particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the axiom [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* appply (b_sum 3 5) *)
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have axioms for both. *)
   apply b_3.
   apply b_5.
Qed.

(* ##################################################### *)
(** * Proof Objects *)

(** Look again at the formal definition of the [beautiful]
    property.  The opening keyword, [Inductive], has been used up to
    this point to declare new types of _data_, such as numbers and
    lists.  Does this interpretation also make sense for the Inductive
    definition of [beautiful]?  That is, can we view evidence of
    beauty as some kind of data structure? Yes, we can!

    The trick is to introduce an alternative pronunciation of "[:]".
    Instead of "has type," we can also say "is a proof of."  For
    example, the second line in the definition of [beautiful] declares
    that [b_0 : beautiful 0].  Instead of "[b_0] has type 
    [beautiful 0]," we can say that "[b_0] is a proof of [beautiful 0]."
    Similarly for [b_3] and [b_5]. *)

(** This pun between types and propositions (between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for") is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation.
<<
                 propositions  ~  types
                 proofs        ~  data values
>>
    Many useful insights follow from this connection.  To begin with, it
    gives us a natural interpretation of the type of [b_sum] constructor: *)

Check b_sum.
(* ===> b_sum : forall n m, 
                  beautiful n -> 
                  beautiful m -> 
                  beautiful (n+m) *)

(** This can be read "[b_sum] is a constructor that takes four
    arguments -- two numbers, [n] and [m], and two values, of types
    [beautiful n] and [beautiful m] -- and yields evidence for the
    proposition [beautiful (n+m)]." *)

(** In view of this, we might wonder whether we can write an
    expression of type [beautiful 8] by applying [b_sum] to
    appropriate arguments.  Indeed, we can: *)

Check (b_sum 3 5 b_3 b_5).
Check (b_sum 3 5).  
(* ===> beautiful (3 + 5) *)

(** The expression [b_sum 3 5 b_3 b_5] can be thought of as
    instantiating the parameterized constructor [b_sum] with the
    specific arguments [3] [5] and the corresponding proof objects for
    its premises [beautiful 3] and [beautiful 5] (Coq is smart enough
    to figure out that 3+5=8).  Alternatively, we can think of [b_sum]
    as a primitive "evidence constructor" that, when applied to two
    particular numbers, wants to be further applied to evidence that
    those two numbers are beautiful; its type, 
[[  
    forall n m, beautiful n -> beautiful m -> beautiful (n+m),
    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] in the previous chapter expressed the fact
    that the constructor [nil] can be thought of as a function from
    types to empty lists with elements of that type. *)

(** This gives us an alternative way to write the proof that [8] is
    beautiful: *)

Theorem eight_is_beautiful': beautiful 8.
Proof.
   exact (b_sum 3 5 b_3 b_5).
Qed.



(** Notice that we're using [apply] here in a new way: instead of just
    supplying the _name_ of a hypothesis or previously proved theorem
    whose type matches the current goal, we are supplying an
    _expression_ that directly builds evidence with the required
    type. *)

(* ##################################################### *)
(** ** Proof Scripts and Proof Objects *)

(** These proof objects lie at the core of how Coq operates. 

    When Coq is following a proof script, what is happening internally
    is that it is gradually constructing a proof object -- a term
    whose type is the proposition being proved.  The tactics between
    the [Proof] command and the [Qed] instruct Coq how to build up a
    term of the required type.  To see this process in action, let's
    use the [Show Proof] command to display the current state of the
    proof tree at various points in the following tactic proof. *)

Theorem eight_is_beautiful'': beautiful 8.
Proof.
   Show Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.

   Show Proof.
Qed.

(** At any given moment, Coq has constructed a term with some
    "holes" (indicated by [?1], [?2], and so on), and it knows what
    type of evidence is needed at each hole.  In the [Show Proof]
    output, lines of the form [?1 -> beautiful n] record these
    requirements.  (The [->] here has nothing to do with either
    implication or function types -- it is just an unfortunate choice
    of concrete syntax for the output!)  

    Each of the holes corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    [Theorem] command gives a name to the evidence we've built and
    stores it in the global context. *)

(** Tactic proofs are useful and convenient, but they are not
    essential: in principle, we can always construct the required
    evidence by hand.  Indeed, we don't even need the [Theorem]
    command: we can instead use [Definition] to directly give a global
    name to a piece of evidence. *)

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

(** All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)

Print eight_is_beautiful.
(* ===> eight_is_beautiful    = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'.
(* ===> eight_is_beautiful'   = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful''.
(* ===> eight_is_beautiful''  = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'''.
(* ===> eight_is_beautiful''' = b_sum 3 5 b_3 b_5 : beautiful 8 *)

(** **** Exercise: 1 star (six_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [6] is [beautiful]. *)

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply b_sum with (n:=3) (m:=3); apply b_3.
Qed.

Definition six_is_beautiful' : beautiful 6 := (b_sum 3 3 b_3 b_3).

(* Digression: In the spirit of "everything is a proof object", consider how we 
   defined the value "admit".  It has type T, for every single type T!
   That's impossible.  So we use Coq's Admitted tactic, which says,
   "I give up for now; just assume this can be proven." For instance,
   we can use Admitted to prove things that are blatantly False: *)
Theorem lie: False. Admitted.
(* We do the same thing for admit: *)
Definition admit {T: Type} : T.  Admitted.
(* If we then ask "what is the proof object for admit?", Coq responds *)
Print admit.
(* [*** [ admit : forall T : Type, T ]]
   which is its way of saying, "I don't know, but whatever it is,
   it has type forall T:Type, T."  In fact, Coq will say something 
   similar for lie: *)
Print lie.
(* [*** lie : False ], or in other words "I don't know what this 
   value is, but it has type False *)

(** [] *)

(** **** Exercise: 1 star (nine_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [9] is [beautiful]. *)

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  (* FILL IN HERE *)
apply (b_sum 3 6 b_3 six_is_beautiful).
Qed.

Definition nine_is_beautiful' : beautiful 9 := (b_sum 3 6 b_3 six_is_beautiful).
  (* FILL IN HERE *)
(** [] *)


(* ##################################################### *)
(** ** Implications and Functions *)

(** In Coq's computational universe (where we've mostly been living
    until this chapter), there are two sorts of values with arrows in
    their types: _constructors_ introduced by [Inductive]-ly defined
    data types, and _functions_.

    Similarly, in Coq's logical universe, there are two ways of giving
    evidence for an implication: constructors introduced by
    [Inductive]-ly defined propositions, and... functions!

    For example, consider this statement: *)

Theorem b_plus3: forall (n:nat) (bn:beautiful n), beautiful (3+n).
Proof.
  intros.
  apply b_sum with (n:=3) (m:=n). exact b_3. exact bn.
  Show Proof.

(* fun (n : nat) (bn : beautiful n) => b_sum 3 n b_3 bn *)
Qed.

(** What is the proof object corresponding to [b_plus3]? 

    We're looking for an expression whose _type_ is [forall n,
    beautiful n -> beautiful (3+n)] -- that is, a _function_ that
    takes two arguments (one number and a piece of evidence) and
    returns a piece of evidence!  Here it is: *)

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) := 
  fun n => fun H : beautiful n =>
    b_sum 3 n b_3 H.

Check b_plus3'.
(* ===> b_plus3' : forall n, beautiful n -> beautiful (3+n) *)

(** Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]."  Another equivalent way to write this definition is: *)

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) := 
  b_sum 3 n b_3 H.

Check b_plus3''.
(* ===> b_plus3'' : forall n, beautiful n -> beautiful (3+n) *)

(** **** Exercise: 2 stars (b_times2) *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros. simpl. apply b_sum. exact H. rewrite plus_0_r. exact H.
Qed.

Theorem b_times2': forall n, beautiful n -> beautiful (2*n).
Proof.
  intros. simpl. apply b_sum. exact H. apply b_sum. exact H. exact b_0.
Qed.

Print b_times2.
Print b_times2'.

(** **** Exercise: 3 stars, optional (b_times2') *)
(** Write a proof object corresponding to [b_times2] above *)

Definition b_times2'': forall n, beautiful n -> beautiful (2*n) :=
  (* FILL IN HERE *)
  fun (n:nat) (b_n : beautiful n) => b_sum n (n+0) b_n (b_sum n 0 b_n b_0).

(** **** Exercise: 2 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   (* FILL IN HERE *)

(* 3*n = 2*n + 1*n  <-  b_2_mult and b_sum.
 2+z * n = 2*n + z*n  <-  b_times2'' and H. *)
intros x y H. induction H.
 Case "x=0". rewrite Mult.mult_0_r. apply b_0.
 Case "x=3". (* 3*y = sum of 3s *) induction y as [|y].
  apply b_0.
  simpl. apply (b_sum 3 (y*3) b_3 IHy).
 Case "x=5". induction y as [|y].
  apply b_0.
  simpl. apply (b_sum 5 (y*5) b_5 IHy).
 Case "x=n+m". 
  rewrite Mult.mult_plus_distr_l.
  apply (b_sum (y*n) (y*m) IHbeautiful1 IHbeautiful2).
Qed.

(** [] *)

(* ####################################################### *)
(** ** Induction Over Proof Objects *)

(** Since we use the keyword [Induction] to define primitive
    propositions together with their evidence, we might wonder whether
    there are some sort of induction principles associated with these
    definitions.  Indeed there are, and in this section we'll take a
    look at how they can be used.  *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells us not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    two constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)
    
(** This gives rise to an _induction principle_ for proofs -- i.e., we
    can use the [induction] tactic that we have already seen for
    reasoning about inductively defined _data_ to reason about
    inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree) *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.
 
(* FILL IN HERE *)

----------
gorgeous 0

gorgeous n
----------
gorgeous (3+n)

gorgeous n
----------
gorgeous (5+n)

[]
*)

(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3".
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.

(* Exercise: 2 stars (recommended)
   Prove the reverse direction. *)
Theorem gorgeous_sum: forall n m, gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  (* FILL IN HERE *)
intros n m N. induction N as [|n|n].
   Case "0". intro H. apply H.
   Case "+ 3". intro H. apply (g_plus3 (n+m) (IHN H)). (* modus ponens *)
   Case "+ 5". intro H. apply (g_plus5 (n+m) (IHN H)).
Qed.

Theorem beautiful__gorgeous : forall n, 
  beautiful n -> gorgeous n.
Proof.
  (* FILL IN HERE *)
intros n H. induction H.
 Case "0". apply g_0.
 Case "3". apply (g_plus3 0 g_0).
 Case "5". apply (g_plus5 0 g_0).
 Case "n+m". apply (gorgeous_sum n m IHbeautiful1 IHbeautiful2).
Qed.



(* 
ExSet_ind :
  ∀P : ExSet → Prop,
    (∀b : bool, P (con1 b)) →
    (∀(n : nat) (e : ExSet), P e → P (con2 n e)) →
    ∀e : ExSet, P e
*)

Inductive ExSet : Type := 
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.




Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.

(*
induction : constructor (arguments ...) (Prop on arguments) ... => Prop on each constructor ...

forall t:T, P t
<-
forall C:constructor,  (forall a:argument, P a) -> (forall as:arguments, P (C as ...))

out: forall t:Tree, P t

in:
X:Type
P:Tree -> Prop
Base: x:X -> P(leaf x):Prop
Recur: l:tree X -> r:tree X -> L:P(r) -> P(node X) -> P (node X)
[dependent types]
[types. values. GAAAH]


apply tree_ind
prove base case
prove recursive case given induction hypothesis

[i thought]
tree_ind :
forall X:Type,
forall P:(tree -> Prop),
   (forall (l:tree X) (r:tree X), P l -> P r -> P (node l r))
-> forall x:X, P (leaf x)
-> forall t:tree X, P t

[it is]
tree_ind :
forall (X : Type) (P : tree X -> Prop),
   (forall x : X, P (leaf X x))
-> (forall l : tree X, P t  ->  forall r : tree X, P l  ->  P (node X l r))
-> forall t : tree X, P t

so an induction hypothesis is weaker. yes (forall a, P a -> forall b, P b -> ...) not (forall a, forall b, P a -> P b -> ...). you cant use some "b" in the proof of "P a", but it shouldnt matter here.
the first constructors come first (i thought last, because induction on some type "is like apply type_ind", and you need to prove the base case first, and apply "works backwards")
the polymorphic constructors get explicit type arguments

PS is there a way to tell coq to use "default names" for values of some type, so that it would show "l r" not "t t0"

*)

Check tree_ind.




(*
      mytype_ind :
        ∀(X : Type) (P : mytype X → Prop),
            (∀x : X, P (constr1 X x)) →
            (∀n : nat, P (constr2 X n)) →
            (∀m : mytype X, P m → 
               ∀n : nat, P (constr3 X m n)) →
            ∀m : mytype X, P m    
*)

Inductive mytype (X:Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.




(*
      foo_ind :
        ∀(X Y : Type) (P : foo X Y → Prop),
             (∀x : X, P (bar X Y x)) →
             (∀y : Y, P (baz X Y y)) →
             (∀f1 : nat → foo X Y,
               (∀n : nat, P (f1 n)) → P (quux X Y f1)) →
             ∀f2 : foo X Y, P f2     
*)

Inductive foo (X:Type) (Y:Type) : Type :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
(* | quux : (nat -> (foo X Y)) -> foo X Y. *)
| quux : (nat * (foo X Y)) -> foo X Y.
Check foo_ind.

(* so any type that depends on the inductive one generates an inductive hypothesis.
even if the inductive type is output by some function "X -> foo". 

PS but why doesnt some type constructor (like "(X, foo)" in "| C : (X, foo X Y) -> foo X Y") generate an inductive hypothesis? *)



(*
Consider the following inductively defined proposition:

Inductive p : (tree nat) → nat → Prop :=
   | c1 : ∀ n,
            p (leaf _ n) 1
   | c2 : ∀ l r n m,
            p l n → p r m → p (node _ l r) (n + m)
   | c3 : ∀ t n,
            p t n → p t (S n).
End P.

Describe, in English, the conditions under which the proposition p t n is provable.

c1 . c2 = len
shouldnt c2 have 1+n+m
maybe its |leaves|

p tree num := |leaves in treep| ≤ num

so... "p tree num" is (provably) true forall trees whose number of leaves is bounded above by num

*)





Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
| nlt_nil  : forall n, no_longer_than X nil n
| nlt_cons : forall x l n, no_longer_than X l n -> 
                     no_longer_than X (x::l) (S n)
| nlt_succ : forall l n, no_longer_than X l n -> 
                   no_longer_than X l (S n)
.

(*
no_longer_than_ind
: ∀(X : Set) (P : list X → nat → Prop),
    (∀n : nat, P [] n)
    → (∀(x : X) (xs : list X) (n : nat), no_longer_than X xs n → 
                                         P xs n → P (x::xs) (S n))
    → (∀(xs : list X) (n : nat), no_longer_than X xs n → 
                                 P xs n → P xs (S n))
    → (∀(xs : list X) (n : nat), 
         no_longer_than X xs n → P xs n)
*)

Check no_longer_than_ind.

