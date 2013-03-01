Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Plus.
Require Import Omega.
Import ListNotations.

Definition admit {T:Type} : T. Admitted.

(* In his book, "Godel, Escher, Bach: An Eternal Golden Braid",
   Douglas Hofstadter created the following puzzle to illustrate the
   challenges of reasoning about term-rewriting systems.  Our language
   will be the set of strings over the alphabet {M, I, U}.  We are
   given the following four rewriting rules
   1. If we have a string xI (where x is an arbitrary substring), we
     can produce xIU.  For instance, MIUIUII -> MIUIUIIU.
   2. If we have a string xIIIy, we can produce xUy. For instance,
     MMMIUIIIUI -> MMMIUUUI.
   3. If we have a string Mx, we can produce Mxx. For instance,
     MIIIUI -> MIIIUIIIIUI.
   4. If we have a string xUUy, we can produce xy.  For instance,
     IIIUUII -> IIIII.

   The challenge is to show how to turn the string MI into the string
   MU...or to show it cannot be done.  You are welcome to play with
   the rewriting rules by hand, and see what patterns you can find,
   before attempting the proofs in this exercise.
*)

(* We'll start by modeling the set of valid characters; MIU strings
   will then be lists of these characters. *) 
Inductive MIUChar : Set :=
| M : MIUChar
| I : MIUChar
| U : MIUChar.

Definition MIUString := list MIUChar.

(* Part 1: Modeling the rewriting rules.  The rules above essentially
   define a set of "valid" strings --- the ones that can be produced
   from MI by following the four rules. Give an inductive defintition
   (of type MIUString -> Prop) that encodes this validity relation.
   Hint: you'll need *five* constructors -- one for each rule, and one
   for the axiom that MI is valid.
*)

Inductive MIUValid : MIUString -> Prop :=
(* root *)
| mi : MIUValid [M;I]
(* suffix I => IU *)
| xI_xIU : forall x:MIUString,
             MIUValid (x ++ [I]) -> MIUValid (x ++ [I;U])
(* III => U *)
| xIIIy_xUy : forall x:MIUString, forall y:MIUString,
                MIUValid (x ++ [I;I;I] ++ y) -> MIUValid (x ++ [U] ++ y)
(* double suffix *)
| Mx_Mxx : forall x:MIUString,
             MIUValid ([M] ++ x) -> MIUValid ([M] ++ x ++ x)
(* kill UU *)
| xUUy_xy : forall x:MIUString, forall y:MIUString,
              MIUValid (x ++ [U;U] ++ y) -> MIUValid (x ++ y)
.


(* Part 2: Warmup: Show that the string MIIUIIU is valid.  In fact,
   prove that every valid string must start with M. 

   Reminder #1: Use the inversion tactic on hypotheses of the form 
     (H : exists l, P l) 
   to extract a specific l for which P l hold.  

   Reminder #2: When your goal is of the form (exists l, P l), Use the
   (exists aList) tactic to claim that P holds for aList.
*)
Example ex1: MIUValid [M;I;I;U;I;I;U].
Proof. 
apply (Mx_Mxx [I;I;U]). simpl.
apply (xI_xIU [M;I]). simpl.
apply (Mx_Mxx [I]). simpl.
apply mi.

Lemma MIUValid_starts_with_M : forall Ml,
 MIUValid Ml -> exists l, Ml = M :: l.
Proof. intros. induction H.

exists [I]. reflexivity.

destruct IHMIUValid as [ll A].
exists (ll++[U]). replace [I;U] with ([I]++[U]). 
rewrite app_assoc. rewrite A. reflexivity. reflexivity.

destruct IHMIUValid as [ll A].
destruct x as [|z].
 inversion A.
 inversion A. exists (x++[U]++y). reflexivity.

destruct IHMIUValid as [ll A].
inversion A. exists (ll++ll). reflexivity.

destruct IHMIUValid as [ll A].
destruct x as [|z].
 inversion A.
 inversion A. exists (x++y). reflexivity.

Qed.


(* The key to solving the puzzle is to notice that the number of Is in
   any valid string is never a multiple of 3 -- it starts at 1, it can
   double, or it can be reduced by 3.  Since MU has zero Is, there's
   just no way to get from MI to MU.
*)


Lemma filter_distributes_append :
  forall (X:Type) (f : X -> bool) (xs ys : list X),
filter f (xs ++ ys) = filter f xs ++ filter f ys.
Proof.
intros X f xs ys.
induction xs as [|x xs]. reflexivity.
simpl. rewrite IHxs.
destruct (f x); reflexivity.
Qed.

Definition isI (x:MIUChar) : bool :=
match x with | I => true | _ => false end
.

(* Part 3: Define the I_count of a MIUString *)
Definition I_count (l : MIUString) : nat :=
length (filter isI l).

(* Part 4: Helper lemmas. You will likely want to use Nat.add_mod *)
Lemma Icount_app_comm : forall l1 l2, 
I_count (l1 ++ l2) = I_count l1 + I_count l2.
Proof. intros xs ys. unfold I_count.
rewrite (filter_distributes_append MIUChar isI xs ys).
apply app_length.
Qed.


(* Part 4: Helper lemmas. You will likely want to use Nat.add_mod *)
Lemma Icount_app_3 : forall l1 l2 l3, 
I_count (l1 ++ l2 ++ l3) = I_count l1 + I_count l2 + I_count l3.
Proof. intros xs ys zs.
rewrite (Icount_app_comm xs (ys++zs)). rewrite (Icount_app_comm ys zs). apply plus_assoc.
Qed.

(* (duh, nat not int)
Lemma Icount_nonneg : forall (xs:MIUString), 0 <= I_count xs.
intros. induction xs as [|x xs].
reflexivity.
replace (x::xs) with ([x]++xs). rewrite Icount_app_comm.
induction x; simpl; omega.
reflexivity.
Qed.
*)

Lemma drop_modulo3 : forall n, (3 + n) mod 3 = n mod 3.
Proof.
intros. rewrite (Nat.add_mod 3 n 3).
replace (3 mod 3) with 0. rewrite plus_0_l. apply Nat.mod_mod.
omega. reflexivity. omega.
Qed.

SearchAbout modulo.
Lemma pos3 : 0<3. omega. Qed.

Lemma case_mod3 : forall (a:nat) (A:0<=a),  a mod 3 <> 0 -> a mod 3 = 1 \/ a mod 3 = 2.
intros.
assert (B := mod_bound_pos a 3 A pos3). clear A. destruct B as [C D]. omega.
Qed.

(* Part 5: Prove that for all valid MIUStrings, the I_count is never 0 mod 3 *)
Lemma MIUValid_Icount_mod3 : forall l, 
MIUValid l -> (I_count l mod 3 <> 0).
Proof. intros xs H. induction H.

simpl. omega.

replace (x++[I;U]) with ((x++[I]) ++ [U]). rewrite Icount_app_comm. 
replace (I_count [U]) with 0. rewrite plus_0_r. assumption.
reflexivity. rewrite<- app_assoc. reflexivity.

rewrite Icount_app_comm in *. rewrite Icount_app_comm in *.
replace (I_count [U]) with 0. rewrite plus_0_l.
replace (I_count [I;I;I]) with 3 in IHMIUValid.
rewrite plus_comm in IHMIUValid. rewrite<- plus_assoc in IHMIUValid.
rewrite drop_modulo3 in *.
rewrite plus_comm. assumption.
reflexivity. reflexivity.

rewrite Icount_app_comm in IHMIUValid. rewrite Icount_app_3 in *.
replace (I_count [M]) with 0 in *. rewrite plus_0_l in *.
rewrite Nat.add_mod. set (a := I_count x) in *.
apply case_mod3 in IHMIUValid. inversion IHMIUValid as [A1 | A2].
rewrite A1. simpl. omega.
rewrite A2. simpl. omega.
omega. omega. reflexivity.

rewrite Icount_app_3 in *. replace (I_count [U;U]) with 0 in *.
rewrite Icount_app_comm. rewrite plus_0_r in *. assumption. reflexivity.

Qed.


(* Part 6: Conclude that MU is not a valid MIUString.  This should be
   a *short* proof! *)
Theorem not_MU : ~ MIUValid [M;U].
Proof.
unfold not. intro. apply MIUValid_Icount_mod3 in H. simpl in H. omega.
Qed.

