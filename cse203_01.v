(* ====================================================================
 * We start by loading a few libraries and declaring some
 * propositional variables.
 * ==================================================================== *)

Require Import ssreflect.

Parameter A B C D : Prop.

(* ====================================================================
 * Introducing the "move" tactic
 * ==================================================================== *)

(* `move` allows giving a name to the first (top) assumption of
 * the current goal. For example: *)

Lemma move_ex : A -> B -> A.
Proof.
(* Introduce the assumptions `A` & `B` with respective names
 * `hA` and `hB`. *)
move=> hA hB.
assumption.
Qed.

(* ====================================================================
 * Introducing the "assumption" tactic
 * ==================================================================== *)

(* `assumption` closes a goal when it can be discharged from an
 * assumption. For example: *)

Lemma assumption_ex : A -> B -> A.
Proof.
(* Introduce the assumptions `A` & `B` with respective
 * names `hA` and `hB`. *)
move=> hA hB.
(* The goal can be solved by `hA` *)
assumption.
Qed.

(* It is also possible to close the goal by explicitly giving the name
 * of the assumption, using `apply`: *)

Lemma apply_ex : A -> B -> A.
Proof.
(* Introduce the assumptions `A` & `B` with respective names
 * `hA` and `hB`. *)
move=> hA hB.
(* The goal can be solved by `hA` *)
apply hA.
Qed.

(* ====================================================================
 * Some basic propositional reasonning
 * ==================================================================== *)

Lemma ex0 : A -> A.
Proof.
move=>a.
apply a.
Qed.


Lemma ex1 : forall A : Prop, A -> A.
Proof.
move=>a.
move=>a0.
apply a0.
Qed.
  
Lemma ex2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
move=>ab.
move=>bc.
move=>a.
apply bc.
apply ab.
apply a.
Qed.

Lemma ex3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.
move=>abc.
move=>ba.
move=>b.
apply abc.
apply ba.
apply b.
apply b.
Qed.

(* ====================================================================
 * With conjunctions
 * ==================================================================== *)

(* examples *)

Lemma demo_conj1 : (A /\ B) -> A.
Proof.
move=> h. case: h => [a b]. exact a.
Qed.

Lemma demo_conj2 : A -> B -> A /\ B.
Proof.
move=> a b; split.
+ trivial.
+ trivial.
Qed.

(* your turn *)

Lemma conj_ex1: A /\ B <-> B /\ A.
Proof.
split.
case.
move=> a b.
(*move=> [a b].*)
split.
apply b.
apply a.
move=>ba.
split.
apply ba.
apply ba.
Qed.

(* ====================================================================
 * With disjunctions
 * ==================================================================== *)

(* examples *)

Lemma demo_disj1 : A -> A \/ B.
Proof.
move=> a. left. trivial.
Qed.

Lemma demo_disj2 : B -> A \/ B.
Proof.
move=> a. right. trivial.
Qed.

Lemma demo_disj3 : A \/ B -> C.
move=> h. case: h => [a | b].    (* gives two subgoals *)
Abort.

(* Your turn *)

Lemma disj_ex1 :  A \/ B <-> B \/ A.
Proof.
split.
+move=>aub.
case: aub => [a | b].
right.
apply a.
left.
apply b.
+move=> bua.
case: bua => [b | a].
right.
apply b.
left.
apply a.
Qed.

Lemma disj_ex2 : A /\ B -> A \/ B.
Proof.
move=>ab.
right.
case : ab => [b].
trivial.
Qed.

(* ====================================================================
 * For negations
 * ==================================================================== *)

Print not.  (* not A (or ~A) is a shorthand for (A -> False) *)

(* examples *)

Lemma demo_not1 : False -> A.
Proof.
(* We can prove any goal from False *)
move=> h. case: h.
Qed.

(* Your turn *)

Lemma not_ex1 : A -> ~(~A).
Proof.
move=>a.
move=>a1.
apply a1.
apply a.
Qed.

Lemma not_ex2 :  (A -> B) -> ~B -> ~A.
Proof.
move=>ab.
move=>nb.
move=>n.
apply nb.
apply ab.
apply n.
Qed.

Lemma not_ex3 : ~ ~(A \/ ~A).
Proof.
move=>n.
apply n.
right.
move=>f.
apply n.
left.
apply f.
Qed.



Lemma not_ex4 :  (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
split.
+
move=>aubnc.
case: aubnc=>[aub c].
case: aub=>[a | b].
left.
split.
apply a.
apply c.
right.
split.
apply b.
apply c.
+
move=>ancubnc.
case: ancubnc=> [anc | bnc].
case: anc=> [a c].
split.
left.
apply a.
apply c.
split.
case: bnc=> [b c].
right.
apply b.
case: bnc => [b c].
apply c.
Qed.


Lemma not_ex5 : (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof. 
split.
+
move=>anbuc.
split.
case: anbuc=>[anb  | c].
case: anb=>[a b].
left.
apply a.
right.
apply c.
case: anbuc=>[anb  | c].
case: anb => [a b].
left.
apply b.
right.
apply c.
+
move=>h.
case: h=>[auc buc].
case: auc => [a | c].
case: buc => [ b|c].
left.
split.
apply a.
apply b.
right.
apply c.
case: buc=> [b | c2].
right.
apply c.
right.
apply c2.
Qed.