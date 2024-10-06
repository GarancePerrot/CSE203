(* -------------------------------------------------------------------- *)
Require Import ssreflect.

(* Predicates                                                           *)
(* ==================================================================== *)

Lemma p1 (P : nat -> Prop) (n : nat) : P n ->  P n.
Proof. 
move=>pn.
exact pn.
Qed.


(* Quantifiers                                                          *)
(* ==================================================================== *)

Parameter P : nat -> Prop.
Parameter Q : nat -> Prop.

Axiom PQ : forall n, P n -> Q n.

Lemma q1 : (P 3) -> exists x, Q x.
Proof.
move=>p3.
exists 3.
apply PQ.
exact p3.
Qed.

Lemma q1' : (exists x, P x) -> exists x, Q x.
Proof. 
move => h1.
case :h1 => [t pt].
exists t.
apply PQ.
exact pt.
Qed.

Lemma q2 : ~(exists x, P x) -> forall x, ~P x.
Proof.
move => nh1.
move =>x.
move => nh2.
apply nh1.
exists x.
apply nh2.
Qed.

(* Here you may want to use the tactic  apply ... with ... *)
Lemma q3 : (forall x, ~P x) -> ~(exists x, P x).
Proof. 
move =>h1.
move =>h2.
case : h2 =>[a b].
apply (h1 a).
apply b.
Qed.

Lemma q4 (R : nat -> nat -> Prop) :
  (exists x, forall y, R x y) -> (forall y, exists x, R x y).
Proof. 
move => h1.
move => h2.
case : h1 => [a b].
exists a.
apply (b h2).
Qed.


(* Leibniz equality                                                     *)
(* ==================================================================== *)

Definition Leibniz (T:Type) (x : T) :=
  fun y => forall P : T->Prop, (P y) -> (P x).

Lemma Lte : forall T x y, Leibniz T x y -> x = y.
Proof. 
move => h1.
move => h2.
move =>h3.
move =>h4.
apply h4.
reflexivity.
Qed.



Lemma etL : forall T x y, x = y -> Leibniz T x y.
Proof. 
move =>h1.
move => h2.
move => h3.
move =>h4.
move =>h5.
move =>h6.
rewrite h4.
apply h6.
Qed.

(* Do the following ones without using the two previous lemmas          *)
Lemma L_sym : forall T x y, Leibniz T x y -> Leibniz T y x.
Proof. 
move =>h1.
move =>h2.
move =>h3.
move =>h4.
apply h4.
move =>h5.
move =>h6.
apply h6.
Qed.


Lemma L_trans : forall T x y z,
  Leibniz  T x y -> Leibniz T y z ->  Leibniz T x z.
Proof.
move =>h1.
move => h2.
move => h3.
move =>h4.
move =>h5.
apply h5.
move => h6.
exact h6.
Qed.

(* Using negation                                                       *)
(* ==================================================================== *)
Lemma ex_neg :forall A B : Prop, A -> ~A -> B.
Proof.
move => A B a na.

(* The following command eliminates the False in 'na' and then asks to  *)
(* prove the assumption A left of the -> in ~A                          *)
case na.

assumption.
Qed.


(* Classical reasonning                                                 *)
(* ==================================================================== *)

(* By default, in Coq, one does not have the principle that any         *)
(* proposition is either true or false (the excluded middle).  We will  *)
(* come back to the reason behind this surprising fact in later         *)
(* lessons. But it is possible to assume the excluded middle as an      *)
(* axiom.                                                               *)

(* Here we start by assuming another classical axiom                    *)
Axiom DNE : forall A : Prop, ~(~A) -> A.

(* Show this axiom entails the excluded middle:                         *)
(* Difficulty: HARD                                                     *)
Lemma excluded_middle : forall A:Prop, A \/ ~A.
Proof.
move => a.




move =>a.
move : DNE.
move => b.
left.
apply DNE.
Admitted.

Lemma cl1 : exists x, (exists y, P y) -> P x.
Proof.
(* See here how one can use the excluded_middle "lemma" by              *)
(* instantiating the universally quantified variable A                  *)
move: (excluded_middle (exists x, P x)).
move => a.
case : a => [b | c].
+
case : b => [d e].
exists d.
move => f.
apply e.
+
exists 0.
move => g.
case c.
apply g.
Qed.


(* now finish the proof                                                 *)


(* The following lemma is known as the "drinker's paradox": In any      *)
(*pub, there is one person x such that, if that person drinks, the      *)
(*everybody in the pub also drinks                                      *)

(* Formally, it is a slightly more complicated variant of the previous  *)
(* lemma.                                                               *)
(* Difficulty: HARD                                                     *)
Lemma drinker_paradox (P : nat -> Prop) :
  exists x : nat, forall y : nat, P x -> P y.
Proof. Admitted.
