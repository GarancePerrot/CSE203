Require Import ssreflect ssrbool Nat.

(* We start by going through material shown in the lecture and
meant to illustrate how inductively defined predicates work *)

(* example 1 : two definitions of equality over natural numbers *)

(* already pre-defined   eqb n m is pretty-printed  n =? m 
Fixpoint eqb n m :=
  match n, m with
  | 0, 0 => true
  | S n, S m => eqb n m
  | _, _ => false
  end.
*)

(* The inductively defined equality is the regular equality n = m *)

Lemma eqb_eq : forall n m, n =? m -> n = m.
Proof.
(* note the compact way to do an induction over n
   and a case analysis over m at the same time
   - three of the four soubgoals are solved by
      done (here written //=                   *)
elim => [|n hn][|m] //=.
  
move => e; rewrite (hn m).
  assumption.
reflexivity.
Qed.

Lemma eqb_refl : forall n, n =? n.
Proof.
(* here //= does simpl; assumption *)
elim => [| n hn]//=.
Qed.

Lemma eq_eqb : forall n m, n = m -> n =? m.
Proof.

move => n m ->.
apply eqb_refl.
Qed.
  
(* We can use these two results for proving the following *)
(* This lemma can be emulated by the tactic injection but
   here we prove it by hand     *)
Lemma eq_Snm_nm : forall n m, S n = S m -> n = m.
Proof.
move => n m e.
apply eqb_eq.
apply (eq_eqb _ _ e).
Qed.

(* example 2 : less or equal *)

(* 
Fixpoint leb n m := 
  match n, m with
 | 0, _ => true
 | S n, S m => leb n m
 | S _, 0 => false
 end.

Inductive le (n : nat) : nat -> Prop :=  
 | le_n : le n n 
 | le_S : forall m : nat, le n m -> le n (S m).

 *)
Lemma leb_refl : forall n, n <=? n.
Proof.
elim => [|n hn]//=.
Qed.

Lemma leb_S : forall n m, n <=? m -> n <=? S m.
Proof.
elim => [|n hn][|m]//=.
move => l; auto.  (* auto tries to apply hypotheses *)
Qed.

Lemma le_leb : forall n m, n <= m -> n <=? m.
Proof.
move => n m l.
induction l.
  apply leb_refl.
apply leb_S; auto.
Qed.

Lemma le_0 : forall n, 0 <= n.
Proof.
elim => [|n hn].
  apply le_n.
by apply le_S.
Qed.

Lemma le_SS : forall n m, n <= m -> S n <= S m.
Proof.
move => n m l.
induction l.
  apply le_n.
by apply le_S.
Qed.
    
Lemma leb_le : forall n m, n <=? m -> n <= m.
Proof.
elim => [|n hn][|m]//=.
  move => *; apply le_0.
move => l; apply le_SS.
auto.
Qed.


(* again we prove the following by going through the boolean 
   version of the lemma    *)
Lemma lep_Snm_nm : forall n m, S n <= S m -> n <= m.
Proof.
move => n m l.
apply leb_le.  
apply (le_leb _ _ l).
Qed.

(* example 3 : being even *)

Fixpoint evenb n :=
  match n with
  | O => true
  | S n => negb (evenb n)
  end.


Inductive even : nat -> Prop :=
| even_0 : even 0
| even_SS : forall n, even n -> even (S (S n)).

(* There is no possible constructor for proving even (S 0)  *)
(* Thus even 1 is false. The proof is obtained by the tactic 
   'inversion'  *)

Lemma even1 : ~even 1.
Proof.
move => e.
inversion e.
Qed.


Lemma negbK (b : bool) : ~~ ~~ b = b.
Proof.
by case: b => /=.
Qed.

(* one direction of the implication is easy *)
Lemma even_pb : forall n, even n -> evenb n.
Proof.
move => n e.
induction e.
simpl.
reflexivity.
simpl.
by case: (evenb _) IHe.
Qed.

(* The other way around is more delicate because
we need to apply the induction hypothesis to n-2
and not n-1.
This is handeld by strengthening the induction hypothesis
and using <=   *)

Lemma even_bp_aux :
  forall n,
  forall m, m <= n ->
             evenb m -> even m.
Proof.
elim => [|n hn][|[|m]]//=; try by move => *; apply even_0.
 inversion 1.
rewrite Bool.negb_involutive.
move => l e.
apply even_SS.
apply hn; trivial.
apply lep_Snm_nm.
apply le_S.
by apply lep_Snm_nm.
Qed.




(* Now the main exercise part*)


(* Here we mix some previously studied structures structure (lists) 
with an inductive definition of the permutation relation *)


(* Those first definitions are well-known to you now *)
Inductive list :=
  nil | cons : nat -> list -> list.

Fixpoint app l1 l2 :=
  match l1 with
  | nil => l2
  | cons n l => cons n (app l l2)
  end.

Fixpoint length l :=
  match l with
  | nil => 0
  | cons _ l => S (length l)
  end.

Lemma app_length : forall l1 l2,
    length (app l1 l2) = length l1 + length l2.
Proof.
elim=> [|a l1 hl1] l2.
reflexivity.
simpl.
rewrite hl1.
reflexivity.
Qed.

(* Now the new component: we can define what it means for 
   two lists to be permutations of each other, as an 
   inductive predicate *)

(* It should be clear that all the constructors correspond 
   to cases of permutations. *)
Inductive perm : list  -> list -> Prop :=
  perm_refl : forall l, perm l l
| perm_ins : forall a l1 l2, perm (cons a (app l1 l2))(app l1 (cons a l2))
| perm_trans : forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.


(* this is another previous version which wuld involve other 
   technical lemmas - I leave it here to show one has
   the choice  
Inductive perm : list -> list -> Prop :=
  perm_refl : forall l, perm l l
| perm_cons : forall a l1 l2, perm l1 l2 -> perm (cons a l1)(cons a l2)
| perm_app : forall a l,  perm  (cons a l) (app l (cons a nil))
| perm_trans : forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

 *)

(* What is less clear is whether the inductive predicate
   gives *all* the permutations *)
(* proving this will be the focus of most exercises *)

(* In case this was not loaded before *)
Lemma addnS : forall n m, n + S m = S (n + m).
Proof.
  elim => [//=|n hn] m.
by rewrite /= hn.
Qed.


  (* This lemma is an instance of an induction over a permutation proof *)
Lemma perm_length : forall l1 l2,
         perm l1 l2 -> length l1 = length l2.
Proof.
move => l1 l2 p.
induction p.
reflexivity.
simpl.

rewrite app_length.
rewrite app_length.
simpl.
rewrite addnS.
reflexivity.
rewrite IHp1.
apply IHp2.
Qed.

(* using the previous lemma you can prove this *)
(*  (no additional induction needed)   *)

Lemma helper : forall l, length nil = length l -> nil = l.
Proof.
elim => [|n l hl].
simpl.
trivial.
simpl.
discriminate.
Qed.

Lemma perm_nil : forall l, perm nil l -> l = nil.
Proof.
move => l p.
move : (perm_length nil l) => h.
apply h in p.
apply helper in p.
rewrite p.
reflexivity.
Qed.

(* These three following properties of concatenation are quite easily  proved  and are useful for later lemmas *)
Lemma app_nil : forall l, (app l nil) = l.
Proof.
elim=> [|n l hl].
simpl.
reflexivity.
simpl.
rewrite hl.
reflexivity.
Qed.

Lemma app_ass : forall l1 l2 l3, app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
elim=> [|n l1 hl1] l2 l3.
simpl.
reflexivity.
simpl.
by rewrite hl1.
Qed.

Lemma app_cons :
  forall l1 n l2,
    app l1 (cons n l2) = app (app l1 (cons n nil)) l2.
Proof.
elim=> [|n1 l1 hl1] n l2.
simpl.
reflexivity.
simpl.
rewrite hl1.
reflexivity.
Qed.




(* This is the main technical lemma about permutations *)
(* The interesting case of the induction is the second one 
    where you need to prove something like :            *)
(* perm (cons a (cons a0 (app l1 l2))) 
        (cons a (app l1 (cons a0 l2))) *)
(* one possibility is to show you have a permutation path 
   between the two lists going through 
   (cons a0 (cons a (app l1 l2)))    *)

Lemma perm_cons : forall a l1 l2,
                      perm l1 l2 -> perm (cons a l1) (cons a l2).
(*start with an induction over the permutation *)
Proof.
move => a l1 l2 p.
induction p.
apply perm_refl.
move: (perm_trans (cons a (cons a0 (app l1 l2))) (cons a0 (cons a (app l1 l2)))  (cons a (app l1 (cons a0 l2))) )=> h.
apply h.
Admitted.


(* This can then be proved by induction over l1 using 
    the previous lemma   *)
Lemma perm_comapp : forall l1 l2, perm (app l1 l2)(app l2 l1).
Proof.
elim=> [|n l hl]l2.
simpl.
rewrite app_nil.
apply perm_refl.

apply: (perm_trans _ _ _ (perm_ins _ _ _)).
apply: (perm_trans _ _ _ (hl _)).
apply: (perm_trans _ _ _ (perm_ins _ _ _)).
apply: perm_refl.
Qed.

  
(* With the previous property, we can prove permutation is
   symetric (and thus an equivalence relation). 
  The proof goes by induction over the fact (perm l1 l2)  *)
Lemma perm_sym :
  forall l1 l2,
    perm l1 l2 -> perm l2 l1.
Proof.
Admitted.





(* This lemma is easy. It is a generalization of perm_cons.  
   Building on this last remark, you may see what the 
  induction is on. *)
Lemma perm_cons_iter : forall l1 l2 l3,
    perm l2 l3 -> perm (app l1 l2)(app l1 l3).
Proof.
Admitted.

(* This lemma is just for making sure we have all permutations *)
Lemma perm_swap : forall l1 l2 n m,
    perm (app l1 (cons n (cons m l2)))(app l1 (cons m (cons n l2))).
Proof.
Admitted.

 
(* We now have enough properties to show that insertion 
  sort preserves this notion of permutations. *)
Require Import Nat.

Fixpoint insert n l :=
  match l with
  | nil => cons n nil
  | cons m l' =>
    if n <=? m then cons n l
    else cons m (insert n l')
  end.

Lemma insert_perm : forall n l, perm (cons n l)(insert n l).
Proof.
Admitted.

Fixpoint insertion_sort l :=
  match l with
  | nil => nil
  | cons n l => insert n (insertion_sort l)
  end.

Lemma sort_perm : forall l, perm l (insertion_sort l).
Proof.
Admitted.


