
Require Import ssreflect ssrbool.


Lemma negb_invol : forall b, negb (negb b) = b.
case.
  simpl.
  reflexivity.
reflexivity.
Qed.

Fixpoint evenb n :=
  match n with
| 0 => true
| S n => negb (evenb n)
  end.

Inductive even : nat -> Prop :=
| even0 : even 0
| evenS : forall n, even n -> even (S (S n)).

Lemma e1 : forall n, even n -> evenb n.
  move => n e.
  induction e.
    done.
  simpl.
  rewrite negb_invol.
  assumption.
Qed.

Definition pred n :=
  match n with
  | S m => m
  | 0 => 0
  end.

Lemma evenb_even_aux :
  forall n,
    (evenb n -> even n)
    /\(evenb (pred n) -> even (pred n)).
  elim => [ | [|n] [hn1 hn2]]; simpl.
(* two remarks :
   - we do [| n] instead of n, that is we have three cases :
     0, (S 0), (S (S n))
   - I write [hn1 hn2] that is I immediately cut the induction hypothesis hn1/\h
n2 in two (hn1 and hn2)  *)

(* when n = 0 both cases are solved by even_0 *)
  - split; move => e; apply even0.
    
(* n = 1 is quite easy *)
- split.
    done.
  move => e; apply even0.

(* the case (S (S n)) *)
- split.
    rewrite negb_invol.
    move => h.
    apply evenS.
    simpl in hn2.
    apply hn2.
    assumption.

  move => h.
  apply hn1.
  simpl.
  assumption.
Qed.

(* the lemma is just a corolary *)
Lemma evenb_even : forall n, evenb n -> even n.
Proof.
move => n e.
move: (evenb_even_aux n) => [h1 h2].
by apply h1.
Qed.

Definition evenl n := exists p, n = p + p.

Lemma addnS : forall n m, n + S m = S (n+m).
elim => [//=|n hn] m /=.
by rewrite hn.
Qed.

Lemma even_l : forall n, even n -> evenb n.
Proof.
move => n h.
induction h.
  trivial.
simpl.
rewrite negb_invol.
assumption.
Qed.

Lemma even_half :
  forall n, even n -> evenl n.
Proof.
move => n h.
induction h.
  by exists 0.
move: IHh => [p hp].
exists (S p).
by rewrite /= addnS hp.
 (* the /= just inserts a "simpl" in the
    rewrite sequence *)
Qed.

