Require Import ssreflect.

(* Type *)
Check true.
Check 0.
Check 5.

(* functions *)

Parameter f : nat -> nat.
Check f.
Parameter g : nat -> nat -> nat.
Parameter g' : (nat -> nat) -> nat.
Check g'.
Check g.

Check (g 2). (* partial application *)
Check (g 2 3).

Parameter weirdo : nat -> bool -> nat.
Check (weirdo 5 false).

Check (g 2 (f 5)).

(* predefined addition *)
Check Nat.add.
Check (Nat.add 4 5).

(* defining a function : identity *)
Check (fun x : nat =>  x).


Definition d :=
  fun x : nat =>  x + x.
Check d.

(* a function over functions *)
Definition iter2 :=
  fun f : nat->nat =>
    fun x : nat =>  f (f x).
Check iter2.

(* Properties *)

Parameter even : nat -> Prop.
Check (even 5).

Lemma ex0 : (even 4)\/(even 5).
Abort.

Check (2 = 4).

Check  forall x : nat, x = 2.
Check  exists y : nat, y = 2.
Check forall x, x = 2.


(* quantifiers and proofs over quantifiers *)
Lemma ex1 : (forall x : nat, even x)
            ->
              (forall y : nat, even y).
  move => h.
move => z.
apply h.
Qed.

Parameter odd : nat -> Prop.



Parameter P Q : nat -> Prop.

Lemma ex11 : (forall x, P x) -> P 3.
Proof.
move => h.  
apply h.
Qed.


Lemma ex2 : (forall x, P x) ->
                   (forall y, P y).
Proof.
  move => h.
  move => z.
  apply h.
Qed.


Lemma ex3 :
  (forall x, P x -> Q x) ->
    Q 4.
move => h.
apply h.
Abort.


Lemma hh : (forall x, P x) ->
                   exists x, P x.
Proof.
move => h.
exists 97. (* we can chose any number *)
apply h.
Qed.


Lemma last : (forall y, P y -> Q y) ->
             (exists x, P x) ->
             exists x, Q x.
Proof.
  (* this is the short proof - look at the
     more explicit one below first *)
move => h1 [t pt].
exists t; apply h1; done.
Qed.

  (*
move => h1.
move => h2. 
case h2 => [t pt].
exists t.
apply h1.
done.  
Qed. *)



Parameter R : nat -> nat -> Prop.

Axiom R_trans : forall x y z, R x y ->
                              R y z ->
                              R x z.


Lemma exR : R 1 2 -> R 2 3 -> R 1 3.
move => r12 r23.
apply R_trans with 2; assumption.
Qed.




  


Lemma sym : forall (x: nat) y,
    x = y ->
    y = x.
Proof.
move => x y xy.
rewrite -xy.
reflexivity.
Qed.

Lemma refl : forall x : nat, x = x.
move => x.
reflexivity.
Qed.


Lemma trans : forall (x:nat) y z,
    x = y -> y = z -> x = z.
  move => x y z xy yz.
  rewrite xy yz. reflexivity.
  (*  rewrite -yz; exact xy. *)
Qed.

Lemma exx :
  (forall x, P x -> Q x) ->
  (forall y, Q y -> y = 5) ->
  ~P 5 ->
  forall z,  ~P z.
  move => h1 h2 h3.
  move => z.
  move => pz.
  apply h3.
  
