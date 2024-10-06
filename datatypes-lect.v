Require Import ssreflect.

Inductive color :=
  | blue
  | red.

Definition inv (c : color) :=
  match c with
  | red => blue
  | blue => red
  end.

Eval compute in (inv (inv red)).

(* various versions *)
Lemma inv_conv : forall x, inv (inv x) = x.
move => x.
case: x.
- simpl.
  reflexivity.
- reflexivity.
Restart.
  move => x.
  case x; reflexivity.  
Restart.
move => [ | ]; reflexivity.
Qed.


  Inductive opt_nat :=
  None
| Some : nat -> opt_nat.

Definition opt_add :=
  fun (n : opt_nat) (m : opt_nat) =>
     match n, m with
     | Some a, Some b => Some (a+b)
     | _ , _ => None
     end.

Eval compute in (opt_add (Some 2)(Some 3)).

Eval compute in (opt_add (Some 2) None).

Definition pred n :=
  match n with
    O => O
  | S m => m
  end.

Eval compute in (pred (pred 6)).


Lemma pred_corr :
  forall x, S (pred x) = x \/ x = 0.
move => x.
case: x.
- simpl.
  right; reflexivity.
- move => x.
  simpl.
  left; reflexivity.
Restart.
move => [ | y].
- right; reflexivity.
- left; reflexivity.
Qed.

Fixpoint plus n m :=
  match n with
  | O => m
  | S p => S (plus p m)
  end.

Eval compute in (plus 2 2).
Eval compute in (plus (S O) (S O)).
Lemma dpd : (plus 2 2) = 4.
reflexivity.
Qed.


Lemma l1 : forall x, plus 0 x = x.
move => x.
reflexivity.
Qed.

Lemma l2 : forall x, plus x 0 = x.
  move => x.
  simpl.
  induction x.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHx.
    reflexivity.    
Qed.
