(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* --------------- *) Import Monoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set   Printing Projections.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Notation "[ 'seq' E | i < n ]" := (mkseq (fun i => E) n)
  (at level 0, E at level 99, i name,
   format "[ 'seq'  E  |  i  <  n ]") : seq_scope.

(* ==================================================================== *)
Lemma mkseqS {T : Type} (f : nat -> T) (n : nat) :
  [seq f i | i < n.+1] = rcons [seq f i | i < n] (f n).
Proof.
by rewrite /mkseq -addn1 iotaD map_cat /= add0n cats1.
Qed.

(* ==================================================================== *)
(* Some extras arithmetic lemmas that are needed later                  *)
Lemma sum_pow2 (n : nat) :
  \sum_(i < n) 2^i = (2^n).-1.
Proof.
elim: n => [|n ih]; first by rewrite big_ord0.
rewrite big_ord_recr //= ih [LHS]addnC -subn1.
rewrite addnBA ?expn_gt0 // subn1; congr _.-1.
by rewrite addnn -mul2n -expnS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma modn2_neq0 (n : nat) : (n %% 2 != 0) = n %% 2 :> nat.
Proof. by rewrite modn2 eqb0 negbK. Qed.

(* -------------------------------------------------------------------- *)
Lemma divnE (n : nat) (p : nat) (k : nat) :
  p != 0 -> k * p <= n < k.+1 * p -> n %/ p = k.
Proof.
move=> nz_p; elim: k n => [|k ih] n.
- by rewrite !simpm => lt; rewrite divn_small.
rewrite [X in X <= _]mulSn [X in _ < X]mulSn => rg; have le_pn: p <= n.
- by case/andP: rg => [+ _] => /(leq_trans _); apply; apply/leq_addr.
move: rg; rewrite -leq_subRL // -ltn_subLR //.
move/ih => <-; rewrite -{1}[n](subnK le_pn) divnDr //.
by rewrite divnn lt0n nz_p addn1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma divn_sumr {I : Type} (P : pred I) (F : I -> nat) (r : seq I) (d : nat) :
  (forall i, P i -> d %| F i) ->
    (\sum_(i <- r | P i) F i) %/ d = \sum_(i <- r | P i) (F i) %/ d.
Proof.
move=> hdvd; elim/big_rec2: _ => //=; first by rewrite div0n.
by move=> i _ n Pi <-; rewrite divnDl ?hdvd.
Qed.

(* ==================================================================== *)
(* We define the discrete logarithm in base 2.                          *)
(*                                                                      *)
(*   - log2(n) = the number of bits needed to represent all `n`         *)
(*               differents values or the range [0..n[                  *)

Definition log2 (n : nat) := trunc_log 2 n.

Lemma log2_0 : log2 0 = 0.
Proof. exact: trunc_log0. Qed.

Lemma log2_1 : log2 1 = 0.
Proof. exact: trunc_log1. Qed.

Lemma log2_expnK n : log2 (2 ^ n) = n.
Proof. exact: trunc_expnK. Qed.

Lemma log2_eq n k : 2 ^ n <= k < 2 ^ n.+1 -> log2 k = n.
Proof. exact: trunc_log_eq. Qed.

Lemma log2_homo : {homo log2 : m n / m <= n}.
Proof. exact: leq_trunc_log. Qed.

Lemma log2_double (n : nat) : 0 < n -> log2 n.*2 = (log2 n).+1.
Proof. exact: trunc_log2_double. Qed.

Lemma log2S (n : nat) : 1 < n -> log2 n = (log2 n./2).+1.
Proof. exact: trunc_log2S. Qed.

Lemma log2_eq0 (n : nat) : (log2 n == 0) = (n < 2).
Proof. by rewrite trunc_log_eq0 /= ltnS. Qed.

Lemma log2_lt2 (n : nat) : n < 2 -> log2 n = 0.
Proof. by rewrite -log2_eq0 => /eqP. Qed.

Lemma log2_ltn (n : nat) : n < 2 ^ (log2 n).+1.
Proof. exact: trunc_log_ltn. Qed.

Lemma log2_bounds (n : nat) : n != 0 -> 2 ^ (log2 n) <= n < 2 ^ (log2 n).+1.
Proof.
by move=> nz_n; apply: (@trunc_log_bounds 2 n) => //; rewrite lt0n.
Qed.

(* ==================================================================== *)
(* We provide a library for bit-vectors. A bit-vector is any sequence   *)
(* of booleans whose last element is not `false`.                       *)

Record bits := Bitseq { bitseq :> seq bool; _ : last true bitseq; }.

Canonical  bits_subType := Eval hnf in [subType for bitseq].
Definition bits_eqMixin := Eval hnf in [eqMixin of bits by <:].
Canonical  bits_eqType  := Eval hnf in EqType bits bits_eqMixin.

Lemma bits_inj : injective bitseq.
Proof. exact: val_inj. Qed.

(* -------------------------------------------------------------------- *)
(* The notation `b.[i]` allows to access the `i`-th bit of a bit-       *)
(* vector `b`. The bit-vector is implicitly padded with a infinite      *)
(* sequence of `false`.                                                 *)

Definition bit i (b : seq bool) := nosimpl (nth false b i).

Notation "b .[ i ]" := (bit i b).

Lemma bit_oversize (b : bits) (i : nat) :
  size b <= i -> b.[i] = false.
Proof. by case: b => /= b _ lti; rewrite /bit nth_default. Qed.

(* -------------------------------------------------------------------- *)
(* We now prove that for any sequence `s` of booleans, there exists a   *)
(* bit-vector `t` with the same bits (once padded with an infinite      *)
(* sequence of `false`), i.e. `t` is `s` with the final `false`         *)
(* elements trimed.                                                     *)

Lemma bits_canon_spec (s : seq bool) :
  { t : seq bool |
        forall i, nth false s i = nth false t i
      & last true t }.
Proof.
elim/last_ind: s => [|s [] ih]; first by exists [::].
- by exists (rcons s true) => //; rewrite last_rcons.
case: ih => bs h1 h2; exists bs => //.
move=> i; rewrite nth_rcons; case: ltnP => // le.
rewrite if_same; apply/esym; case: (ltnP i (size bs)); last first.
- by move=> ?; rewrite nth_default.
move/(leq_ltn_trans le) => {le} lt; absurd false => //.
move: h2; rewrite (last_nth false) -[size bs]prednK //=.
- by apply: (leq_ltn_trans _ lt).
rewrite -h1 nth_default // -ltnS prednK //.
by apply: (leq_ltn_trans _ lt).
Qed.

(* -------------------------------------------------------------------- *)
(* The function `mkbits` allows the creation of a bit-vector from a     *)
(* given sequence of booleans.                                          *)

Definition mkbits_def (s : seq bool) :=
  Bitseq (s2valP' (bits_canon_spec s)).

Fact mkbits_key : unit.
Proof. by []. Qed.

Definition mkbits := locked_with mkbits_key mkbits_def.
Canonical mkbits_unlockable := [unlockable fun mkbits].

(* -------------------------------------------------------------------- *)
Lemma mkbitsE (s : seq bool) (i : nat) : (mkbits s).[i] = s.[i].
Proof. by rewrite unlock; move: (s2valP (bits_canon_spec s) i). Qed.

(* -------------------------------------------------------------------- *)
Lemma size_mkbits_le (s : seq bool) :
  size (mkbits s) <= size s.
Proof.
rewrite leqNgt; apply/negP => lt.
have := mkbitsE s (size (mkbits s)).-1; rewrite [X in _ = X]nth_default.
- by rewrite -ltnS prednK // (leq_ltn_trans _ lt).
rewrite /bit (@set_nth_default _ _ true) ?prednK //.
- by apply: (leq_ltn_trans _ lt).
by rewrite nth_last unlock (s2valP' (bits_canon_spec s)).
Qed.

(* -------------------------------------------------------------------- *)
Lemma mkbitsK (s : seq bool) : last true s -> mkbits s = s :> seq _.
Proof.
move=> h; apply: (@eq_from_nth _ false); last first.
- by move=> i lti; apply: mkbitsE.
have := size_mkbits_le s; rewrite leq_eqVlt => /orP[/eqP //|lt].
absurd (last true s) => //; rewrite -nth_last.
rewrite (@set_nth_default _ _ false).
- by rewrite prednK // (leq_ltn_trans _ lt).
rewrite -/(bit _ _) -mkbitsE /bit nth_default //.
by rewrite -ltnS prednK // (leq_ltn_trans _ lt).
Qed.

(* -------------------------------------------------------------------- *)
(* Two bit-vectors are equal (i.e. represented by the same sequence)    *)
(* iff they have the same bits (once padded with an infinite sequence   *)
(* of `false`.                                                          *)

Lemma bits_eqP (b1 b2 : bits) :
  reflect (forall i, b1.[i] = b2.[i]) (b1 == b2).
Proof.
apply: (iffP eqP) => [->//|].
case: b1 b2 => [b1 h1] [b2 h2] /= eq_bits.
apply/val_eqP/eqP => /=; apply: (@eq_from_nth _ false); last first.
- by move=> i _; apply: eq_bits.
wlog: b1 h1 b2 h2 eq_bits / (size b1 <= size b2) => [wlog|].
- case: (leqP (size b1) (size b2)); first by apply: wlog.
  by move/ltnW => le; apply/esym/wlog.
rewrite leq_eqVlt => /orP[/eqP //|lt_sz].
absurd false => //; move/(_ (size b2).-1): eq_bits.
rewrite [X in _ = X]/bit (set_nth_default true).
- by rewrite ltn_predL (leq_ltn_trans _ lt_sz).
rewrite nth_last h2 -/(is_true _) /bit nth_default //.
by rewrite -ltnS prednK // (leq_ltn_trans _ lt_sz).
Qed.

Lemma bits_eqW (b1 b2 : bits) :
  (forall i, b1.[i] = b2.[i]) <-> (b1 = b2).
Proof. by rewrite (rwP eqP); split=> /bits_eqP. Qed.

(* -------------------------------------------------------------------- *)
(* The empty bit-vector and some related lemmas.                        *)

Definition bits0 := mkbits [::].

Notation "0%:B" := bits0 (at level 0).

Lemma b0E (i : nat) : 0%:B.[i] = false.
Proof. by rewrite mkbitsE /bit nth_nil. Qed.

Lemma val_b0E : val 0%:B = [::].
Proof. by rewrite /mkbits /= mkbitsK. Qed.

Lemma size_b0 : size 0%:B = 0.
Proof. by rewrite val_b0E. Qed.

(* -------------------------------------------------------------------- *)
Lemma size_bits_eq0P (b : bits) :
  (size b == 0) = (b == 0%:B).
Proof. by rewrite -val_eqE /= val_b0E size_eq0. Qed.

(* -------------------------------------------------------------------- *)
Lemma bits_neq0P (b : bits) :
  reflect (exists i, b.[i]) (b != 0%:B).
Proof.
apply: (iffP idP); last first.
- by case=> i nz_bi; apply/contraL: nz_bi => /eqP->; rewrite b0E.
case: b => b hb /=; rewrite -size_bits_eq0P /= => nz_szb.
move: hb; rewrite (last_nth false) -[size b]prednK ?lt0n //=.
by move: _.-1 => i h; exists i.
Qed.

(* -------------------------------------------------------------------- *)
Lemma bits_neq0W (b : bits) : (exists i, b.[i]) <-> (b <> 0%:B).
Proof. by split=> [|/eqP] /bits_neq0P => // /eqP. Qed.

(* -------------------------------------------------------------------- *)
Lemma hibit_neq0P (b : bits) : (b != 0%:B) = b.[(size b).-1].
Proof.
rewrite -size_bits_eq0P; case: b => /= b hb.
by rewrite /bit nth_last; case: b hb.
Qed.

(* -------------------------------------------------------------------- *)
Lemma hibit_neq0W (b : bits) : (b <> 0%:B) <-> b.[(size b).-1].
Proof. by rewrite -hibit_neq0P; split=> /eqP. Qed.

(* -------------------------------------------------------------------- *)
(* The bitwise xor (eXclusive OR) of two bit-vectors                    *)

Definition bxor (b1 b2 : bits) : bits :=
  mkbits [seq b1.[i] (+) b2.[i] | i < maxn (size b1) (size b2)].

Lemma bxorE (b1 b2 : bits) (i : nat) :
  (bxor b1 b2).[i] = b1.[i] (+) b2.[i].
Proof.
rewrite mkbitsE /=; case: (ltnP i (maxn (size b1) (size b2))) => [lt|ge].
- by rewrite /bit nth_mkseq.
rewrite /bit !nth_default ?size_mkseq //;
  by move: ge; rewrite geq_max => /andP[].
Qed.

(* -------------------------------------------------------------------- *)
(* We prove that the set of bitvectors, with 0%:B and (.+), forms a     *)
(* commutative monoid.                                                  *)

Lemma bxor0b : left_id 0%:B bxor.
Proof.
by move=> b; apply/eqP/bits_eqP => i; rewrite !(bxorE, b0E) addFb.
Qed.

Lemma bxorC : commutative bxor.
Proof.
by move=> b1 b2; apply/eqP/bits_eqP => i; rewrite !bxorE addbC.
Qed.

Lemma bxorA : associative bxor.
Proof.
by move=> b1 b2 b3; apply/eqP/bits_eqP => i; rewrite !bxorE addbA.
Qed.

Lemma bxorb0 : right_id 0%:B bxor.
Proof. by move=> b; rewrite bxorC bxor0b. Qed.

Lemma bxorbb : self_inverse 0%:B bxor.
Proof.
by  move=> b; apply/eqP/bits_eqP => i; rewrite bxorE b0E addbb.
Qed.

Notation "b1 .+ b2" := (bxor b1 b2) (at level 50, left associativity).

Canonical bxor_monoid := Monoid.Law bxorA bxor0b bxorb0.
Canonical bxor_comoid := Monoid.ComLaw bxorC.

(* -------------------------------------------------------------------- *)
Lemma bigxorE {I : Type} (P : pred I) (F : I -> bits) (r : seq I) (i : nat) :
    (\big[bxor/0%:B]_(x <- r | P x) F x).[i]
  = \big[addb/false]_(x <- r | P x) (F x).[i].
Proof.
elim/big_ind2: _ => //; first by rewrite b0E.
by move=> _ bs _ cs <- <-; rewrite bxorE.
Qed.

(* ==================================================================== *)
(* We now define functions from converting from bit-vectors to natural  *)
(* numbers, following the 1-complement convention.                      *)
(*                                                                      *)
(* We prove that b2n / n2b are the inverse of each other, along with    *)
(* some more basic properties.                                          *)

Definition b2n (b : bits) : nat :=
  \sum_(i < size b) 2^i * b.[i].

Definition n2b (n : nat) : bits :=
  mkbits [seq (n %/ (2 ^ i)) %% 2 != 0 | i < (log2 n).+1].

(* -------------------------------------------------------------------- *)
Lemma b2nWE (n : nat) (b : bits) :
  size b <= n -> b2n b = \sum_(i < n) 2^i * b.[i].
Proof.
pose F i := 2^i * b.[i]; move=> le; rewrite /b2n.
rewrite (big_ord_widen n F) // big_mkcond /=.
apply: eq_bigr; case=> /= i lti _; rewrite {}/F.
by case: ltnP => // gei; rewrite /bit nth_default ?simpm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma n2b0 : n2b 0 = 0%:B.
Proof. 
apply/eqP/bits_eqP => i; rewrite b0E /n2b mkbitsE.
rewrite log2_0 -(@eq_mkseq _ (fun=> false)) //.
- by move=> j /=; rewrite div0n mod0n eqxx.
case: (ltnP i 1) => ?; first by rewrite /bit nth_mkseq.
by rewrite /bit nth_default.
Qed.

(* -------------------------------------------------------------------- *)
Lemma n2bE (n : nat) (i : nat) :
  (n2b n).[i] = ((n %/ 2 ^ i) %% 2 != 0).
Proof.
case: (n =P 0) => [->|/eqP nz_n].
- by rewrite n2b0 b0E div0n mod0n eqxx.
rewrite mkbitsE; case: (ltnP i (log2 n).+1) => [lt|ge].
- by rewrite /bit nth_mkseq.
rewrite /bit nth_default ?size_mkseq //.
apply/esym/negbTE; rewrite negbK divn_small //.
have /andP [_ +] := log2_bounds nz_n.
by move/leq_trans; apply; apply: leq_pexp2l.
Qed.

(* -------------------------------------------------------------------- *)
Lemma size_n2b (i : nat) : i != 0 -> size (n2b i) = (log2 i).+1.
Proof.
move=> nz_i; set d := (log2 i).+1.
suff nz: (n2b i).[d.-1].
- apply/eqP; rewrite /n2b; set s := (X in mkbits X).
  have := size_mkbits_le s; rewrite size_mkseq -/d.  
  rewrite leq_eqVlt => /orP[//|lt]. absurd (n2b i).[d.-1] => //.
  by rewrite bit_oversize.
have := log2_bounds nz_i; rewrite n2bE /d /=.
rewrite -[X in X <= _]mul1n expnS => /divnE -> //.
by rewrite -lt0n expn_gt0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma size_n2b_half (i : nat) :
  size (n2b i./2) = (size (n2b i)).-1.
Proof.
case: i => /= [|i]; first by rewrite n2b0 /= size_b0.
case: i => /= [|i].
- by rewrite n2b0 size_b0 /n2b log2_1 mkbitsK.
by rewrite !size_n2b //= [in RHS]log2S.
Qed.

(* -------------------------------------------------------------------- *)
Lemma b2nE (b : bits) (i : nat) :
  ((b2n b) %/ 2 ^ i) %% 2 = b.[i].
Proof.
pose F (i : nat) := 2 ^ i * b.[i]; rewrite /b2n.
have dvdF (j : nat) : i <= j -> 2 ^ i %| F j.
- by move=> le_ij; rewrite dvdn_mulr // dvdn_exp2l.
case: (ltnP i (size b)) => [lti|gei]; last first.
- rewrite bit_oversize //= divn_small ?mod0n //.
  apply: (@leq_ltn_trans (\sum_(j < size b) 2 ^ j)).
  - apply: leq_sum; case=> /= j ltj _.
    by case: b.[_]; rewrite simpm.
  by rewrite sum_pow2 prednK ?expn_gt0 // leq_pexp2l.
rewrite -(big_mkord xpredT F) (big_cat_nat _ (n := i.+1)) //=.
rewrite divnDr; first rewrite big_nat dvdn_sum //.
- by move=> j /andP[/ltnW + _]; apply: dvdF.
rewrite -[X in (_ + X)](@divnK 2); last rewrite addnC modnMDl.
- rewrite big_nat divn_sumr.
  - by move=> j /andP[/ltnW + _]; apply: dvdF.
  rewrite dvdn_sum // => j /andP[/[dup] lt_ik / ltnW le_ij _].
  rewrite /F mulnC -muln_divA ?dvdn_exp2l //.
  by rewrite dvdn_mull // -expnB // dvdn_exp // subn_gt0.
rewrite big_nat_recr //= divnDr ?dvdn_mulr //.
rewrite mulKn ?expn_gt0 // [X in X+_](_ : _ = 0); last first.
- by rewrite add0n modn_small // ltnS leq_b1.
rewrite divn_small // (@leq_ltn_trans (\sum_(j < i) 2 ^ j)) //.
- rewrite big_mkord; apply: leq_sum => /= -[/= k ltk] _.
  apply/(@leq_trans (2 ^ k))/leq_pexp2l => //.
  by rewrite /F; case: b.[k]; rewrite simpm.
- by rewrite sum_pow2 ltn_predL expn_gt0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma b2nK : cancel b2n n2b.
Proof.
by move=> b; apply/eqP/bits_eqP => i; rewrite n2bE b2nE eqb0 negbK.
Qed.

(* -------------------------------------------------------------------- *)
Lemma n2bK : cancel n2b b2n.
Proof.
suff: forall l, forall i, log2 i = l -> b2n (n2b i) = i.
- by move=> ih i; apply: (ih (log2 i)).
elim=> [|l ih] i logiE.
- rewrite /n2b logiE mkseqS /= expn0 divn1.
  rewrite (b2nWE (size_mkbits_le _)) /=.
  rewrite big_ord_recl /= big_ord0 addn0.
  rewrite expn0 mul1n mkbitsE /bit /= modn2_neq0.
  by rewrite modn_small // -log2_eq0; apply/eqP.
have gt1_n: 1 < i by rewrite ltnNge -ltnS -log2_eq0 logiE.
pose F i k := 2 ^ k * (n2b i).[k].
have gt0_size: 0 < size (n2b i).
- by rewrite lt0n size_n2b //; case: {+}i gt1_n.
rewrite /b2n -(big_mkord predT (F i)) /= -[size _]prednK //.
rewrite big_nat_recl //= {1}/F expn0 mul1n.
rewrite -(eq_big_nat _ _ (F1 := fun j => (F i./2 j) * 2)).
- move=> k rg_k; rewrite /F n2bE modn2_neq0.
  rewrite mulnAC -expnSr; congr (_ * _).
  by rewrite n2bE modn2_neq0 -divn2 -divnMA -expnS.
rewrite -big_distrl /= -size_n2b_half big_mkord -/(b2n _) ih.
- by rewrite log2S // in logiE; case: logiE.
rewrite n2bE expn0 divn1 modn2_neq0.
by rewrite addnC -divn2; apply/esym/divn_eq.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lt_n2b (b1 b2 : bits) :
  (exists2 k,
      (forall i, k < i -> b1.[i] = b2.[i])
    & b1.[k] < b2.[k])
  -> b2n b1 < b2n b2.
Proof.
case=> k eq lt; pose s := maxn (size b1) (size b2).
rewrite !(@b2nWE s) /=; try by rewrite leq_max leqnn simpm.
pose g (b : bits) (i : nat) := 2^i * b.[i].
have [z_b1k nz_b2k] : (~~ b1.[k]) /\ b2.[k].
- by case: b1.[k] b2.[k] lt => [] [].
rewrite -(big_mkord predT (g b1)) -(big_mkord predT (g b2)) /=.
have lek: k < s.
- apply/(@leq_trans (size b2))/leq_maxr.
  apply/contraLR: lt; rewrite -!(leqNgt, ltnNge).
  by move/bit_oversize => ->.
rewrite [X in X<_](big_cat_nat _ (n := k.+1)) //=.
rewrite [X in _<X](big_cat_nat _ (n := k.+1)) //=.
rewrite -!addSn; apply: leq_add; last first.
- rewrite leq_eqVlt -(rwP orP) /g; left; apply/eqP.
  by apply/eq_big_nat => i /andP[+ _] => /eq ->.
rewrite !big_nat_recr //= {2 4}/g.
rewrite (negbTE z_b1k) nz_b2k ?simpm.
apply: (@leq_trans (2 ^ k)); last by apply: leq_addl.
apply: (@leq_ltn_trans (\sum_(0 <= i < k) 2 ^ i)).
- apply: leq_sum => i _; rewrite {}/g.
  by case: b1.[i]; rewrite ?simpm.
suff ->: \sum_(0 <= i < k) 2 ^ i = (2 ^ k).-1.
- by rewrite prednK // expn_gt0.
- by rewrite big_mkord; apply/sum_pow2.
Qed.

(* ==================================================================== *)
Module Nim.
Context (p : nat).

(* A Nim game is composed of `p` rows of matches. We represents this    *)
(* as a function from [s : 'I_p -> nat] where [s i] denotes the number  *)
(* of matches in the row [i].                                           *)

Definition state := 'I_p -> nat.

(* At each turn, the running player must select a row and remove at     *)
(* least 1 match from this row. We here denote a binary relation [R]    *)
(* over states s.t. [s1 R_i s2] iff it is possible to move from [s1] to *)
(* [s2] in one turn on row [i].*)

Definition rows (s : state) : list nat :=
  [seq s i | i <- enum 'I_p].

Lemma size_rows (s : state) :
  size (rows s) = p.
Proof. Admitted.

Lemma nth_rows (x0 : nat) (i : 'I_p) (s : state) :
  nth x0 (rows s) i = s i.
Proof. Admitted.

Variant R (i : 'I_p) (s1 s2 : state) : Prop :=
| Turn of (s2 i < s1 i) & (forall j : 'I_p, j != i -> s2 j = s1 j).

(* -------------------------------------------------------------------- *)
(* The weight a of Nim state is obtained by xor'ing the number of       *)
(* matches (in 1-complement) for all the game rows.                     *)

Fixpoint weight_r (s : seq nat) : bits :=
  match s with
  | nil => 0%:B
  | cons n tl => ( bxor (n2b n) (weight_r tl))
  end.

Definition weight (s : state) : bits :=
  (weight_r (rows s)).

(* -------------------------------------------------------------------- *)
(* The empty game board has a weight of 0                               *)

Lemma weight_empty : weight (fun=> 0) = 0%:B.
Proof.
unfold weight.
unfold rows.
elim: (enum 'I_p) => /=.
reflexivity.
move => ip seq eq.
rewrite eq.
Search (n2b 0).
rewrite n2b0.
apply bxor0b.
Qed.


(* -------------------------------------------------------------------- *)
(* We can describe how the weight evolves after one turn                *)

Lemma turn_weight (i : 'I_p) (s1 s2 : state) (g : R i s1 s2) :
  weight s2 = weight s1 .+ n2b (s1 i) .+ n2b (s2 i).
Proof.

Admitted.

(* -------------------------------------------------------------------- *)
(* Any move from a 0-weighted game leads to a non 0-weighted game       *)

Lemma z2nz (i : 'I_p) (s1 s2 : state) :
  R i s1 s2 -> weight s1 = 0%:B -> weight s2 <> 0%:B.
Proof.
Admitted.

(* -------------------------------------------------------------------- *)
(* From any non 0-weight game, it is possible to move to a              *)
(* 0-weighted game.                                                     *)

Lemma nz2z (s : state) : weight s <> 0%:B ->
  exists (i : 'I_p), exists (s' : state), weight s' = 0%:B /\ R i s s'.
Proof.
Admitted.
End Nim.
