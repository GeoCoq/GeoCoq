From mathcomp Require Import ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra vector.
From mathcomp
Require Import zmodp.
From mathcomp Require Import tuple fintype bigop.
From mathcomp Require Import ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Local Notation "''[' u , v ]" := (POF_to_Tarski.dot _ _ u v) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Section Tarskinp1D.

Variable n : nat.
Variable R : realFieldType.

Lemma nth_basis i (t : (n.+2).-tuple 'rV[R]_n.+1) :
  (i < n.+2)%N -> tnth t (@inord n.+1 i) = t`_i.
Proof. by move => iP; rewrite (tnth_nth 0) inordK. Qed.

Lemma bet_cong__mid (a b c :'rV[R]_n.+1 ) :
  bet a b c -> cong b a b c -> c - b = -(a - b).
Proof.
rewrite opprB => /orP[/betEP[[<- <-]|<-|<-] HC|HB HC] //.
- by move: HC => /cong_eq' <-.
- by move: HC => /cong_identity ->.
have ab0 : '[a - b] != 0.
  by rewrite dot2_eq0 subr_eq0; move: HB; rewrite betS_neq12 => /andP[].
have s_gt0 := betS_gt0 HB; move: HC; rewrite /cong (betS_ratio HB).
set s := (1 - _) / _ in s_gt0 *.
rewrite dotZl dotZr -[b - a]opprB dot2N => /eqP E.
suff -> : s = 1 by rewrite scale1r.
have /eqP : (s * s - 1) * '[a - b] = 0 by rewrite mulrBl mul1r -mulrA -E subrr.
rewrite mulf_eq0 (negPf ab0) orbF subr_eq0 -expr2 sqrf_eq1.
by case/orP => /eqP // sN; move: s_gt0; rewrite sN; lra.
Qed.

Lemma zeromxE : 0%:M == 0 :> 'rV[R]_1.
Proof. by apply /eqP/rowP; move => i; rewrite ord1 !mxE mul0rn. Qed.

Lemma lower_dim : forall o i basis,
  ~ lower_dimP _ (@bet R n.+1) (@cong R n.+1) n.+2 o i basis.
Proof.
move => o i' basis HF; pose new_basis := map_tuple (+%R^~ (- o)) basis.
suff: free new_basis.
- move => {}HF; suff {HF} : ~~ free new_basis by rewrite HF.
  rewrite /free size_tuple ltn_eqF // ltnS.
  apply: (leq_trans (dimvS (subvf <<new_basis>>))).
  by rewrite dimvf /dim /= mul1n.
suff: (forall (i : 'I_n.+2), new_basis`_i *m (new_basis`_i)^T <> 0) /\
      (forall (i j : 'I_n.+2), i <> j -> new_basis`_i *m (new_basis`_j)^T = 0).
- move => {HF} [no_null_vec ortho]; apply /freeP => k kt0 j.
  have {kt0} : (\sum_(i < n.+2) k i *: new_basis`_i) *m (new_basis`_j)^T = 0.
  + by rewrite kt0 mul0mx.
  rewrite mulmx_suml (bigID (pred1 j)) /= big_pred1_eq big1 ?addr0.
  + move=> /eqP; rewrite -scalemxAl scaler_eq0.
    by move/eqP/negPf: (no_null_vec j) => ->; rewrite orbF; apply /eqP.
  + by move => l lP; rewrite -scalemxAl ortho ?scaler0 //; move/eqP: lP.
move: HF; rewrite /lower_dimP /orthonormal_basis; set i := tnth basis (inord 0).
move => [] HNE [] HB []; rewrite -big_andb_and -big_pairs_andb_and !big_all.
move => /allP HC1 /allP HC2.
have E l : (l < n.+2)%N -> '[basis`_l - o] = '[i' - o].
  move=> lP; have := HC1 l; rewrite mem_index_iota leq0n lP /= => /(_ isT).
  by rewrite nth_basis // /cong eq_sym => /eqP.
have Hi : cong o i' o i.
  by have := HC1 O; rewrite mem_index_iota ltn0Sn => /(_ isT).
have imid := bet_cong__mid HB Hi.
have ortho1 : '[basis`_1 - o, i' - o] = 0.
  move: (HC2 O); rewrite mem_index_iota ltn0Sn big_all => /(_ isT) /allP.
  move=> /(_ 1%N); rewrite mem_index_iota /= => /(_ isT).
  rewrite (@nth_basis 1) // /cong.
  have -> : basis`_1 - i = (basis`_1 - o) + (i' - o).
    by rewrite -[i' - o]opprK -imid opprB subrKA.
  have -> : basis`_1 - i' = (basis`_1 - o) - (i' - o) by rewrite opprB subrKA.
  by rewrite (dot2D (basis`_1 - o)) (dot2B (basis`_1 - o)) => /eqP; lra.
have ortho j k : (j < k)%N -> (k < n.+2)%N -> '[basis`_k - o, basis`_j - o] = 0.
  move=> jk kn; have jn := ltn_trans jk kn.
  move: (HC2 j); rewrite mem_index_iota leq0n jn big_all => /(_ isT) /allP.
  move=> /(_ k); rewrite mem_index_iota jk kn => /(_ isT).
  rewrite !nth_basis ?(@nth_basis 1) // /cong.
  have -> : basis`_k - basis`_j = (basis`_k - o) - (basis`_j - o).
    by rewrite opprB subrKA.
  have -> : basis`_1 - i' = (basis`_1 - o) - (i' - o) by rewrite opprB subrKA.
  rewrite (dot2B (basis`_k - o)) (dot2B (basis`_1 - o)) ortho1 !E //.
  by move=> /eqP; lra.
split => [j|j k /eqP jk_neq]; rewrite /new_basis.
- apply/eqP; rewrite quad_eq0 (nth_map 0) ?size_tuple // subr_eq0.
  apply/eqP => jP.
  have i'o : i' = o.
    by apply/eqP; rewrite -subr_eq0 -dot2_eq0 -(E j) // jP subrr dot0v.
  move: Hi; rewrite /cong i'o subrr dot0v eq_sym dot2_eq0 subr_eq0 => /eqP io.
  by move: HNE; rewrite io i'o.
rewrite !(nth_map 0) ?size_tuple // mulmx_tr; apply/eqP.
move: jk_neq; rewrite neq_ltn => /orP[jk|kj].
  by rewrite dotC (ortho _ _ jk (ltn_ord k)) zeromxE.
by rewrite (ortho _ _ kj (ltn_ord j)) zeromxE.
Qed.

Lemma upper_dim : forall o i basis,
  upper_dimP _ (@bet R n.+1) (@cong R n.+1) n.+2 o i basis.
Proof.
move => o i basis; move: (@lower_dim o i basis).
by rewrite /lower_dimP /upper_dimP /no_more_orthogonal_point.
Qed.

End Tarskinp1D.