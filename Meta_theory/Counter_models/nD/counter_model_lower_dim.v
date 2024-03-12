Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra vector.
From mathcomp
Require Import zmodp.
From mathcomp Require Import tuple fintype bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Meta_theory.Counter_models.nD.independence.
Require Import GeoCoq.Meta_theory.Models.POF_to_Tarski.

Section Tarskinp1D.

Variable n : nat.
Variable R : realFieldType.

Lemma nth_basis i (t : (n.+2).-tuple 'rV[R]_n.+1) :
  (i < n.+2)%N -> tnth t (@inord n.+1 i) = t`_i.
Proof. by move => iP; rewrite (tnth_nth 0) inordK. Qed.

Lemma bet_cong__mid (a b c :'rV[R]_n.+1 ) :
  bet a b c -> cong b a b c -> c - b = -(a - b).
Proof.
rewrite /bet /betE; case: (a =P b) => [-> _ HC|ab_nz].
- by move: (cong_eq' HC) => ->; rewrite opprB.
case: (b =P c) => [-> _ HC|bc_nz /= HB HC].
- by move: (cong_eq HC) => ->; rewrite opprB.
move: (@bet_cong_ratio_eq R n.+1 a b c c b a); rewrite (betS_sym c) HB.
rewrite HC /cong eq_sym /= => E; move: (E isT isT isT HC) => {E}.
have ac_nz : a - c != 0 by move: HB; rewrite betS_neq13 subr_eq0 => /andP [].
rewrite /betR !sub_1_ratio // ?subr_eq0 1?eq_sym -1?subr_eq0 //.
rewrite opprB addrBDB opprB addrBDB -(opprB a b) -(opprB b c) -(opprB a c).
rewrite -!ratioNN; set r1 := ratio _ _; set r2 := ratio _ _.
have r1r2P : r2 = 1 - r1 by rewrite /r1 /r2 sub_1_ratio // opprB addrBDB.
rewrite -(invf_div r1) r1r2P; set r := _ / _; move => E; have r_lt0 : 0 < r.
- move: (betS_gt0 HB); rewrite ratioNN !opprB.
  by rewrite -/r2 r1r2P opprB addrCA subrr addr0.
have r_nz : r != 0 by move: r_lt0; rewrite lt0r => /andP [].
have {r_nz} /eqP : r * r = 1 by apply (mulfI r_nz); rewrite {3}E divff ?mulr1.
rewrite -expr2 sqrf_eq1 => /orP [] /eqP rE; last first.
- by move: r_lt0; rewrite rE lt0r ler_oppr oppr0 ler10 andbF.
have /andP[/eqP r1E /eqP r2E] : (r1 == 1%:R / 2%:R) && (r2 == 1%:R / 2%:R).
- suff /eqP r1E : r1 == 1%:R / 2%:R.
  + rewrite r1E eqxx r1r2P r1E subr_eq.
    by rewrite addf_divrr -?natrD ?divff ?add11_neq0 ?eqxx.
  apply /eqP; apply (mulfI (add11_neq0 R)); rewrite mulrA mulr1.
  rewrite divff ?add11_neq0 // mulrDl mul1r; apply /eqP.
  rewrite -{2}(opprK r1) subr_eq; apply /eqP; suff r1P : (1 - r1)^-1 != 0.
  - by apply (mulfI r1P); rewrite mulrC -/r rE mulrC divff -1?invr_eq0.
  rewrite invr_eq0 -r1r2P; move: HB; rewrite /betS /betR ratioNN !opprB -/r2.
  by move => /and3P [] _; rewrite lt0r => /andP [].
have: betS c b a by rewrite betS_sym.
move: HB; rewrite /betS /betR ratioNN !opprB -/r1 -/r2 -(opprB b).
move => /and3P [] /eqP -> _ _ /and3P [] /eqP -> _ _.
by rewrite -scalerN opprB r1E r2E.
Qed.

Lemma lower_dim : forall o i basis,
  ~ lower_dimP _ (@bet R (n.+1)) (@cong R (n.+1)) n.+2 o i basis.
Proof.
move => o i' basis HF; pose new_basis := map_tuple (+%R^~ (- o)) basis.
suff: free new_basis.
- move => {HF} HF; suff {HF} : ~~ free new_basis by rewrite HF.
  rewrite /free size_tuple ltn_eqF // ltnS.
  apply: (leq_trans (dimvS (subvf <<new_basis>>))).
  by rewrite dimvf /Vector.dim /= mul1n.
suff: (forall (i : 'I_n.+2), new_basis`_i *m new_basis`_i^T <> 0) /\
      (forall (i j : 'I_n.+2), i <> j -> new_basis`_i *m new_basis`_j^T = 0).
- move => {HF} [no_null_vec ortho]; apply /freeP => k kt0 j.
  have {kt0} : (\sum_(i < n.+2) k i *: new_basis`_i) *m new_basis`_j^T = 0.
  + by rewrite kt0 mul0mx.
  rewrite mulmx_suml (bigID (pred1 j)) /= big_pred1_eq big1 ?addr0.
  + move=> /eqP; rewrite -scalemxAl scaler_eq0.
    by move/eqP/negPf: (no_null_vec j) => ->; rewrite orbF; apply /eqP.
  + by move => l lP; rewrite -scalemxAl ortho ?scaler0 //; move/eqP: lP.
move: HF; rewrite /lower_dimP /orthonormal_basis; set i := tnth basis (inord 0).
move => [] HNE [] HB []; rewrite -big_andb_and -big_pairs_andb_and !big_all.
move => /allP HC1 /allP HC2; split => [j|j k jk_neq].
- apply /eqP; rewrite quad_eq0 /new_basis.
  rewrite (nth_map 0) ?size_tuple ?(ltn_ord j) // subr_eq0.
  case: (basis`_j =P o) => // jP; move: (HC1 j).
  rewrite mem_index_iota leq0n (ltn_ord j) => {HC2} HC2.
  move: (HC2 isT); rewrite nth_basis ?(ltn_ord j) // => {HC2}.
  rewrite /cong jP subrr mul0mx quad_eq0 subr_eq0 => /eqP i'oE.
  move: (HC1 O); rewrite mem_index_iota ltn0Sn /= => {HC1} HC.
  move: (HC isT); rewrite /cong i'oE subrr mul0mx eq_sym quad_eq0.
  by rewrite subr_eq0 => /eqP ioE; move: HNE; rewrite /i ioE i'oE.
- suff: forall (j k : 'I_n.+2), (j < k)%N -> new_basis`_j *m new_basis`_k^T = 0.
  + move/eqP: jk_neq; rewrite neq_ltn => /orP.
    move => [|] jk_lt jkP; rewrite ?(jkP j k jk_lt) //.
    by rewrite dotC (jkP k j jk_lt).
  have: forall i, (i < n.+2)%N ->
                  (basis`_i - o) *m (basis`_i - o)^T = (i' - o) *m (i' - o)^T.
  + move => l lP; move: (HC1 l); rewrite mem_index_iota leq0n lP /= => {HC1} HC.
    by move: (HC isT); rewrite nth_basis // /cong eq_sym => /eqP.
  have {HC1 j k jk_neq} : cong o i' o i by rewrite (HC1 O).
  move => ii'P E j k jk_lt; move: (HC2 O) (HC2 j) => {HC2}.
  rewrite mem_index_iota leq0n ltn0Sn big_all => HC.
  move: (HC isT) => {HC} /allP HC; move: (HC (S O)).
  rewrite mem_index_iota -ltn_predRL ?ltn0Sn => {HC} HC.
  move: (HC isT); rewrite !nth_basis -?ltn_predRL ?ltn0Sn // => {HC} HC.
  have {HC} iP : (i' - o) *m (basis`_1 - o)^T = 0.
  - move: HC; rewrite /cong (cosine_rule o) eq_sym (cosine_rule o).
    rewrite (E O) ?ltn0Sn // (E (S O)) -?ltn_predRL ?ltn0Sn //.
    rewrite add2r_eq eqr_opp -/i -(@nth_basis O) ?ltn0Sn // -/i.
    rewrite (bet_cong__mid HB) // mulNmx mulrN -subr_eq0 opprK -mulrDl.
    move => {E} /eqP/rowP E; apply /rowP => l; apply /eqP.
    move: (E l); rewrite ord1 2?mxE !big_ord1; move => /eqP.
    rewrite mulf_eq0 => /orP [] //; rewrite mxE -mulr2n mulrn_eq0 !mxE eqxx.
    by rewrite -natrD pnatr_eq0 addn1.
  rewrite mem_index_iota leq0n (ltn_ord j) big_all => HC.
  move: (HC isT) => {HC} /allP HC; move: (HC k).
  rewrite mem_index_iota jk_lt (ltn_ord k) => {HC} HC.
  move: (HC isT); rewrite !nth_basis ?(ltn_ord j) ?(ltn_ord k) // => {HC}.
  rewrite /cong (cosine_rule o) eq_sym (cosine_rule o).
  rewrite (E j) // (E k) // eq_sym (E (S O)) -?ltn_predRL ?ltn0Sn //.
  rewrite add2r_eq eqr_opp iP mulr0 /new_basis.
  rewrite !(nth_map 0) ?size_tuple ?(ltn_ord j) //.
  move => {E} /eqP/rowP E; apply /rowP => l; apply /eqP.
  move: (E l); rewrite ord1 2?mxE !big_ord1; move => /eqP.
  rewrite mulf_eq0 => /orP [] //.
  by rewrite mxE -mulr2n mulrn_eq0 !mxE eqxx oner_eq0.
Qed.

Lemma upper_dim : forall o i basis,
  upper_dimP _ (@bet R (n.+1)) (@cong R (n.+1)) n.+2 o i basis.
Proof.
move => o i basis; move: (@lower_dim o i basis).
by rewrite /lower_dimP /upper_dimP /no_more_orthogonal_point.
Qed.

End Tarskinp1D.
