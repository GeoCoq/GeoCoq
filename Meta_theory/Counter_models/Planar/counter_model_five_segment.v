Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp
Require Import fintype finset finfun bigop order.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Require Import GeoCoq.Meta_theory.Models.POF_to_Tarski.

Require Import GeoCoq.Meta_theory.Counter_models.Planar.independence.

Section Ratio1D.

Variable R : realFieldType.

Lemma ratio_1D (v1 v2 : 'rV[R]_(1)) : v2 != 0 -> v1 == ratio v1 v2 *: v2.
Proof.
rewrite /ratio; case: pickP=> [x|/all_v_neq0 //]; case: x=> ? ?.
rewrite ord1=> ? ?; apply /eqP /matrixP=> i j; case: i; case: j=> ? ? ? ?.
by rewrite !ord1 !mxE mulrAC -mulrA divff // mulr1.
Qed.

End Ratio1D.

Section RfTarski2D.

Variable R : realFieldType.
Definition Point := 'rV[R]_2.
Implicit Types (a b c d : Point).

(* Definition of the counter-model *)
Definition bet' a b c :=
  bet (a 0 0)%:M (b 0 0)%:M (c 0 0)%:M &&
  bet (a 0 1)%:M (b 0 1)%:M (c 0 1)%:M.

Definition cong' a b c d :=
  cong (a 0 0)%:M (b 0 0)%:M  (c 0 0)%:M (d 0 0)%:M &&
  cong (a 0 1)%:M (b 0 1)%:M  (c 0 1)%:M (d 0 1)%:M.

Definition a' : 'rV[R]_2 := row2 (-1) 0.
Definition b' : 'rV[R]_2 := row2 0 1.
Definition c' : 'rV[R]_2 := row2 1 0.

Definition sqr_L2_norm_1D (a b : 'rV[R]_1) := (b 0 0 - a 0 0) ^+ 2.

Definition sqr_L2_norm_1D_i a b i := sqr_L2_norm_1D (a 0 i)%:M (b 0 i)%:M.

Lemma congP_aux' (a b : 'rV[R]_1) :
  (b - a) *m (b - a)^T = (sqr_L2_norm_1D a b)%:M.
Proof.
rewrite [X in X=_]mx11_scalar /sqr_L2_norm_1D !mxE.
rewrite !big_ord_recr /= big_ord0 add0r !mxE -!expr2.
by congr ((b 0 _ - a 0 _) ^+ 2)%:M; apply: val_inj.
Qed.

Lemma congP_aux a b c d :
  cong' a b c d =
  (sqr_L2_norm_1D_i a b 0 == sqr_L2_norm_1D_i c d 0) &&
  (sqr_L2_norm_1D_i a b 1 == sqr_L2_norm_1D_i c d 1).
Proof.
rewrite /cong' /sqr_L2_norm_1D_i /cong !congP_aux' /sqr_L2_norm_1D;
apply/andP/andP; [move=> [H0 H1]|move=> [/eqP-> /eqP->] //].
move/eqP: H0; move/eqP: H1; move=>/matrixP /(_ 0 0) /eqP H0.
move=> /matrixP /(_ 0 0) /eqP H1; move: H1 H0; rewrite !mxE /= !mulr1n.
move=> /eqP -> /eqP ->; by split.
Qed.

Lemma congP a b c d :
  reflect ((sqr_L2_norm_1D_i a b 0 == sqr_L2_norm_1D_i c d 0) /\
           (sqr_L2_norm_1D_i a b 1 == sqr_L2_norm_1D_i c d 1))
          (cong' a b c d).
Proof. by rewrite !congP_aux; exact /andP. Qed.

Lemma bet_012 : @bet R 1 0%:M 1%:M (1+1)%:M.
Proof.
have eq0P : 0%:M = 0 by move => *; apply/matrixP => i j; rewrite !mxE// mul0rn.
apply /orP; right; rewrite -scalemx1 -scalemx1 -[(1+1)%:M]scalemx1 ?eq0P.
rewrite /betS /betR ?scale0r !subr0 scale1r /ratio.
case: pickP=> [x _|HF]; [|move: (HF 0)]; rewrite ?ord1 !mxE eqxx !mulr1;
rewrite ?add11_neq0 // mul1r !scalerA 1!mulrC divff ?add11_neq0 ?eqxx //=.
rewrite ?scale1r ?eqxx//.
by rewrite invf_lt1 -1?{3}[1]add0r ?invr_gt0 ?addr_gt0 ?ltr_add2r ?ltr01.
Qed.

(* Proof that the following axiom does not hold in the given model *)
Lemma five_segment : ~ five_segmentP Point bet' cong'.
Proof.
unfold five_segmentP=> H.
set a := (@row2 R 0 1); set b := (@row2 R 1 1); set c := (@row2 R (1+1) (1+1)).
set d := (@row2 R 1 (1+1)); set d' := (@row2 R 1 0); absurd (cong' c d c d').
  rewrite /cong' /cong !mxE eqxx /= subrr mul0mx eq_sym quad_eq0.
  rewrite -[X in X == _]opprB oppr_eq0 -scalemx1 -[0%:M]scalemx1 -scalerBl.
  rewrite subr0 scalemx_eq0=> /orP [|/eqP HF]; rewrite ?paddr_eq0 ?oner_eq0;
  by rewrite ?ler01 //; move: (matrix_nonzero1 R 0); rewrite HF eqxx.
apply (H a a b b c c d d'); rewrite /bet' /a /b /c /d /d'; try apply /congP;
rewrite /sqr_L2_norm_1D_i /sqr_L2_norm_1D ?mxE /= ?eqxx ?bet_xxa ?andbT //=;
rewrite ?mul0rn ?sub0r ?mulr1n ?sqrrN -1?addrA ?subrr ?addr0 ?eqxx ?bet_012 //.
by apply /eqP; rewrite -subr_eq0 vector2_eq0 !mxE /= sub0r oppr_eq0 oner_eq0.
Qed.

(* Proof that the following axioms hold in the given model *)
Lemma point_equality_decidability : point_equality_decidability Point.
Proof. by move=> a b; case: (a =P b); tauto. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof.
move=> a b c d /andP[H10 H11] /andP[H20 H21]; rewrite /bet'; apply /andP; split;
[move : H10 H20|move: H11 H21]; apply bet_inner_transitivity.
Qed.

Lemma cong_pseudo_reflexivity :
  cong_pseudo_reflexivityP Point cong'.
Proof.
move => a b; rewrite /cong'; apply /andP; split; apply cong_pseudo_reflexivity.
Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof.
move => a b c /congP[H0 H1]; apply /eqP; rewrite vector2_eq; move: H0 H1.
rewrite /sqr_L2_norm_1D_i /sqr_L2_norm_1D !mxE eqxx !subrr !mulr1n expr0n.
by rewrite !sqrf_eq0 !subr_eq0=> /eqP -> /eqP ->; rewrite !eqxx.
Qed.

Lemma cong_inner_transitivity :
  cong_inner_transitivityP Point cong'.
Proof.
move => a b c d e f /andP[H10 H11] /andP[H20 H21]; rewrite /cong'; apply /andP;
split; [move: H10 H20|move: H11 H21]; apply cong_inner_transitivity.
Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q /andP[H00 H01] /andP[H10 H11] /eqP E1 /eqP E2 /eqP E3 /eqP E4.
move: E1; rewrite -subr_eq0 vector2_neq0 !mxE !subr_eq0 => E1.
move: E2; rewrite -subr_eq0 vector2_neq0 !mxE !subr_eq0 => E2.
move: E3; rewrite -subr_eq0 vector2_neq0 !mxE !subr_eq0 => E3.
move: E4; rewrite -subr_eq0 vector2_neq0 !mxE !subr_eq0 => E4.
suffices: ((exists x0,
             bet (p 0 0)%:M x0 (b 0 0)%:M && bet (q 0 0)%:M x0 (a 0 0)%:M) /\
           (exists x1,
             bet (p 0 1)%:M x1 (b 0 1)%:M && bet (q 0 1)%:M x1 (a 0 1)%:M)).
  move=> [[x0 /andP[Hx01 Hx02]] [x1 /andP[Hx11 Hx12]]].
  exists (row2 (x0 0 0) (x1 0 0)); rewrite /bet' !mxE /= -2!mx11_scalar.
  by rewrite Hx01 Hx02 Hx11 Hx12.
split; [move: H00 H10|move: H01 H11]; move: E1 E2 E3 E4.
  case: (a 0 0 =P p 0 0)=> [->|?];
  [set x0 := p 0 0|case: (p 0 0 =P c 0 0)=> [->|?];
  [set x0 := q 0 0|case: (b 0 0 =P q 0 0)=> [->|?];
  [set x0 := q 0 0|case: (q 0 0 =P c 0 0)=> [->|?]; [set x0 := p 0 0|]]]];
  try (exists (x0)%:M); rewrite ?bet_xxa ?bet_axx ?andbT /= 1?bet_sym ?H00 ?H10;
  rewrite //; move=> _ _ _ _ Hb1 Hb2; assert (H := @inner_pasch_gen R 1);
  destruct (H (a 0 0)%:M (b 0 0)%:M (c 0 0)%:M (p 0 0)%:M (q 0 0)%:M) as [x Hx];
  try solve[move=> /matrixP /(_ 0 0) /eqP; rewrite !mxE !mulr1n=> /eqP E //];
  [rewrite bet_sym Hb1|rewrite Hb2|exists x]=> //; by apply /andP.
case: (a 0 1 =P p 0 1)=> [->|?];
[set x1 := p 0 1|case: (p 0 1 =P c 0 1)=> [->|?];
[set x1 := q 0 1|case: (b 0 1 =P q 0 1)=> [->|?];
[set x1 := q 0 1|case: (q 0 1 =P c 0 1)=> [->|?]; [set x1 := p 0 1|]]]];
try (exists (x1)%:M); rewrite ?bet_xxa ?bet_axx ?andbT /= 1?bet_sym ?H01 ?H11;
rewrite //; move=> _ _ _ _ Hb1 Hb2; assert (H := @inner_pasch_gen R 1).
destruct (H (a 0 1)%:M (b 0 1)%:M (c 0 1)%:M (p 0 1)%:M (q 0 1)%:M) as [x Hx];
try solve[move=> /matrixP /(_ 0 0) /eqP; rewrite !mxE !mulr1n=> /eqP E //];
[rewrite bet_sym Hb1|rewrite Hb2|exists x]=> //; by apply /andP.
Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof. move => a b c /andP[H1 H2]; apply /andP; split; by rewrite bet_sym. Qed.

Lemma bet_1D (a b c : Point) i :
  a 0 i - c 0 i != 0 ->
  0 < (b 0 i - a 0 i) / (c 0 i - a 0 i) < 1 ->
  bet (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M.
Proof.
move=> NE /andP[HGt HLt]; rewrite /bet /betS.
have: (betR (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M = (b 0 i-a 0 i) / (c 0 i-a 0 i)).
  apply ratio_eq; rewrite -[(a 0 i) %:M]scalemx1 -1?[(b 0 i)%:M]scalemx1;
  rewrite -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA ?scalemx_eq0 ?negb_or;
  rewrite ?matrix_nonzero1 ?andbT -1?mulrAC -?mulrA ?divff ?mulr1 //;
  by rewrite subr_eq0 eq_sym -subr_eq0.
move=> ->; rewrite HLt HGt !andbT -[(a 0 i) %:M]scalemx1 -[(b 0 i)%:M]scalemx1.
rewrite -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA -mulrAC -mulrA divff ?mulr1;
by rewrite ?eqxx ?orbT // subr_eq0 eq_sym -subr_eq0.
Qed.

Lemma neq_mx10 (n : nat) : ((1%:M : 'M[R]_n.+1) == 0) = false.
Proof.
apply /eqP. intro H.
move: (@matrix_nonzero1 R n).
by rewrite H eqxx.
Qed.

Lemma neq_mx (n : nat) (a b : R) : ((a%:M : 'M[R]_n.+1) == b%:M) = (a == b).
Proof.
by rewrite -scalemx1 -[b%:M]scalemx1 -subr_eq0 -scalerBl scalemx_eq0
           neq_mx10 orbF subr_eq0.
Qed.

Lemma oner_neqm1: 1 != -1 :> R.
Proof. by rewrite -addr_eq0 lt0r_neq0 ?addr_gt0 ?ltr01. Qed.

Lemma oner_eqm1: 1 == -1 :> R = false.
Proof. by rewrite (negbTE oner_neqm1). Qed.

Lemma nbet_abc : (bet' a' b' c') = false.
Proof.
rewrite /bet' /bet /betE /a /b /c !mxE /= !neq_mx oner_eq0.
rewrite [0 == 1]eq_sym oner_eq0.
have:  (betS 0%:M 1%:M 0%:M = false).
  rewrite /betS /betR /ratio /= => t.
  case: pickP => /= [i|/all_v_neq0 H].
  case: i => ? ?.
  rewrite ord1 /= subrr.
  rewrite !mxE /=.
  by rewrite eqxx.
  by rewrite ltxx /= andbF.
by move->;apply /andP; move=> [_ /orP[/or3P[||]|]].
Qed.

Lemma nbet_bca : (bet' b' c' a') = false.
Proof.
rewrite /bet'/bet /betE /a /b /c !mxE /= !neq_mx.
rewrite oner_eq0 [0 == 1]eq_sym oner_eq0.
rewrite gt_eqF ?gt0_cp ?ltr01 //.
have: betS 0%:M 1%:M (-1)%:M = false.
  move=>t.
  rewrite /betS /betR /ratio.
  case: pickP => /= [i|/all_v_neq0 H].
  case: i => ? ?.
  rewrite ord1 !mxE /= mul0rn subr0 mulr1n subr0 invrN mulrN.
  rewrite divff ?oner_eq0 //.
  by rewrite oppr_gt0 ltr10 andbF.
  by rewrite ltxx andbF.
by move->;apply /andP; move=> [/orP[/or3P[||]|]?  _].
Qed.

Lemma nbet_cab : (bet' c' a' b') = false.
Proof.
rewrite /bet' /bet /betE /a /b /c !mxE /= !neq_mx.
rewrite oner_eqm1 oppr_eq0 oner_eq0.
have: betS 1%:M (-1)%:M 0%:M = false.
  move=>t.
  rewrite /betS  /betR /ratio /=.
  case: pickP => /= [i|/all_v_neq0 H].
  case: i => ? ?.
  rewrite ord1 !mxE mul0rn sub0r !mulr1n invrN mulrN divr1.
  by rewrite opprB ltr_subl_addr subrr ltr10 !andbF.
  by rewrite ltxx andbF.
by move->;apply /andP; move=> [/orP[/or3P[||]|]?  _].
Qed.

Lemma lower_dim : lower_dimP Point bet' a' b' c'.
Proof.
rewrite /lower_dimP /Col nbet_abc nbet_cab nbet_bca.
by move=> [|[|]].
Qed.

Lemma cong_abac_1D  (a b c : 'rV[R]_1) :
  (cong a b a c) = ((b == c) || (a == (1+1)^-1 *: (b+c))).
Proof.
rewrite /cong !congP_aux' /sqr_L2_norm_1D neq_mx eqf_sqr.
rewrite -subr_eq0 opprB addrBDB subr_eq0.
rewrite -[(b 0 0 - a 0 0 == a 0 0 - c 0 0)]subr_eq0.
rewrite opprB addrACA -[X in _ + X]opprB opprK.
rewrite subr_eq0 -[a 0 0]mul1r -mulrDl.
apply /orP/orP.
move=> [/eqP H|/eqP H]; [left|right].
apply /eqP /matrixP=> i j.
by rewrite !ord1 H.
apply /eqP /matrixP=> i j.
by rewrite !ord1 !mxE H mulKf ?add11_neq0.
move=> [/eqP->|/eqP->]; [left|right]; rewrite ?eqxx //.
by rewrite !mxE /= mulrA divff ?add11_neq0 ?mul1r.
Qed.

Lemma mx11_eq (a b : 'rV[R]_1):
  a == b = (a 0 0 == b 0 0).
Proof.
apply /eqP/eqP=> [-> //|H].
by apply/matrixP=> i j; rewrite !ord1.
Qed.

Lemma bet_1D' (a b c : 'rV[R]_1) :
  a 0 0 - c 0 0 != 0 ->
  0 < (b 0 0 - a 0 0) / (c 0 0 - a 0 0) < 1 ->
  bet a b c.
Proof.
move=> NE /andP[HGt HLt]; rewrite /bet /betS.
have: (betR (a 0 0)%:M (b 0 0)%:M (c 0 0)%:M = (b 0 0-a 0 0) / (c 0 0-a 0 0)).
  apply ratio_eq; rewrite -[(a 0 0) %:M]scalemx1 -1?[(b 0 0)%:M]scalemx1;
  rewrite -[(c 0 0)%:M]scalemx1 -!scalerBl ?scalerA ?scalemx_eq0 ?negb_or;
  rewrite ?matrix_nonzero1 ?andbT -1?mulrAC -?mulrA ?divff ?mulr1 //;
  by rewrite subr_eq0 eq_sym -subr_eq0.

rewrite -!mx11_scalar.
move=> ->. rewrite HLt HGt !andbT. apply /orP; right.
apply /eqP/matrixP=> i j.
by rewrite !ord1 !mxE /= mulrAC -mulrA divff ?mulr1 // subr_eq0 eq_sym -subr_eq0.
Qed.

Lemma col_1D (a b c : 'rV[R]_1) :
  (bet a b c \/ bet b c a \/ bet c a b).
Proof.
suffices: ([ || bet a b c, bet b c a | bet c a b]).
  by move => /or3P[]; tauto.
case: (a =P b) => [-> |/eqP NE1]; rewrite ?bet_xxa //.
case: (b =P c) => [-> |/eqP NE2]; rewrite ?bet_xxa ?bet_axx //.
case: (c =P a) => [-> |/eqP NE3]; rewrite ?bet_xxa ?orbT //.
move: NE1 NE2 NE3.
rewrite !mx11_eq.
rewrite -subr_eq0 => NE1.
rewrite -subr_eq0 => NE2.
rewrite -subr_eq0 => NE3.
elim (ratio_cp NE1 NE2 NE3).
move => H .
move: NE3.
rewrite subr_eq0 eq_sym -subr_eq0 => NE3.
by move: (bet_1D' NE3 H)=> ->.
elim.
move => H.
move: NE1.
rewrite subr_eq0 eq_sym -subr_eq0 => NE1.
move: (bet_1D' NE1 H)=> -> /=.
apply /orP.
by right.
move => H.
move: NE2.
rewrite subr_eq0 eq_sym -subr_eq0 => NE2.
move: (bet_1D' NE2 H) => ->.
apply /orP.
right.
apply /orP.
by right.
Qed.

Lemma upper_dim : upper_dimP Point bet' cong'.
Proof.
move => a b c p q /eqP neq_pq _ _ _; move: neq_pq.
rewrite /cong' !cong_abac_1D !neq_mx -subr_eq0 vector2_neq0 !mxE /= !subr_eq0.
case: (p 0 0 =P q 0 0) => /= _; [case: (p 0 1 =P q 0 1) => //= _ | ] => _.
  rewrite /Col /bet'=> /eqP-> /eqP-> /eqP->; rewrite !bet_xxa !andbT; apply col_1D.
rewrite /Col /bet'=> /andP[/eqP-> _] /andP[/eqP-> _] /andP[/eqP-> _].
rewrite !bet_xxa /=; apply col_1D.
Qed.

End RfTarski2D.

Section RcfTarski2D.

Variable R : rcfType.

Implicit Types (a b c d : 'rV[R]_(2)).

Lemma segment_construction :
  segment_constructionP (@Point R) (@bet' R) (@cong' R).
Proof.
move=> a b c d.
(*pose (@segment_construction R 1 a b c d).*)
destruct (@segment_construction R _ (a 0 0)%:M (b 0 0)%:M (c 0 0)%:M (d 0 0)%:M) as [x [HxB HxC]].
destruct (@segment_construction R _ (a 0 1)%:M (b 0 1)%:M (c 0 1)%:M (d 0 1)%:M) as [y [HyB HyC]].
exists (row2 (x 0 0) (y 0 0)).
rewrite /bet' /cong' !mxE /=.
rewrite [x]mx11_scalar in HxB HxC.
rewrite [y]mx11_scalar in HyB HyC.
by split; apply /andP; split.
Qed.

Lemma bet_1Di a b c i :
  a 0 i <= b 0 i -> b 0 i <= c 0 i ->
  bet (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M.
Proof.
rewrite !le_eqVlt; case: (a 0 i =P b 0 i)=> [->|_]; rewrite ?bet_xxa //=.
case: (b 0 i =P c 0 i)=> [->|_]; rewrite ?bet_axx //= => HLt HGt.
have: (0 < c 0 i - a 0 i)=> [|ac_lt]; first by rewrite subr_gt0 (lt_trans HLt).
have: (0 < (b 0 i-a 0 i) / (c 0 i-a 0 i)); [|move: HLt=> _ HLt].
  by rewrite ltr_pdivl_mulr // mul0r subr_gt0.
have: ((b 0 i-a 0 i) / (c 0 i-a 0 i) < 1); [|move: HGt=> _ HGt].
  by rewrite ltr_pdivr_mulr // mul1r ltr_subr_addr addrAC -addrA subrr addr0.
have: (betR (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M = (b 0 i-a 0 i) / (c 0 i-a 0 i)).
  by apply ratio_eq; rewrite -[(a 0 i) %:M]scalemx1 -1?[(b 0 i)%:M]scalemx1;
  rewrite -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA ?scalemx_eq0 ?negb_or;
  rewrite ?matrix_nonzero1 -1?mulrAC -?mulrA ?divff ?lt0r_neq0 // mulr1 eqxx.
rewrite /bet /betS=> ->; rewrite HLt HGt -[(a 0 i) %:M]scalemx1;
rewrite -[(b 0 i)%:M]scalemx1 -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA;
by rewrite -mulrAC -mulrA divff ?mulr1 ?eqxx ?orbT // lt0r_neq0.
Qed.

Lemma bet_1Dd a b c i :
  c 0 i <= b 0 i -> b 0 i <= a 0 i ->
  bet (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M.
Proof.
rewrite !le_eqVlt; case: (b 0 i =P a 0 i)=> [->|_]; rewrite ?bet_xxa //=.
case: (c 0 i =P b 0 i)=> [->|_]; rewrite ?bet_axx //= => HLt HGt.
have: (c 0 i - a 0 i < 0)=> [|ac_lt]; first by rewrite subr_lt0 (lt_trans HLt).
have: (0 < (b 0 i-a 0 i) / (c 0 i-a 0 i)); [|move: HGt=> _ HGt].
  by rewrite ltr_ndivl_mulr // mul0r subr_lt0.
have: ((b 0 i-a 0 i) / (c 0 i-a 0 i) < 1); [|move: HLt=> _ HLt].
  by rewrite ltr_ndivr_mulr // mul1r ltr_subr_addr addrAC -addrA subrr addr0.
have: (betR (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M = (b 0 i-a 0 i) / (c 0 i-a 0 i)).
  by apply ratio_eq; rewrite -[(a 0 i) %:M]scalemx1 -1?[(b 0 i)%:M]scalemx1;
  rewrite -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA ?scalemx_eq0 ?negb_or;
  rewrite ?matrix_nonzero1 -1?mulrAC -?mulrA ?divff ?ltr0_neq0 // mulr1 eqxx.
rewrite /bet /betS=> ->; rewrite HLt HGt -[(a 0 i) %:M]scalemx1;
rewrite -[(b 0 i)%:M]scalemx1 -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA;
by rewrite -mulrAC -mulrA divff ?mulr1 ?eqxx ?orbT // ltr0_neq0.
Qed.

Lemma permP a b c d : exists e f g h : Point R,
  [&& perm_eq [:: a; b; c; d] [:: e; f; g; h],
  (e 0 0 <= f 0 0), (g 0 0 <= h 0 0) &
  [&& (g 0 1 <= e 0 1), (h 0 1 <= e 0 1), (g 0 1 <= f 0 1) & (h 0 1 <= f 0 1)]].
Proof.
move: (perm_sort (fun p q : (@Point R) => q 0 1 <= p 0 1) [:: a; b; c; d]).
have: (total (fun p q : (@Point R) => q 0 1 <= p 0 1))=> [p q|totalP].
  case: (p 0 1 =P q 0 1)=> [->|/eqP H]; rewrite ?lexx //.
  by move: (lt_total H)=> /orP[HLt|HLt]; rewrite (ltW HLt) ?orbT.
pose s := (sort (fun p q : Point R => q 0 1 <= p 0 1) [:: a; b; c; d]).
move: totalP (sort_sorted totalP [:: a; b; c; d]); rewrite -/s=> _ seqP1 seqP2.
have: (exists e f g h, s = [:: e; f; g; h])=> [|[e [f [g [h sP]]]]].
  exists (nth a s 0), (nth a s 1), (nth a s 2), (nth a s 3).
  move: (size_sort (fun p q : Point R => q 0 1 <= p 0 1) [:: a; b; c; d]).
  rewrite -/s=> Hsize; apply eq_from_nth with a; first by move: Hsize.
  rewrite Hsize; move=> i; case i=> //=; repeat (move=> n; case: n => //=).
move: seqP1; rewrite sP=> /= /and4P[HLe1 HLe2 HLe3 _].
suff: ([:: e; f; g; h] = [:: e; f] ++ [:: g; h])=> [Eq1|//=].
suff: ([:: f; e; g; h] = [:: f; e] ++ [:: g; h])=> [Eq2|//=].
suff: ([:: e; f; h; g] = [:: e; f] ++ [:: h; g])=> [Eq3|//=].
suff: ([:: f; e; h; g] = [:: f; e] ++ [:: h; g])=> [Eq4|//=].
suff: ([:: f; e] = rcons [:: f] e)=> [Eq5|//=].
suff: ([:: h; g] = rcons [:: h] g)=> [Eq6|//=].
case: (e 0 0 =P f 0 0)=> [ef_eq|/eqP H]; [|move: H (lt_total H)=> _].
  case: (g 0 0 =P h 0 0)=> [gh_eq|/eqP H]; [|move: H (lt_total H)=> _].
    exists e, f, g, h; rewrite -ef_eq -gh_eq !lexx -sP perm_sym permEl //.
    by rewrite !(le_trans HLe3) ?(le_trans HLe2) ?lexx.
  move=> /orP[HLt|HLt]; [exists e, f, g, h|exists e, f, h, g];
  rewrite !(le_trans HLe3) ?(le_trans HLe2) ?lexx // -ef_eq lexx (ltW HLt);
  rewrite !andbT; apply perm_trans with s; rewrite perm_sym;
  rewrite sP ?perm_refl //; try solve [rewrite -sP permEl //].
  by rewrite Eq1 Eq3 Eq6 perm_cat2l perm_rcons perm_refl.
case: (g 0 0 =P h 0 0)=> [gh_eq|/eqP H]; [|move: H (lt_total H)=> _].
  move=> /orP[HLt|HLt]; [exists e, f, g, h|exists f, e, g, h];
  rewrite !(le_trans HLe3) ?(le_trans HLe2) ?lexx // -gh_eq lexx (ltW HLt);
  rewrite !andbT; apply perm_trans with s; rewrite perm_sym;
  rewrite sP ?perm_eq_refl //; try solve [rewrite -sP permEl //].
  by rewrite Eq1 Eq2 Eq5 perm_cat2r perm_rcons perm_refl.
move=> /orP[HLt1|HLt1] /orP[HLt2|HLt2];
[exists e, f, g, h|exists f, e, g, h|exists e, f, h, g|exists f, e, h, g];
rewrite !(le_trans HLe3) ?(le_trans HLe2) ?lexx // (ltW HLt1) (ltW HLt2);
rewrite !andbT; apply perm_trans with s; rewrite perm_sym;
rewrite sP ?perm_refl //; try solve [rewrite -sP permEl //];
[| |apply perm_trans with ([:: e; f; h; g])]; rewrite ?Eq1 ?Eq2 ?Eq3 ?Eq4;
by rewrite ?Eq5 ?Eq6 ?perm_cat2l ?perm_cat2r ?perm_rcons perm_refl.
Qed.

Lemma line_intersection_1 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a d y /\ Col (Point R) (@bet' R) b c y.
Proof.
move=> ab_le0 cd_le0 ca_le1 da_le1 cb_le1 db_le1.
have: (bet (d 0 1)%:M (Num.min (a 0 1) (b 0 1))%:M (a 0 1)%:M)=> [|betPy1].
  case: (a 0 1 =P b 0 1)=> [->|/eqP H]; first by rewrite minxx bet_axx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // ?bet_axx // bet_1Di ?lexx // ltW.
have: (bet (c 0 1)%:M (Num.min (a 0 1) (b 0 1))%:M (b 0 1)%:M)=> [|betPy2].
  case: (a 0 1 =P b 0 1)=> [->|/eqP H]; first by rewrite minxx bet_axx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
exists (row2 (Num.max (a 0 0) (c 0 0)) (Num.min (a 0 1) (b 0 1))).
split; right; left; rewrite /bet' !mxE /= ?betPy1 ?betPy2 andbT.
  case: (a 0 0 =P c 0 0)=> [->|/eqP H]; first by rewrite max_l ?bet_1Dd ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // ?bet_axx // bet_1Dd ?lexx // ltW.
case: (a 0 0 =P c 0 0)=> [->|/eqP H]; first by rewrite max_l ?bet_xxa ?lexx.
move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
by rewrite ?ltW // ?bet_xxa // bet_1Di ?lexx // ltW.
Qed.

Lemma line_intersection_2 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.
Proof.
move=> ab_le0 cd_le0 ca_le1 da_le1 cb_le1 db_le1.
have: (bet (Num.min (a 0 0) (c 0 0))%:M (a 0 0)%:M (b 0 0)%:M)=> [|betPx1].
  case: (a 0 0 =P c 0 0)=> [->|/eqP H]; first by rewrite min_l ?bet_xxa ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
have: (bet (a 0 0)%:M (b 0 0)%:M (Num.max (b 0 0) (d 0 0))%:M)=> [|betPx2].
  case: (b 0 0 =P d 0 0)=> [->|/eqP H]; first by rewrite max_l ?bet_axx ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
have: (bet (Num.min (a 0 0) (c 0 0))%:M (c 0 0)%:M (d 0 0)%:M)=> [|betPx3].
  case: (a 0 0 =P c 0 0)=> [->|/eqP H]; first by rewrite min_l ?bet_xxa ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
have: (bet (c 0 0)%:M (d 0 0)%:M (Num.max (b 0 0) (d 0 0))%:M)=> [|betPx4].
  case: (b 0 0 =P d 0 0)=> [->|/eqP H]; first by rewrite max_l ?bet_axx ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
case: (a 0 1 =P b 0 1)=> [H|/eqP H]; [|move: (lt_total H)=> /orP[?|?]].
    exists (row2 (Num.max (b 0 0) (d 0 0)) (d 0 1)).
    by split; left; rewrite /bet' !mxE /= ?H ?bet_xxa ?bet_axx ?betPx2 ?betPx4.
  exists (row2 (Num.min (a 0 0) (c 0 0)) (c 0 1)); split; right; right;
  by rewrite /bet' !mxE /= ?bet_xxa ?betPx1 ?betPx3 ?bet_1Di // ?ltW.
exists (row2 (Num.max (b 0 0) (d 0 0)) (d 0 1)); split; left;
by rewrite /bet' !mxE /= ?bet_axx ?betPx2 ?betPx4 ?bet_1Dd // ?ltW.
Qed.

Lemma line_intersection_3 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a c y /\ Col (Point R) (@bet' R) b d y.
Proof.
move=> ab_le0 cd_le0 ca_le1 da_le1 cb_le1 db_le1.
have: (bet (Num.max (a 0 1) (b 0 1))%:M (a 0 1)%:M (c 0 1)%:M)=> [|betPx1].
  case: (a 0 1 =P b 0 1)=> [->|/eqP H]; first by rewrite max_l ?bet_xxa ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // bet_1Dd ?lexx // ltW.
have: (bet (a 0 1)%:M (c 0 1)%:M (Num.min (c 0 1) (d 0 1))%:M)=> [|betPx2].
  case: (c 0 1 =P d 0 1)=> [->|/eqP H]; first by rewrite min_l ?bet_axx ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Dd ?lexx // ltW.
have: (bet (Num.max (a 0 1) (b 0 1))%:M (b 0 1)%:M (d 0 1)%:M)=> [|betPx3].
  case: (a 0 1 =P b 0 1)=> [->|/eqP H]; first by rewrite max_l ?bet_xxa ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // bet_1Dd ?lexx // ltW.
have: (bet (b 0 1)%:M (d 0 1)%:M (Num.min (c 0 1) (d 0 1))%:M)=> [|betPx4].
  case: (c 0 1 =P d 0 1)=> [->|/eqP H]; first by rewrite min_l ?bet_axx ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Dd ?lexx // ltW.
case: (a 0 0 =P c 0 0)=> [H|/eqP H]; [|move: (lt_total H)=> /orP[?|?]].
    exists (row2 (d 0 0) (Num.min (c 0 1) (d 0 1))).
    by split; left; rewrite /bet' !mxE /= ?H ?bet_xxa ?bet_axx ?betPx2 ?betPx4.
  exists (row2 (d 0 0) (Num.min (c 0 1) (d 0 1))); split; left;
  by rewrite /bet' !mxE /= ?bet_axx ?betPx2 ?betPx4 ?bet_1Di // ?ltW.
exists (row2 (b 0 0) (Num.max (a 0 1) (b 0 1))); split; right; right;
by rewrite /bet' !mxE /= ?bet_xxa ?betPx1 ?betPx3 ?bet_1Dd // ?ltW.
Qed.

Lemma col_axx a x : Col _ (@bet' R) a x x.
Proof. by left; rewrite /Col /bet' !bet_axx. Qed.

Lemma col_xax x a : Col _ (@bet' R) x a x.
Proof. by right; left; rewrite /Col /bet' !bet_axx. Qed.

Lemma col_xxa x a : Col _ (@bet' R) x x a.
Proof. by left; rewrite /Col /bet' !bet_xxa. Qed.

Lemma dup_meet a b c d :
  uniq [:: a; b; c; d] = false ->
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.
Proof.
move=> H; have: (~~ uniq [:: a; b; c; d]) by rewrite H. move: H=> _ H.
move/uniqPn: H=> H; move: H (H a)=> _ [i [j [H1 H2 H3]]]; move: H1 H2 H3.
case: j; rewrite ?ltn0 //= => j; repeat try (case: j=> [|j //=]);
repeat try (case: i=> [|i //=])=> /=; move=> _ _ ->;
try solve [exists b; split; rewrite /Col /bet' ?bet_axx ?bet_xxa; intuition];
try solve [exists c; split; rewrite /Col /bet' ?bet_axx ?bet_xxa; intuition];
           exists d; split; rewrite /Col /bet' ?bet_axx ?bet_xxa; intuition.
Qed.

Lemma bet'_sym a b c : bet' a b c = bet' c b a.
Proof.
by rewrite /bet' bet_sym [bet (a 0 1)%:M (b 0 1)%:M (c 0 1)%:M] bet_sym.
Qed.

Lemma col_213 a b c :
  Col (Point R) (@bet' R) a b c -> Col (Point R) (@bet' R) b a c.
Proof.
by rewrite /Col bet'_sym [bet' b c a]bet'_sym [bet' c a b]bet'_sym; tauto.
Qed.

Lemma all_lines_meet a b c d :
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.
Proof.
move: (permP a b c d)=> [e [f [g [h /and4P[H H1 H2 /and4P[H3 H4 H5 H6]]]]]].
move: H (perm_mem H) (perm_uniq H)=> _ H; move: H (H a) (H b) (H c) (H d).
move: (line_intersection_1 H1 H2 H3 H4 H5 H6)=> [y1 [Y11 Y12]].
move: (line_intersection_2 H1 H2 H3 H4 H5 H6)=> [y2 [Y21 Y22]].
move: (line_intersection_3 H1 H2 H3 H4 H5 H6)=> [y3 [Y31 Y32]].
move=> _ aP bP cP dP; move: H1 H2 H3 H4 H5 H6=> _ _ _ _ _ _.
case (uniq [:: e; f; g; h] =P true)=> [H|]; rewrite ?H;
  last by rewrite Bool.not_true_iff_false => ->; apply dup_meet.
move=> H1; have: (uniq [:: a; b; c; d] = uniq [:: e; f; g; h]) by rewrite H H1.
move=> H2; move: Y22 (col_213 Y22) Y31 (col_213 Y31) Y32 (col_213 Y32).
move: H2 H H1 aP bP cP dP Y11 (col_213 Y11) Y12 (col_213 Y12) Y21 (col_213 Y21).
rewrite /uniq !in_cons !eqxx !orbT /= !in_nil=> uniqP.
case: (e =P f)=> [-> //=|]; case: (e =P g)=> [-> //=|].
case: (e =P h)=> [-> //=|]; case: (f =P g)=> [-> //=|].
case: (f =P h)=> [-> //=|]; case: (g =P h)=> [-> //=|/=]; move: uniqP.
case: (a =P b)=> [-> //=|]; case: (a =P c)=> [-> //=|].
case: (a =P d)=> [-> //=|]; case: (b =P c)=> [-> //=|].
case: (b =P d)=> [-> //=|]; case: (c =P d)=> [-> //=|/=].
move=> H1 H2 H3 H4 H5 H6 uniqP; move: uniqP H1 H2 H3 H4 H5 H6.
case: (a =P e)=> [ae_eq|_]; case: (a =P f)=> [af_eq|_];
case: (a =P g)=> [ag_eq|_]; case: (a =P h)=> [ah_eq|_];
rewrite -?ae_eq -?af_eq -?ag_eq -?ah_eq // ?ae_eq ?af_eq ?ag_eq ?ah_eq;
case: (b =P e)=> [be_eq|_]; case: (b =P f)=> [bf_eq|_];
case: (b =P g)=> [bg_eq|_]; case: (b =P h)=> [bh_eq|_];
rewrite -?be_eq -?bf_eq -?bg_eq -?bh_eq // ?be_eq ?bf_eq ?bg_eq ?bh_eq;
case: (c =P e)=> [ce_eq|_]; case: (c =P f)=> [cf_eq|_];
case: (c =P g)=> [cg_eq|_]; case: (c =P h)=> [ch_eq|_];
rewrite -?ce_eq -?cf_eq -?cg_eq -?ch_eq // ?ce_eq ?cf_eq ?cg_eq ?ch_eq;
case: (d =P e)=> [de_eq|_]; case: (d =P f)=> [df_eq|_];
case: (d =P g)=> [dg_eq|_]; case: (d =P h)=> [dh_eq|_];
rewrite -?de_eq -?df_eq -?dg_eq -?dh_eq // ?de_eq ?df_eq ?dg_eq ?dh_eq;
move=> _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _;
move=> Y11 Y11' Y12 Y12' Y21 Y21' Y22 Y22' Y31 Y31' Y32 Y32';
try solve [exists y1; split; rewrite ?Y11 ?Y11' ?Y12 ?Y12'=> //];
try solve [exists y2; split; rewrite ?Y21 ?Y21' ?Y22 ?Y22'=> //];
by exists y3; split; rewrite ?Y31 ?Y31' ?Y32 ?Y32'.
Qed.

Lemma euclid : euclidP (@Point R) (@bet' R).
Proof.
by move=> a b c d p q; move: (all_lines_meet p q c d)=> [y yP]; exists y.
Qed.

End RcfTarski2D.
