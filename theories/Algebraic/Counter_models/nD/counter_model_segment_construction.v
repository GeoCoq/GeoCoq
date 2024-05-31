Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.
From mathcomp Require Import tuple fintype bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Algebraic.Counter_models.nD.dimensional_axioms.
Require Import GeoCoq.Algebraic.tcp_ndc.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section RfTarskinD.

Variable n : nat.
Variable R : realFieldType.

Definition Point := 'rV[R]_n.
Implicit Types (a b c d : Point).

Definition bet' a b c := betS a b c || [ && a == b & b == c ].
Definition cong' a b c d := cong a b c d.
(* One cannot use the usual betwenness together with a strict congruence
   as five segment implies forall a b, cong a a b b *)

Lemma cong_abab a b : cong' a b a b.
Proof. by rewrite /cong' /cong. Qed.

Definition midpoint a b := 2%:R^-1 *: (a + b).

Lemma midpointLR a b : midpoint a b = midpoint b a.
Proof. by rewrite /midpoint addrC. Qed.

Lemma midpointBL a b : midpoint a b - a = 2%:R^-1 *: (b - a).
Proof.
rewrite /midpoint -{2}[a]scale1r scalerDr scalerBr addrAC -scalerBl addrC.
apply /eqP; rewrite add2r_eq -addr_eq0 -scalerDl scaler_eq0 addrAC.
by rewrite -div1r addf_divrr ?add11_neq0// divff ?add11_neq0// subrr eqxx.
Qed.

Lemma midpointBR a b : midpoint a b - b = 2%:R^-1 *: (a - b).
Proof. by rewrite midpointLR midpointBL. Qed.

Lemma midpointxx a : midpoint a a = a.
Proof.
rewrite /midpoint -{-3}[a]scale1r -scalerDl scalerA.
by rewrite mulrC divff ?add11_neq0// scale1r.
Qed.

Lemma betR_midpoint a b : a <> b -> betR a (midpoint a b) b = 2%:R^-1.
Proof.
move=> /eqP ab_neq; rewrite /betR midpointBL.
by apply ratio_eq; rewrite // subr_eq0 eq_sym.
Qed.

Lemma bet_midpoint a b (m := midpoint a b) : bet' a m b.
Proof.
rewrite /m /bet'; case: (a =P b)=> [->|]; first by rewrite midpointxx eqxx orbT.
move=> ab_neq; rewrite /betS betR_midpoint// midpointBL eqxx.
rewrite invr_gte0 addr_gt0 ?ltr01// invf_lt1 ?addr_gt0 ?ltr01//.
by rewrite -subr_gt0 -addrA subrr addr0 ltr01.
Qed.

Lemma cong_midpoint a b (m := midpoint a b) : cong' a m b m.
Proof.
rewrite /m /cong' /cong midpointBL midpointBR.
by rewrite -opprB scalerN mulNmx dotC -mulNmx opprK.
Qed.

Lemma Col_aaa a : independence.Col Point bet' a a a.
Proof. by rewrite /independence.Col /bet' eqxx orbT; intuition. Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point cong'.
Proof. by unfold cong_pseudo_reflexivityP; apply cong_pseudo_reflexivity. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point cong'.
Proof. by unfold cong_inner_transitivityP; apply cong_inner_transitivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. by unfold cong_identityP; apply cong_identity. Qed.

Lemma five_segment : five_segmentP Point bet' cong'.
Proof.
move => a a' b b' c c' d d'; rewrite /bet'; move=> HCab HCbc HCad HCbd.
move=> /orP[Hb1|/andP[/eqP->/eqP->//]] /orP[Hb2|/andP[/eqP Ha'b' /eqP Hb'c']];
last by move: HCab; rewrite Ha'b' Hb'c' /cong' => HCab; move: (cong_eq HCab).
by apply (@five_segment R n a a' b b' c c' d d'); rewrite /bet ?Hb1 ?Hb2 ?orbT.
Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q; rewrite /Col /bet'; move=> /orP[Hb1|/andP[/eqP->/eqP->//]].
rewrite /independence.Col => /orP[Hb2|/andP[/eqP->/eqP->//]]; move: Hb1 Hb2.
case: (a =P q) => [-> _|]; first by rewrite betS_sym => ->; intuition.
case: (b =P p)=> [-> _|? ? ? ?]; first by move=> ->; intuition.
destruct (@inner_pasch'' R n a b c p q) as [x [Hb1 Hb2]] => //.
by exists x; rewrite Hb1 Hb2.
Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof.
by move=> a b c; rewrite /bet' eq_sym Bool.andb_comm eq_sym betS_sym.
Qed.

Lemma coplanar_1324 a b c d :
  independence.Coplanar Point bet' a b c d ->
  independence.Coplanar Point bet' a c b d.
Proof.
move=> [e [f [g [Hnc [Ha [Hb [Hc Hd]]]]]]]; exists e, f, g.
by split; [|split; [|split; [|split]]].
Qed.

Lemma coplanar_3214 a b c d :
  independence.Coplanar Point bet' a b c d ->
  independence.Coplanar Point bet' c b a d.
Proof.
move=> [e [f [g [Hnc [Ha [Hb [Hc Hd]]]]]]]; exists e, f, g.
by split; [|split; [|split; [|split]]].
Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof.
rewrite /bet' => a b c d /orP[Hb1|/andP[/eqP->/eqP->]];
  last by rewrite betS_id /= => /andP[/eqP-> _]; rewrite eqxx orbT.
move=> /orP[Hb2|/andP[/eqP Hbc /eqP Hcd]].
  by rewrite (betS_inner_transitivity Hb1 Hb2).
by move: Hb1; rewrite Hbc -Hcd betS_neq23 eqxx andbF.
Qed.

End RfTarskinD.

Section RcfTarskinp2D.

Variable n : nat.
Variable R : realFieldType.

Definition o := o n R.

Definition i := i n R.

Definition basis := basis n R.

Lemma lower_dim :
  lower_dimP (@Point n.+2 R) (@bet' n.+2 R) (@cong' n.+2 R) n.+2 o i basis.
Proof.
move: (dimensional_axioms.lower_dim n R) => [oi_nz [_ ldP]].
split => //; split => //; rewrite /bet' /o /i.
by rewrite nth_basis // betS_o_i_basis_nth0.
Qed.

Lemma upper_dim :
  upper_dimP (@Point n.+2 R) (@bet' n.+2 R) (@cong' n.+2 R) n.+2 o i basis.
Proof.
have bet'P : forall a b c, @betS R n.+2 a b c -> bet' a b c.
- by move => a b c; rewrite /bet' => ->.
move => p ob1P [_ [_ [HC1 HC2]]] pP; apply bet'P, upper_dimS => //.
- by rewrite nth_new_basis //; apply i_neq_basis_nth0.
- by rewrite nth_new_basis // bet_o_i_basis_nth0.
Qed.

End RcfTarskinp2D.

Section RcfTarskinD.

Variable n : nat.
Variable R : rcfType.

Lemma onemx_neq0 :
  @const_mx (Num.RealField.sort R) (S O) (S n) 0 !=
  @const_mx (Num.RealField.sort R) (S O) (S n) 1.
Proof.
by apply/eqP=> /matrixP/(_ 0 0)/eqP; rewrite /const_mx !mxE eq_sym oner_eq0.
Qed.

Lemma segment_construction :
  ~ segment_constructionP (@Point n.+1 R) (@bet' n.+1 R) (@cong' n.+1 R).
Proof.
move/eqP: onemx_neq0 => HD HF; move: (HF _ _ (const_mx 0) (const_mx 0) HD).
rewrite /bet'; move=> [x [Hb Hc]]; move: Hb; apply /negP; rewrite Bool.negb_orb.
by rewrite Bool.negb_andb onemx_neq0 (cong_identity Hc) betS_neq23 eqxx andbF.
Qed.

Lemma bet'__bet a b c : bet' a b c -> (@bet R n.+2) a b c.
Proof. by rewrite /bet /betE; move=> /orP[->|/andP[-> ->//]]; rewrite orbT. Qed.

Lemma Midpoint_midpoint a b (m := midpoint a b) :
  @Definitions.Midpoint (Rcf_to_T R n) m a b.
Proof.
split; [apply bet'__bet, bet_midpoint|suff: cong a m m b=> [//|]].
move: (cong_midpoint a b); rewrite -/m /cong => /eqP ->.
by rewrite -{1}[m - b]opprB mulNmx dotC -mulNmx opprB.
Qed.

Lemma col__ColT a b c :
  @col R n a b c <-> @Definitions.Col (Rcf_to_T R n) a b c.
Proof. by rewrite /col /Definitions.Col. Qed.

Lemma ncol__nColT a b c :
  ~ @col R n a b c <-> ~ @Definitions.Col (Rcf_to_T R n) a b c.
Proof. by rewrite /col /Definitions.Col. Qed.

Lemma Col'__Col a b c :
  independence.Col (@Point n.+2 R) (@bet' n.+2 R) a b c ->
  independence.Col (@Point n.+2 R) (@bet R n.+2) a b c.
Proof.
move=> HC [Hnb1 [Hnb2 Hnb3]]; apply HC; split; [|split]=> Hb;
[apply Hnb1|apply Hnb2|apply Hnb3]; by apply bet'__bet.
Qed.

Lemma nCol__nCol' a b c :
  ~ independence.Col (@Point n.+2 R) (@bet R n.+2) a b c ->
  ~ independence.Col (@Point n.+2 R) (@bet' n.+2 R) a b c.
Proof. by move=> HF HNC; apply HF, Col'__Col. Qed.

Lemma ncol__nCol a b c :
  ~ @col R n a b c -> ~ independence.Col (@Point n.+2 R) (@bet R n.+2) a b c.
Proof.
rewrite /col /independence.Col.
by case: (bet a b c); case: (bet b c a); case: (bet c a b); intuition.
Qed.

Lemma nCol__ncol a b c :
  ~ independence.Col (@Point (n.+2) R) (@bet' (n.+2) R) a b c ->
  [ \/ ~ @col R n a b c, a = b /\ c <> a, c = a /\ a <> b | b = c /\ a <> b ].
Proof.
rewrite /independence.Col /col /bet' /bet /betE; case: (a =P b); case: (b =P c);
case: (c =P a); case: (betS a b c); case: (betS b c a); case: (betS c a b);
intuition; [apply Or42|apply Or44|apply Or43|apply Or41]; intuition.
Qed.

Lemma ColT__Col a b c :
  a <> b -> a <> c -> b <> c -> @Definitions.Col (Rcf_to_T R n) a b c ->
  independence.Col (@Point (n.+2) R) (@bet' (n.+2) R) a b c.
Proof.
move=> Hab Hac Hbc HC; apply col__ColT in HC; move: Hab Hac Hbc HC.
rewrite /independence.Col /bet' /col /bet /betE [c == a]eq_sym.
case: (a =P b)=> [-> //|_]; case: (a =P c)=> [->//|_]; case: (b =P c)=> [->//|];
case: (betS a b c); case: (betS b c a); case: (betS c a b)=> /=; intuition.
Qed.

Lemma coplanar_midpoint a b (m := midpoint a b) :
  a <> b -> independence.Coplanar (Point n.+2 R) (@bet' n.+2 R) a a b m.
Proof.
move=> ab_neq; move: (@tcp_aligned_plane_exists _ (Rcf_to_T_PED R n) a b m).
move=> HE; destruct (HE ab_neq (Midpoint_midpoint a b)) as [p [q [r Hpqr]]].
destruct Hpqr as [mar [mbr [? [? [? [? []]]]]]]; exists p, q, r; clear HE.
move: (@tcp_aligned_inplane _ _ (Rcf_to_T_euclidean R n)
                            a b m p q r mar mbr)=> HE.
destruct HE as [Ha [Hb Hm]]=> //; first by apply Midpoint_midpoint.
repeat split; [by apply nCol__nCol', ncol__nCol, ncol__nColT|..];
[destruct Ha as [x Hx]..|destruct Hb as [x Hx]|destruct Hm as [x Hx]];
by destruct Hx as [[? [? []]] [? [? []]]]; exists x; split; apply ColT__Col.
Qed.

Lemma col__colI a b c : @col R n a b c <-> colI a b c.
Proof.
by rewrite /col /colI; case: (bet a b c);
case: (bet b c a); case: (bet c a b); intuition.
Qed.

Lemma euclid : euclidP (@Point (n.+2) R) (@bet' (n.+2) R) (@cong' (n.+2) R).
Proof.
move => a b c HNC; apply nCol__ncol in HNC.
destruct HNC as [HNC1|[-> HNE]|[-> HNE]|[-> HNE]];
[|set m := midpoint b c|set m := midpoint a b|set m := midpoint a c];
[|exists m..]; rewrite ?cong_abab ?cong_midpoint; [|repeat split..];
[| |apply coplanar_1324|apply coplanar_3214]; [|apply coplanar_midpoint..|];
auto; last by rewrite /m midpointLR; apply coplanar_midpoint; auto.
destruct (@tcp R n a b c) as [x [HC1 [HC2 HCop]]]; rewrite -?col__colI //.
exists x; rewrite /cong'; split; [|split]=> //.
destruct (@tcp_ncol_inplane _ _ (Rcf_to_T_euclidean R n) a b c x) as [E HE] => //.
- move: HCop; rewrite -Cop__Coplanar; move => [e [f [g]]].
  move => [efgP [aP [bP [cP xP]]]]; exists e, f, g.
  split; [by move: efgP; rewrite -col__colI|repeat split];
  [destruct aP as [y [Hc1 Hc2]]|destruct bP as [y [Hc1 Hc2]]|
   destruct cP as [y [Hc1 Hc2]]|destruct xP as [y [Hc1 Hc2]]]; exists y;
  by move: Hc1 Hc2; rewrite -!col__colI.
destruct HE as [F [G [HNC2 [HA [HB [HC HX]]]]]].
exists E, F, G; split; first by apply nCol__nCol', ncol__nCol, ncol__nColT.
repeat split; [destruct HA as [Y HY]|destruct HB as [Y HY]|
               destruct HC as [Y HY]|destruct HX as [Y HY]]; exists Y;
destruct HY as [[HCol1 [HNE1 [HNE2 HNE3]]] [HCol2 [HNE4 [HNE5 HNE6]]]];
by split; apply ColT__Col.
Qed.

End RcfTarskinD.
