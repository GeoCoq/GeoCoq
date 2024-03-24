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
Require Import GeoCoq.Algebraic.tcp_ndc.
Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section RfTarskinD.

Variable n : nat.
Variable R : realFieldType.

Definition Point := 'rV[R]_(n.+1).
Implicit Types (a b c d : Point).

Definition bet' a b c :=
  bet a b c && ~~ ((a == b) && (b == c)).
Definition cong' a b c d := cong a b c d.

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

Lemma bet_midpoint a b (m := midpoint a b) : bet a m b.
Proof.
rewrite /m /bet.
case: (a =P b)=> [->|ab_neq]; first by rewrite midpointxx /betE eqxx.
rewrite /betS midpointBL betR_midpoint ?eqxx //= invr_gte0 addr_gt0 ?ltr01//.
by rewrite invf_lt1 ?addr_gt0 ?ltr01//  -subr_gt0 -addrA subrr addr0 ltr01 orbT.
Qed.

Lemma bet'_midpoint a b (m := midpoint a b) : a <> b -> bet' a m b.
Proof.
rewrite /m /bet' bet_midpoint /= eq_sym -subr_eq0 midpointBL.
rewrite scaler_eq0 invr_eq0 subr_eq0 mulr2n paddr_eq0 ?ler01 ?oner_eq0 //.
by case: (b =P a) => [->|].
Qed.

Lemma cong_midpoint a b (m := midpoint a b) : cong' a m b m.
Proof.
rewrite /m /cong' /cong midpointBL midpointBR.
by rewrite -opprB scalerN mulNmx dotC -mulNmx opprK.
Qed.

Lemma onemx_neq0 :
  @const_mx (Num.RealField.sort R) (S O) (S n) 0 !=
  @const_mx (Num.RealField.sort R) (S O) (S n) 1.
Proof.
by apply/eqP=> /matrixP/(_ 0 0)/eqP; rewrite /const_mx !mxE eq_sym oner_eq0.
Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point cong'.
Proof. by unfold cong_pseudo_reflexivityP; apply cong_pseudo_reflexivity. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point cong'.
Proof. by unfold cong_inner_transitivityP; apply cong_inner_transitivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. by unfold cong_identityP; apply cong_identity. Qed.

Lemma five_segment : five_segmentP Point bet' cong'.
Proof.
move => a a' b b' c c' d d' ? ? ? ? /andP[? _] /andP[? _] ?.
by apply (@five_segment R (n.+1) a a' b b' c c' d d').
Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q /andP[Hb1 _] /andP[Hb2 _] Hap Hpc Hbq Hqc HNC.
rewrite bet_betS in Hb1 => //; rewrite bet_betS in Hb2 => //.
have: (~~ [&& a == b, a == c & b == c]) => [|HNE].
  case (a =P b) => [_|//]; case (a =P c) => [Hac|//]; case (b =P c) => _ //=.
  by rewrite Hac betS_id in Hb1.
destruct (inner_pasch' Hb1 Hb2) as [x [Hb3 Hb4]]=> //.
  by move=> [HC|[HC|HC]]; apply HNC; rewrite /independence.Col /bet' HC;
  move=> [Hb3 [Hb4 Hb5]]; move: Hb3 Hb4 Hb5 HNE; rewrite 1?[c == a]eq_sym;
  case (a =P b) => [<-|//]; case (a =P c) => [-> //=|//]; case (b =P c)=> [<-|].
exists x; rewrite /bet' /bet Hb3 Hb4 !orbT /=; move: Hb3 Hb4.
rewrite betS_neq12 betS_neq23=> /andP[/andP[Hb3 /eqP xb_neq] /eqP px_neq].
rewrite betS_neq12 betS_neq23=> /andP[/andP[Hb4 /eqP xa_neq] /eqP qx_neq].
move: px_neq qx_neq; case: (p =P x)=> [//|_]; case: (q =P x)=> [//|_ //=].
Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof.
move=> a b c; rewrite /bet' bet_sym [a == b]eq_sym [b == c]eq_sym.
by rewrite [X in _ && ~~ X]andbC.
Qed.

Lemma bet_inner_transitivity : ~ bet_inner_transitivityP Point bet'.
Proof.
move=> HF; move: (HF (const_mx 0) (const_mx 0) (const_mx 0) (const_mx 1));
rewrite /bet' !bet_xxa eqxx /= onemx_neq0 => H.
by have: (true -> false); [apply H=> //|apply /implyP].
Qed.

End RfTarskinD.

Section RcfTarskinD.

Variable n : nat.
Variable R : rcfType.

Lemma segment_construction :
  segment_constructionP (@Point n R) (@bet' n R) (@cong' n R).
Proof.
move=> a b c d ab_neq; destruct (segment_construction a b c d) as [x [Hb Hc]].
exists x; rewrite /bet' /cong' Hb Hc; split; move=> //=; move: ab_neq.
by case: (a =P b)=> [-> //|/=].
Qed.

Lemma Col__col a b c :
  independence.Col (@Point (n.+1) R) (@bet' (n.+1) R) a b c -> @col R n a b c.
Proof.
move: (bet_axx a b); rewrite /independence.Col /bet' /col [c == a]eq_sym.
case: (a =P b)=> [<-|_]; case: (a =P c)=> [->|_]; case: (b =P c)=> [<-|_];
move=> Hb; rewrite ?Hb ?bet_axx ?bet_xxa ?andbT //=; [intuition..|].
case: (bet a b c); case: (bet b c a); case: (bet c a b)=> HF /=; auto.
exfalso; apply HF; auto.
Qed.

Lemma col__Col a b c :
  a <> b -> @col R n a b c ->
  independence.Col (@Point (n.+1) R) (@bet' (n.+1) R) a b c.
Proof.
rewrite /independence.Col /bet' /col /bet /betE [c == a]eq_sym.
case: (a =P b)=> [-> //|_]; case: (a =P c)=> [->//|_]; case: (b =P c)=> [->//|];
case: (betS a b c); case: (betS b c a); case: (betS c a b)=> /=; intuition.
Qed.

Lemma col__colI a b c : @col R n a b c <-> colI a b c.
Proof.
by rewrite /col /colI; case: (bet a b c);
case: (bet b c a); case: (bet c a b); intuition.
Qed.

Lemma ncol__ncolI a b c : ~ @col R n a b c <-> ~ colI a b c.
Proof. by rewrite col__colI. Qed.

Lemma colI__Col a b c :
  a <> b -> colI a b c ->
  independence.Col (@Point (n.+1) R) (@bet' (n.+1) R) a b c.
Proof. by rewrite -col__colI; apply col__Col. Qed.

Lemma ColD a b c : @col R n a b c \/ ~ @col R n a b c.
Proof.
rewrite /col; case: (bet a b c); case: (bet b c a); case: (bet c a b);
intuition.
Qed.

Lemma Midpoint_midpoint a b (m := midpoint a b) :
  @Definitions.Midpoint (Rcf_to_T R n) m a b.
Proof.
split; first by rewrite /Bet /= bet_midpoint.
suff: cong a m m b => //.
move: (cong_midpoint a b); rewrite -/m /cong => /eqP ->.
by rewrite -{1}[m - b]opprB mulNmx dotC -mulNmx opprB.
Qed.

Lemma coplanar_midpoint a b (m := midpoint a b) :
  a <> b -> independence.Coplanar (Point n.+1 R) (@bet' n.+1 R) a a b m.
Proof.
move=> ab_neq; move: (@tcp_aligned_plane_exists _ (Rcf_to_T_PED R n) a b m).
move=> HE; destruct (HE ab_neq (Midpoint_midpoint a b)) as [p [q [r Hpqr]]].
destruct Hpqr as [mar [mbr [? [? [? [HNC []]]]]]]; exists p, q, r; clear HE.
move: (@tcp_aligned_inplane _ _ (Rcf_to_T_euclidean R n)
                            a b m p q r mar mbr)=> HE.
destruct HE as [Ha [Hb Hm]]=> //; first by apply Midpoint_midpoint.
split; [by move => HF; apply HNC, Col__col|repeat split];
[destruct Ha as [x Hx]..|destruct Hb as [x Hx]|destruct Hm as [x Hx]];
by destruct Hx as [[? [? []]] [? [? []]]]; exists x; split; apply col__Col.
Qed.

Lemma Col_23 a b c :
  independence.Col _ (@bet' (n.+1) R) a b c ->
  independence.Col _ (@bet' (n.+1) R) a c b.
Proof.
rewrite /independence.Col /bet' (eq_sym b a) (eq_sym c a) (eq_sym c b).
rewrite !(bet_sym c) (bet_sym b c a); case: (a =P b) => [->|];
first by rewrite bet_xxa bet_xax; case: (b =P c); intuition.
case: (a =P c) => [->|]; first by rewrite ?bet_xxa ?bet_xax ?bet_axx; intuition.
by case: (b =P c) => [->|]; rewrite ?bet_axx ?bet_xax; intuition.
Qed.

Lemma col__Col_13 a b c :
  a <> c -> @col R n a b c -> independence.Col _ (@bet' (n.+1) R) a b c.
Proof.
by move => ? ?; apply Col_23, col__Col, (@col_permutation_5 (Rcf_to_T R n)).
Qed.

Lemma colI__Col_13 a b c :
  a <> c -> colI a b c -> independence.Col _ (@bet' (n.+1) R) a b c.
Proof. by rewrite -col__colI; apply col__Col_13. Qed.

Lemma euclid : euclidP (@Point (n.+1) R) (@bet' (n.+1) R) (@cong' (n.+1) R).
Proof.
move => a b c; case: (a =P b) => [->|ab_neq HNC].
- case: (b =P c) => [->|bc_neq] _; last first.
  + exists (midpoint b c); rewrite /cong' {1}/cong eqxx; split => //.
    have -> : cong b (midpoint b c) c (midpoint b c)
      by move: (cong_midpoint b c); rewrite /cong' /cong.
    by split => //; apply coplanar_midpoint.
  exists c; rewrite /independence.Coplanar /InP.
  rewrite /cong' /cong subrr mul0mx eqxx; split; [|split]; [intuition..|].
  destruct (@another_point (Rcf_to_T R n) c) as [d cdP].
  destruct (@not_col_exists _ (Rcf_to_T_PED R n) c d) as [e HNC] => //.
  exists e, d, c => {a b cdP}.
  split; first by move => HF; apply HNC, col_permutation_3, Col__col.
  have edP : independence.Col _ (fun a b c => bet' a b c) e d d.
  + rewrite /independence.Col /bet' eqxx bet_axx.
    case: (e =P d) => [E|]; last by intuition.
    by exfalso; apply HNC; rewrite E; Col.
  have cdP : independence.Col _ (fun a b c => bet' a b c) c c d.
  + rewrite /independence.Col /bet' eqxx bet_xxa.
    case: (c =P d) => [E|]; last by intuition.
    by exfalso; apply HNC; rewrite E; Col.
  by repeat split; exists d; split.
have: (~ col a b c) by move=> HF; apply col__Col in HF. rewrite col__colI.
clear HNC; move=> HNC; destruct (@tcp R n a b c) as [x [? [? xP]]]=> //.
exists x; split; [|split]; [by []..|].
destruct xP as [e [f [g [efgP abcxP]]]]; apply <- ncol__ncolI in efgP.
destruct abcxP as [aP [bP [cP xP]]].
exists e, f, g; split; first by move => HF; apply efgP, Col__col.
have: e <> f by intro; subst; apply efgP, (@col_trivial_1 (Rcf_to_T R n)).
have gP ef_neq : forall y p, ~ col e f g -> colI e f y -> colI g p y -> g <> y
  by move => y p; rewrite col__colI; case: (g =P y) => [->|//].
have ColP := colI__Col; have Col13P := colI__Col_13.
split; first by destruct aP as [y []]; exists y; split; eauto; intuition.
split; first by destruct bP as [y []]; exists y; split; eauto; intuition.
split; first by destruct cP as [y []]; exists y; split; eauto; intuition.
by destruct xP as [y []]; exists y; split; eauto; intuition.
Qed.

End RcfTarskinD.
