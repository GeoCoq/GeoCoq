Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section RfTarskinD.

Variable n : nat.
Variable R : realFieldType.

Definition Point := 'rV[R]_(2+n).

Implicit Types (a b c d : Point).

Definition head (v : 'rV[R]_(2+n)) : R := v 0 (@lshift 1 (1+n) 0).

Definition behead (v : 'rV[R]_(2+n)) := col' (@lshift 1 (1+n) 0) v.

Definition bet' a b c :=
  bet (head a)%:M (head b)%:M (head c)%:M &&
  bet (behead a) (behead b) (behead c).

Definition cong' a b c d := cong a b c d.

Lemma row2_cong_nD (a b c d :'rV[R]_2) :
  cong (to_nD n a) (to_nD n b) (to_nD n c) (to_nD n d) = cong a b c d.
Proof.
rewrite /cong /to_nD !opp_row_mx !add_row_mx subr0.
by rewrite !tr_row_mx !mul_row_col mul0mx !addr0.
Qed.

Lemma to_nD_head (a b : R) : head (to_nD n (row2 a b)) = a.
Proof.
have: (forall v, head v = v 0 (@lshift 2 n 0))=> [?|->];
by rewrite ?row_mxEl /row2 ?mxE //= /head !lshift0.
Qed.

Lemma to_nD_behead (a b : R) :
  behead (to_nD n (row2 a b)) = row_mx (@const_mx R 1 1 b) (const_mx 0).
Proof.
have: (forall v, behead v = col' (@lshift 2 n 0) v)=> [//|->].
apply /matrixP=> i j; case: i => [] [|//] ? /=; rewrite col'Kl.
by rewrite !mxE split1 /oapp; case: (unlift 0 j)=> //; rewrite !mxE.
Qed.

Lemma row_mx_head (v1 : 'M_1) (v2 : 'rV[R]_(1 + n)) :
  (head (row_mx v1 v2))%:M = v1.
Proof.
by rewrite /head /row_mx !mxE lshift0 split1 /oapp unlift_none -mx11_scalar.
Qed.

Lemma row_mx_behead (v1 : 'M_1) (v2 : 'rV[R]_(1 + n)) :
  behead (row_mx v1 v2) = v2.
Proof.
apply /matrixP=> i; case: i => [] [|//] ? /=; rewrite /behead col'Kl => j.
rewrite /row_mx mxE; case: (@fintype.splitP (predn 1) (1+n) j)=> [[] //|/= k].
by move=> eq_jk; have: (j = k)=> [|-> //]; move: eq_jk; apply ord_inj.
Qed.

Lemma eq_head_behead v1 v2 :
  v1 == v2 = (head v1 == head v2) && (behead v1 == behead v2).
Proof.
apply /eqP; case: (head v1 =P head v2) => [|HF H]; last by apply HF; rewrite H.
case: (behead v1 =P behead v2) => [/=|HF _ H]; last by apply HF; rewrite H.
move=> beheadP headP; apply /rowP => i; case: (@fintype.splitP 1 (1+n) i).
  by move=> i0 iP; move: headP; rewrite /head; have: (i = lshift (1+n) i0);
  [apply ord_inj; rewrite iP|]; rewrite ord1 lshift0 // => ->.
move=> i1 iP; move/rowP/(_ i1): beheadP; have: (i = rshift 1 i1) => [|->];
[by apply ord_inj; rewrite iP|rewrite /behead lshift0 !mxE].
by rewrite (_ : lift _ _ = rshift 1%nat i1); last exact/val_inj.
Qed.

Lemma bet_bet' a b c : bet a b c -> bet' a b c.
Proof.
rewrite /bet' {1}/bet betS_neq13; case: (a =P c)=> [->|/eqP neq_ac].
  by rewrite betE_xax andbF orbF => /eqP ->; rewrite !bet_axx.
rewrite /betE; case: (a =P b)=> [->|/eqP neq_ab]; first by rewrite !bet_xxa.
case: (b =P c)=> [->|/eqP neq_bc /=]; first by rewrite !bet_axx.
rewrite andbT /bet /betE /betS eq_head_behead => /andP[/andP[headP beheadP] bP].
have: (@eq_op (GRing.Zmodule.eqType (matrix_zmodType R 1 1))
              ((head b)%:M - (head a)%:M)
              (betR a b c *: ((head c)%:M - (head a)%:M))).
  by apply /eqP/rowP => i; move/eqP: headP; rewrite ord1 /head !mxE eqxx.
have: (behead b - behead a == betR a b c *: (behead c - behead a)).
  by apply /eqP/rowP => i; move/eqP/rowP/(_ i): beheadP; rewrite /behead !mxE.
case: (head c =P head a) => [eq_hd_ac|/eqP neq_hd_ac] behead_betR head_betR.
  move: neq_ac; rewrite eq_sym eq_head_behead eq_hd_ac eqxx /= => ?.
  move: eq_hd_ac headP; rewrite /head !mxE => ->; rewrite !subrr mulr0.
  have: (betR (behead a) (behead b) (behead c) = betR a b c) => [|->].
    by apply ratio_eq; rewrite ?subr_eq0.
  by rewrite subr_eq0 => /eqP ->; rewrite eqxx behead_betR bP /= orbC.
have: (betR (head a)%:M (head b)%:M (head c)%:M = betR a b c) => [|->].
  apply ratio_eq; rewrite //; apply /eqP/rowP; move=> H; move: neq_hd_ac.
  by move/(_ 0): H; rewrite !mxE eqxx !mulr1n -subr_eq0 => ->; rewrite eqxx.
rewrite head_betR bP !orbT; case: (behead c =P behead a) => [eq_bh_ac|/eqP ?].
  suff: (behead a = behead b) => [<-|]; first by rewrite eq_bh_ac eqxx.
  apply /rowP => i; move/eqP/rowP/(_ i): beheadP; move/rowP/(_ i): eq_bh_ac;
  rewrite /behead !mxE=> ->; rewrite subrr mulr0; move=> /eqP.
  by rewrite subr_eq0 => /eqP ->.
have: (betR (behead a) (behead b) (behead c) = betR a b c) => [|->];
by rewrite ?behead_betR ?bP ?orbT //; apply ratio_eq; rewrite ?subr_eq0.
Qed.

Definition a2D : 'rV[R]_2 := row2 0 1.
Definition b2D : 'rV[R]_2 := row2 1 1.
Definition c2D : 'rV[R]_2 := row2 (1+1) (1+1).
Definition d2D : 'rV[R]_2 := row2 1 (1+1).
Definition d'2D : 'rV[R]_2 := row2 1 0.

Definition a := to_nD n a2D.
Definition b := to_nD n b2D.
Definition c := to_nD n c2D.
Definition d := to_nD n d2D.
Definition d' := to_nD n d'2D.

Lemma bet'_abc : bet' a b c.
Proof.
rewrite /bet' !to_nD_head !to_nD_behead bet_xxa andbT /bet /betS /betR.
rewrite -scalemx1 -{2}[1%:M]scalemx1 -[(1+1)%:M]scalemx1 /ratio -!scalerBl.
rewrite -addrA subr0; case: pickP=> [x _|HF]; [|move: (HF 0)]; rewrite scale0r;
rewrite ?ord1 !mxE eqxx !mulr1 ?scalerA ?subr0 ?mul1r 1?mulrC ?divff;
rewrite ?add11_neq0 // scale1r eqxx /=.
by rewrite orbC invf_lt1 ?invr_gt0 -1?{3}[1]add0r !addr_gt0 ?ltr_add2r ?ltr01.
Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point cong'.
Proof. move => a b; rewrite /cong'; apply cong_pseudo_reflexivity. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point cong'.
Proof. move => a b c d e f; rewrite /cong'; apply cong_inner_transitivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. move => a b c; rewrite /cong'; apply cong_identity. Qed.

Lemma five_segment : ~ five_segmentP Point bet' cong'.
Proof.
have: (a <> b) by apply /eqP; rewrite row2_eq_nD eq_sym oner_eq0.
move: bet'_abc=> ? ? H; absurd (cong' c d c d'); [|apply H with a a b b];
rewrite // /a /b /c /d /d' /a2D /b2D /c2D /d2D /d'2D /cong' ?row2_cong_nD;
rewrite ?congP_aux /sqr_L2_norm_2D /row2 ?mxE /= ?subrr ?add2r_eq -?addrA;
rewrite ?subrr ?subr0 ?addr0 ?sub0r ?sqrrN ?expr2 ?mulr0 ?mulr1 ?eqxx //.
by apply /negP; rewrite eq_sym mulf_eq0 negb_or add11_neq0.
Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q /andP[Hb11 Hb12] /andP[Hb21 Hb22] _ _ _ _ Hnc.
destruct (inner_pasch_gen Hb11 Hb21) as [x1 [Hx1 Hx2]].
destruct (inner_pasch_gen Hb12 Hb22) as [x2 [Hx3 ?]].
by exists (row_mx x1 x2); rewrite /bet' row_mx_head row_mx_behead Hx1 Hx2 Hx3.
Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof. by move => a b c /andP[? ?]; apply /andP; split; rewrite bet_sym. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof.
by move=> a b c d /andP[Hb11 Hb12] /andP[Hb21 Hb22]; rewrite /bet';
rewrite (bet_inner_transitivity Hb11 Hb21) (bet_inner_transitivity Hb12 Hb22).
Qed.

End RfTarskinD.

Section RcfTarskinD.

Variable n : nat.
Variable R : rcfType.

Lemma segment_construction :
  segment_constructionP (Point n R) (@bet' n R) (@cong' n R).
Proof.
move=> a b c d _; destruct (segment_construction a b c d) as [x [Hb Hc]].
by exists x; split; first by apply bet_bet'.
Qed.

Lemma col__colI a b c : @col R n a b c <-> colI a b c.
Proof.
by rewrite /col /colI; case: (bet a b c);
case: (bet b c a); case: (bet c a b); intuition.
Qed.

Lemma Col_Col a b c :
  @Col (Rcf_to_T R n) a b c -> independence.Col _ (@bet' n R) a b c.
Proof.
move => [|[|]]; rewrite /Bet /= /independence.Col => Hb;
rewrite (bet_bet' Hb); intuition.
Qed.

Lemma euclid : euclidP (Point n R) (@bet' n R) (@cong' n R).
Proof.
move => a b c HNC; destruct (@tcp R n a b c) as [x [abP [acP HCop]]].
- rewrite -col__colI /col; move => [|[|]] Hb; apply HNC;
  by rewrite /independence.Col (bet_bet' Hb); intuition.
exists x; rewrite /cong'; split; [|split] => // {abP acP}.
have : @Coplanar (Rcf_to_T R n) a b c x.
- move: HCop => [e [f [g [efgP [aP [bP [cP xP]]]]]]].
  rewrite -Cop__Coplanar; exists e, f, g.
  split; [by move: efgP; rewrite -col__colI|split; [|split; [|split]]];
  [destruct aP as [y [Hc1 Hc2]]|destruct bP as [y [Hc1 Hc2]]|
   destruct cP as [y [Hc1 Hc2]]|destruct xP as [y [Hc1 Hc2]]]; exists y;
  by move: Hc1 Hc2; rewrite -!col__colI.
move => [y [|[|]]] [Hc1 Hc2]; [exists a, b, c|exists c, a, b|exists b, c, a].
- split => //; split; [|split; [|split]].
  + exists a; rewrite /independence.Col.
    suff: bet' b a a /\ bet' c a a by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + exists b; rewrite /independence.Col.
    suff: bet' a b b /\ bet' c b b by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + exists b; rewrite /independence.Col.
    suff: bet' a b b /\ bet' b c c by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + by exists y; split; apply Col_Col.
- split; first by move: HNC; rewrite /independence.Col; intuition.
  split; [|split; [|split]].
  + exists a; rewrite /independence.Col.
    suff: bet' b a a /\ bet' c a a by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + exists a; rewrite /independence.Col.
    suff: bet' c a a /\ bet' a b b by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + exists c; rewrite /independence.Col.
    suff: bet' a c c /\ bet' b c c by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + by exists y; split; apply Col_Col; Col.
- split; first by move: HNC; rewrite /independence.Col; intuition.
  split; [|split; [|split]].
  + exists b; rewrite /independence.Col.
    suff: bet' b a a /\ bet' c b b by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + exists b; rewrite /independence.Col.
    suff: bet' c b b /\ bet' a b b by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + exists c; rewrite /independence.Col.
    suff: bet' a c c /\ bet' b c c by intuition.
    by split; apply bet_bet'; rewrite bet_axx.
  + by exists y; split; apply Col_Col.
Qed.

End RcfTarskinD.
