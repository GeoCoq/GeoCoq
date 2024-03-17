Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp
Require Import fintype finset finfun bigop order.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.
(*Require Import complex.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

Section RfTarski2D.

Variable R : realFieldType.

Definition Point := 'rV[R]_2.
Implicit Types (a b c d : Point).

(* Definition of the counter-model *)
Definition bet' a b c :=
  bet a b c && ([ && a == b, a 0 1 == 0 & c 0 1 == 0 ] ==> (b == c)).
Definition cong' a b c d := cong a b c d.

Definition a' := (@a R 0).
Definition b' := (@b R 0).
Definition c' := (@c R 0).

Definition col' a b c :=
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0).

Lemma bet'_col_2D a b c :
  (bet' a b c \/ bet' b c a \/ bet' c a b) ->
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0).
Proof. move=> [/andP[? _]|[/andP[? _]|/andP[? _]]]; apply col_2D'; tauto. Qed.

Lemma bet_on_abscissa a b c :
  a <> b -> a 0 1 = 0 -> b 0 1 = 0 -> bet a b c -> c 0 1 = 0.
Proof.
rewrite /bet' /bet /betE; case: (a =P b)=> [//|_ /=].
case: (b =P c)=> [-> //|bc_neq /=]=> ab_neq Ha1 Hb1 /betSP'[_ Hc1 r_neq0 _].
move/eqP: Hc1; rewrite Ha1 Hb1 !subr0 eq_sym mulf_eq0=> /orP[/eqP Hr|/eqP-> //].
by move: r_neq0; rewrite Hr lt_def eqxx.
Qed.

Lemma bet_col' a b c : bet a b c -> col' a b c.
Proof. move=> ?; apply col_2D'; tauto. Qed.

Lemma col_xxa x a : col' x x a.
Proof. apply col_2D'; rewrite bet_xxa; intuition. Qed.

Lemma col_perm_1 a b c : col' a b c = col' b c a.
Proof.
apply /eqP/eqP=> /eqP H; move: (col_2D H)=> H';
apply /eqP; apply col_2D'; tauto.
Qed.

Lemma col_perm_2 a b c : col' a b c = col' a c b.
Proof.
apply /eqP/eqP=> /eqP H; move: (col_2D H)=> H'; apply /eqP; apply col_2D'.
  elim H'; clear H'; [|move=> H'; elim H'; clear H']; rewrite bet_sym; tauto.
elim H'; clear H'; [|move=> H'; elim H'; clear H']; rewrite bet_sym; tauto.
Qed.

Lemma col_2D_bet' a b c :
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0) ->
  (bet' a b c \/ bet' b c a \/ bet' c a b).
Proof.
rewrite /bet'; case: (a =P b)=> [E1|?]; case: (b =P c)=> [E2|NE];
case: (c =P a)=> [E3|?]; rewrite ?E1 ?E2 ?E3 ?bet_xxa ?bet_axx ?bet_xax ?eqxx;
rewrite ?andbT ?andbF; try solve[intuition; by []]; rewrite /=;
try solve[exfalso; apply NE; by rewrite E3 E1]; case: (a 0 1 =P 0)=> _ /=;
try solve [intuition; by []]; apply col_2D.
Qed.

Lemma col_trans x y a b c :
  x <> y -> col' x y a -> col' x y b -> col' x y c -> col' a b c.
Proof.
rewrite /col'; set c0 := x 0 0 - y 0 0; set c1 := x 0 1 - y 0 1.
move=> /eqP xy_neq; rewrite eq_sym -subr_eq0 -mulNr=> /eqP E1.
rewrite eq_sym -subr_eq0 -mulNr=> /eqP E2.
rewrite eq_sym -subr_eq0 -mulNr=> /eqP E3.
move: (upper_dim_aux E2 E1) (upper_dim_aux E3 E2).
move/eqP: E1; move/eqP: E2; move/eqP: E3=> E3 E2 E1.
set ba0 := a 0 0 - b 0 0; set ba1 := a 0 1 - b 0 1; set cb0 := b 0 0 - c 0 0;
set cb1 := b 0 1 - c 0 1; move=> E4 E5.
have: (c0 * c1 * (ba0 * cb1) == c0 * c1 * (ba1 * cb0)).
  rewrite mulrCA [c0*c1]mulrC -mulrA mulrCA mulrA E4 eq_sym.
  rewrite [X in X == _]mulrCA [c1*c0]mulrC -mulrA E5 mulrCA mulrA.
  by rewrite mulNr mulrN -mulNr -mulNr [X in _ * X]mulNr mulrN -mulNr -mulNr.
rewrite -subr_eq0 -mulrBr mulf_eq0 subr_eq0=> /orP[|//]; rewrite mulf_eq0.
move: xy_neq; rewrite -subr_eq0 vector2_eq !mxE=> NE1 NE2; move: E1 E2 E3;
move: NE2 NE1; rewrite /c0 /c1; move=> /orP[/eqP ->|/eqP ->];
rewrite eqxx /= ?orbF !mulNr !mul0r ?subr0 ?sub0r ?oppr_eq0 !mulf_eq0.
  case: (x 0 1 - y 0 1 =P 0)=> //= _ _; rewrite !subr_eq0 /ba0 /cb1 /ba1 /cb0.
  by move=> /eqP -> /eqP -> /eqP ->; rewrite subrr mulr0 mul0r eqxx.
case: (x 0 0 - y 0 0 =P 0)=> //= _ _; rewrite !subr_eq0 /ba0 /cb1 /ba1 /cb0.
by move=> /eqP -> /eqP -> /eqP ->; rewrite subrr mulr0 mul0r eqxx.
Qed.

(* Proof that the following axiom does not hold in the given model *)
Lemma bet_symmetry : ~ bet_symmetryP Point bet'.
Proof.
move => HF; move: (HF (@c2D R) (@a2D R) (@a2D R)).
rewrite /bet' bet_xxa bet_axx !mxE /= !eqxx (eq_sym (@a2D R)) ca_neq_2D /=.
by apply /implyP.
Qed.

(* Proof that the following axioms hold in the given model *)
Lemma point_equality_decidability : point_equality_decidability Point.
Proof. by move=> a b; case: (a =P b); tauto. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof.
move=> a b c d /andP[Hb1 /implyP Himp1] /andP[Hb2 _].
rewrite /bet' (bet_inner_transitivity Hb1 Hb2) /=; apply /implyP.
move=> /and3P[/eqP E1 /eqP E2 /eqP E3]; case: (b =P c)=> [//|bc_neq].
have E4 : (d 0 1 = 0) by apply (bet_on_abscissa bc_neq)=> //; rewrite -E1.
have E5 : (b = d) by apply /eqP; apply Himp1; rewrite E2 E1 E4 !eqxx.
by exfalso; apply bc_neq; apply /eqP; rewrite -E5 in Hb2; rewrite -bet_xax.
Qed.

Lemma cong_pseudo_reflexivity :
  cong_pseudo_reflexivityP Point cong'.
Proof. by unfold cong_pseudo_reflexivityP; apply cong_pseudo_reflexivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. by unfold cong_identityP; apply cong_identity. Qed.

Lemma cong_inner_transitivity :
  cong_inner_transitivityP Point cong'.
Proof. by unfold cong_inner_transitivityP; apply cong_inner_transitivity. Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q /andP[Hb1 _] /andP[Hb2 _] ap_neq pc_neq bq_neq qc_neq HNC.
destruct (inner_pasch Hb1 Hb2) as [x [Hb3 Hb4]]=> //.
  by move=> HC ; apply HNC, col_2D_bet', col_2D'.
exists x; rewrite /bet' Hb3 Hb4 /=; case: (p =P x)=> /= [E|_].
  exfalso; apply HNC, col_2D_bet'; rewrite -E in Hb4; suffices: (col' a b c)=> [//|].
  apply bet_col' in Hb1; apply bet_col' in Hb2; apply bet_col' in Hb4.
  apply col_trans with q c=> //; rewrite col_perm_1 ?col_xxa // col_perm_1 //.
  by apply col_trans with a p=> //; rewrite col_perm_2 ?col_xxa // col_perm_1.
case: (q =P x)=> /= [E|_ //]; exfalso; apply HNC, col_2D_bet'; rewrite -E in Hb3.
suffices: (col' a b c)=> [//|]; apply bet_col' in Hb1; apply bet_col' in Hb2.
apply bet_col' in Hb3; apply col_trans with p c=> //; rewrite col_perm_1;
rewrite ?col_xxa // col_perm_1 //; apply col_trans with b q=> //;
by rewrite col_perm_2 ?col_xxa // col_perm_1.
Qed.

Lemma five_segment : five_segmentP Point bet' cong'.
Proof.
move => a a' b b' c c' d d' H1 H2 H3 H4 /andP [H5 _] /andP [H6 _] H7.
by apply (@five_segment R 2 a a' b b' c c' d d').
Qed.

Lemma lower_dim : lower_dimP Point bet' a' b' c'.
Proof.
move=> H; move: H; rewrite /Col /bet' /bet /betE ab_neq bc_neq ca_neq.
rewrite /betS betR_abc betR_bca; elim (@betR_cab R 0)=> [->|->];
by rewrite !ltxx ltr01 /= ![_ && false]andbC /=; firstorder.
Qed.

Lemma upper_dim : upper_dimP Point bet' cong'.
Proof.
move=> a b c p q ? _ _ _ H1 H2 H3; apply col_2D_bet'.
move: (cong_perp H1) (cong_perp H2) (cong_perp H3); set m := (1/(1+1)) *: (p+q).
move=> HP1 HP2 HP3; move: (upper_dim_aux HP2 HP1) (upper_dim_aux HP3 HP2).
rewrite opprB; set mp0 := p 0 0 - m 0 0; set pm1 := m 0 1 - p 0 1.
set ba0 := a 0 0 - b 0 0; set ba1 := a 0 1 - b 0 1; set cb0 := b 0 0 - c 0 0;
set cb1 := b 0 1 - c 0 1; move=> E1 E2.
have: (mp0 * pm1 * (ba0 * cb1) == mp0 * pm1 * (ba1 * cb0)).
  by apply /eqP; rewrite mulrACA E1 -E2 -mulrACA [pm1* mp0]mulrC.
rewrite -subr_eq0 -mulrBr mulf_eq0 subr_eq0 mulf_eq0=> /orP[/orP[C1|C2]|->//];
by [apply upper_dim_dgc1 with p q|apply upper_dim_dgc2 with p q].
Qed.

End RfTarski2D.

Section RcfTarski2D.

Variable R : rcfType.

Implicit Types (a b c d : 'rV[R]_2).

Lemma colP a b c : col a b c <-> Col (@Point R) (@bet' R) a b c.
Proof.
split; rewrite /col /col'=> col_abc; [apply col_2D_bet', col_2D'|]=> //.
by apply col_2D, bet'_col_2D.
Qed.

Lemma ncolP a b c : ~ col a b c <-> ~ Col (@Point R) (@bet' R) a b c.
Proof. by split; move=> HF ?; apply HF, colP. Qed.

Lemma coplanarP a b c d :
  coplanar a b c d <-> Coplanar (@Point R) (@bet' R) a b c d.
Proof.
split; move=> [x [[]|[[]|[]]]]; exists x;
try solve [by left; split; apply colP];
try solve [by right; left; split; apply colP];
by right; right ; split; apply colP.
Qed.

Lemma par_strictP a b c d :
  par_strict a b c d <-> Par_strict (@Point R) (@bet' R) a b c d.
Proof.
split; [move=> [? HF]|move => [? [? [? HF]]]]; last first.
- repeat (split=> //); try (by apply coplanarP).
  by move=> [x [? ?]]; apply HF; exists x; split; apply colP.
repeat (split=> //); try (by apply coplanarP);
last by move=> [x [? ?]]; apply HF; exists x; split; apply colP.
- move => abP; apply HF; exists c; rewrite abP; split; apply colP;
  [left|right; right]; by rewrite /bet' bet_axx eqxx andTb implybT.
- move => cdP; apply HF; exists a; rewrite cdP; split; apply colP;
  [right; right|left]; by rewrite /bet' bet_axx eqxx andTb implybT.
Qed.

Lemma parP a b c d : par a b c d <-> Par (@Point R) (@bet' R) a b c d.
Proof.
split; move=> [?|[? [? [? ?]]]]; try (by left; apply par_strictP); right;
repeat (split=> //); by apply colP.
Qed.

Lemma euclid : euclidP (@Point R) (@bet' R).
Proof.
move=> a b c d p q par col ncol cop; apply parP in par; apply colP in col;
apply ncolP in ncol; apply coplanarP in cop.
by destruct (proclus par col ncol cop) as [y []]; exists y; split; apply colP.
Qed.

Lemma A10_segment_construction :
  segment_constructionP (@Point R) (@bet' R) (@cong' R).
Proof.
move=> a b c d; rewrite /bet'; case (a =P b)=> [->|_].
  case: (b 0 1 =P 0)=> [Hb1|_]; [exists (row2 (b 0 0) (normv(d - c)))|].
    rewrite bet_xxa /= /cong' congP_aux /sqr_L2_norm_2D !mxE /=; split.
      case: (normv (d - c) =P 0)=> /= [->|//]; by rewrite vector2_eq !mxE Hb1 !eqxx.
    rewrite subrr Hb1 subr0 expr0n add0r /normv congP_aux' /sqr_L2_norm_2D.
    by rewrite mxE eqxx mulr1n sqr_sqrtr // addr_ge0 ?sqr_ge0.
  by destruct (segment_construction b b c d) as [E HE]; exists E; rewrite andbT.
by destruct (segment_construction a b c d) as [E HE]; exists E; rewrite andbT.
Qed.

End RcfTarski2D.
