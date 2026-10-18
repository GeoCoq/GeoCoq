From mathcomp Require Import ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp
Require Import fintype finset finfun bigop order.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.
From mathcomp
Require Import ring lra.

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
Proof. by rewrite /col' !subrr !mul0r. Qed.

Lemma col_perm_1 a b c : col' a b c = col' b c a.
Proof. by rewrite /col' -subr_eq0 -[RHS]subr_eq0; congr (_ == 0); ring. Qed.

Lemma col_perm_2 a b c : col' a b c = col' a c b.
Proof.
by rewrite /col' -subr_eq0 -[RHS]subr_eq0 -[LHS]oppr_eq0; congr (_ == 0); ring.
Qed.

Lemma bet__bet' a b c : bet a b c -> bet' a b c || bet' c a b.
Proof.
move=> Hb; have [<-|ab] := eqVneq a b; last by rewrite /bet' Hb (negPf ab).
by rewrite /bet' bet_axx eqxx !implybT orbT.
Qed.

Lemma col_2D_bet' a b c :
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0) ->
  (bet' a b c \/ bet' b c a \/ bet' c a b).
Proof. by move=> /col_2D [|[|]] /bet__bet' /orP[]; tauto. Qed.

Lemma col_trans x y a b c :
  x <> y -> col' x y a -> col' x y b -> col' x y c -> col' a b c.
Proof.
move=> /eqP; rewrite vector2_eq negb_and /col'.
move=> /orP[] xy /eqP Ha /eqP Hb /eqP Hc;
rewrite -subr_eq0 in xy; apply/eqP.
- have Ea : a 0 1 = y 0 1 - (x 0 1 - y 0 1) * (y 0 0 - a 0 0) / (x 0 0 - y 0 0)
    by rewrite -Ha; field.
  have Eb : b 0 1 = y 0 1 - (x 0 1 - y 0 1) * (y 0 0 - b 0 0) / (x 0 0 - y 0 0)
    by rewrite -Hb; field.
  have Ec : c 0 1 = y 0 1 - (x 0 1 - y 0 1) * (y 0 0 - c 0 0) / (x 0 0 - y 0 0)
    by rewrite -Hc; field.
  by rewrite Ea Eb Ec; field.
have Ea : a 0 0 = y 0 0 - (x 0 0 - y 0 0) * (y 0 1 - a 0 1) / (x 0 1 - y 0 1)
  by rewrite Ha; field.
have Eb : b 0 0 = y 0 0 - (x 0 0 - y 0 0) * (y 0 1 - b 0 1) / (x 0 1 - y 0 1)
  by rewrite Hb; field.
have Ec : c 0 0 = y 0 0 - (x 0 0 - y 0 0) * (y 0 1 - c 0 1) / (x 0 1 - y 0 1)
  by rewrite Hc; field.
by rewrite Ea Eb Ec; field.
Qed.

Lemma bet_symmetry : ~ bet_symmetryP Point bet'.
Proof.
move => HF; move: (HF (@c2D R) (@a2D R) (@a2D R)).
rewrite /bet' bet_xxa bet_axx !mxE /= !eqxx (eq_sym (@a2D R)) ca_neq_2D /=.
by apply /implyP.
Qed.

Lemma point_equality_decidability : point_equality_decidabilityP Point.
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

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point cong'.
Proof. exact: cong_pseudo_reflexivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. exact: cong_identity. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point cong'.
Proof. exact: cong_inner_transitivity. Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q /andP[Hb1 _] /andP[Hb2 _] ap_neq pc_neq bq_neq qc_neq HNC.
destruct (inner_pasch Hb1 Hb2) as [x [Hb3 Hb4]]=> //.
  by move=> HC ; apply HNC, col_2D_bet', col_2D'.
exists x; rewrite /bet' Hb3 Hb4 /=; case: (p =P x)=> /= [E|_].
  exfalso; apply HNC, col_2D_bet'; rewrite -E in Hb4.
  suffices: (col' a b c)=> [//|].
  apply bet_col' in Hb1; apply bet_col' in Hb2; apply bet_col' in Hb4.
  apply col_trans with q c=> //; rewrite col_perm_1 ?col_xxa // col_perm_1 //.
  by apply col_trans with a p=> //; rewrite col_perm_2 ?col_xxa // col_perm_1.
case: (q =P x)=> /= [E|_ //]; exfalso; apply HNC, col_2D_bet'.
rewrite -E in Hb3.
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
move=> HC; apply: (@POF_to_Tarski.lower_dim R 0).
by case: HC => [/andP[? _]|[/andP[? _]|/andP[? _]]];
   [left|right; left|right; right].
Qed.

Lemma upper_dim : upper_dimP Point bet' cong'.
Proof.
move=> a b c p q pq_neq _ _ _ H1 H2 H3; apply col_2D_bet'.
exact: (cong_col_2D pq_neq H1 H2 H3).
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
      case: (normv (d - c) =P 0)=> /= [->|//].
      by rewrite vector2_eq !mxE Hb1 !eqxx.
    rewrite subrr Hb1 subr0 expr0n add0r /normv congP_aux' /sqr_L2_norm_2D.
    by rewrite mxE eqxx mulr1n sqr_sqrtr // addr_ge0 ?sqr_ge0.
  by destruct (segment_construction b b c d) as [E HE]; exists E; rewrite andbT.
by destruct (segment_construction a b c d) as [E HE]; exists E; rewrite andbT.
Qed.

End RcfTarski2D.