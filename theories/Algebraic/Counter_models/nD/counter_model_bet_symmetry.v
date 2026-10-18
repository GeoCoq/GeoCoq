From mathcomp Require Import ssreflect.
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
Require Import GeoCoq.Algebraic.POF_to_Tarski.
Require Import GeoCoq.Algebraic.Counter_models.nD.dimensional_axioms.

Section RfTarskinD.

Variable n : nat.
Variable R : realFieldType.

Definition Point := 'rV[R]_n.+1.
Implicit Types (a b c d : Point).

Definition bet' a b c :=
  bet a b c && ((a == b) ==> (b == c)).
Definition cong' a b c d := cong a b c d.

Lemma bet__bet' a b c : bet a b c -> bet' a b c || bet' c a b.
Proof.
move=> Hb; have [<-|ab] := eqVneq a b; last by rewrite /bet' Hb (negPf ab).
by rewrite /bet' bet_axx eqxx implybT orbT.
Qed.

Lemma bet3__Col a b c :
  bet a b c \/ bet b c a \/ bet c a b -> independence.Col _ bet' a b c.
Proof.
move=> HC [H1 [H2 H3]];
by case: HC => [/bet__bet'|[/bet__bet'|/bet__bet']] /orP[];
   [apply: H1|apply: H3|apply: H2|apply: H1|apply: H3|apply: H2].
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
by apply (@five_segment R n.+1 a a' b b' c c' d d').
Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q /andP[Hb1 _] /andP[Hb2 _] Hap Hpc Hbq Hqc HNC.
rewrite bet_betS // in Hb1; rewrite bet_betS // in Hb2.
have [x []] := inner_pasch' Hb1 Hb2 (fun HC => HNC (bet3__Col HC)).
rewrite betS_neq12 [betS q x a]betS_neq12 => /andP[Hb3 px] /andP[Hb4 qx].
by exists x; rewrite /bet' /bet Hb3 Hb4 (negPf px) (negPf qx) !orbT.
Qed.

Lemma bet_symmetry : ~ bet_symmetryP Point bet'.
Proof.
move=> HF; have := HF (const_mx 1) (const_mx 0) (const_mx 0).
rewrite /bet' bet_axx bet_xxa eqxx implybT (negPf onemx_neq0).
by move=> /(_ isT).
Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof.
move=> a b c d; rewrite /bet'; case: (a =P b)=> [-> /andP[_ /eqP->]|_] /=;
rewrite ?bet_xax ?bet_xxa; first by move=> /andP[/eqP -> _]; rewrite eqxx.
by rewrite !andbT=> ? /andP[? _]; apply bet_inner_transitivity with d.
Qed.

End RfTarskinD.

Section RcfTarskinp2D.

Variable n : nat.
Variable R : realFieldType.

Definition o := o n R.

Definition i := i n R.

Definition basis := basis n R.

Lemma lower_dim :
  lower_dimP (@Point n.+1 R) (@bet' n.+1 R) (@cong' n.+1 R) n.+2 o i basis.
Proof.
move: (dimensional_axioms.lower_dim n R) => [oi_nz [_ ldP]].
split => //; split => //; rewrite /bet' /o /i.
rewrite nth_basis // bet_o_i_basis_nth0 /=.
suff -> : (dimensional_axioms.i n R == dimensional_axioms.o n R) = false by [].
apply /negbTE/eqP; move: (betS_o_i_basis_nth0 n R).
by rewrite betS_neq12 => /andP[_ /eqP].
Qed.

Lemma upper_dim :
  upper_dimP (@Point n.+1 R) (@bet' n.+1 R) (@cong' n.+1 R) n.+2 o i basis.
Proof.
have bet'P : forall a b c, @betS R n.+2 a b c -> bet' a b c.
- move=> a b c; rewrite /bet' /bet betS_neq12 => /andP[-> /negPf->].
  by rewrite orbT.
move => p ob1P [_ [_ [HC1 HC2]]] pP; apply bet'P, upper_dimS => //.
- by rewrite nth_new_basis //; apply i_neq_basis_nth0.
- by rewrite nth_new_basis // bet_o_i_basis_nth0.
Qed.

End RcfTarskinp2D.

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

Lemma ColP a b c : @col R n a b c <-> independence.Col _ (@bet' (n.+1) R) a b c.
Proof.
split=> [|HC]; first exact: bet3__Col.
case Hb1: (bet a b c); first by left.
case Hb2: (bet b c a); first by right; left.
case Hb3: (bet c a b); first by right; right.
by exfalso; apply: HC; rewrite /bet' Hb1 Hb2 Hb3.
Qed.

Lemma CopP a b c d : cop a b c d -> Coplanar _ (@bet' (n.+1) R) a b c d.
Proof.
move => [e [f [g [HNC [aP [bP [cP dP]]]]]]]; exists e, f, g.
split; first by move: HNC; rewrite -ColP col__colI.
suff: forall a b c d, inplane a b c d ->
                      InP _ (@bet' (n.+1) R) a b c d by auto.
move => {e f g HNC aP bP cP dP} {}a {}b {}c {}d.
by move => [x [Hc1 Hc2]]; exists x; rewrite -!ColP !col__colI.
Qed.

Lemma euclid : euclidP (@Point (n.+1) R) (@bet' (n.+1) R) (@cong' (n.+1) R).
Proof.
move => a b c HNC; destruct (@tcp R n a b c) as [x [abP [acP HC]]];
  first by rewrite -col__colI ColP.
by exists x; rewrite /cong'; split; [|split] => //; apply CopP.
Qed.

End RcfTarskinD.