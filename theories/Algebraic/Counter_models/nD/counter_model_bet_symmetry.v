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
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section RfTarskinD.

Variable n : nat.
Variable R : realFieldType.

Definition Point := 'rV[R]_n.+1.
Implicit Types (a b c d : Point).

Definition bet' a b c :=
  bet a b c && ((a == b) ==> (b == c)).
Definition cong' a b c d := cong a b c d.

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
destruct (inner_pasch' Hb1 Hb2) as [x [Hb3 Hb4]]=> //.
  move=> [HC|[HC|HC]]; apply HNC; rewrite /independence.Col /bet' HC;
  rewrite [c == a]eq_sym; case: (a =P b)=> [<-|_]; case: (a =P c)=> [->|_];
  case: (b =P c)=> [<-|_]; rewrite ?bet_axx ?bet_xxa !andbT ?andbF; intuition.
exists x; rewrite /bet' /bet Hb3 Hb4 !orbT /=; move: Hb3 Hb4.
rewrite betS_neq12 betS_neq23=> /andP[/andP[Hb3 /eqP xb_neq] /eqP px_neq].
rewrite betS_neq12 betS_neq23=> /andP[/andP[Hb4 /eqP xa_neq] /eqP qx_neq].
move: px_neq qx_neq; case: (p =P x)=> [//|_]; case: (q =P x)=> [//|_ //=].
Qed.

Lemma bet_symmetry : ~ bet_symmetryP Point bet'.
Proof.
move => HF; move: (HF (const_mx 1) (const_mx 0) (const_mx 0)).
rewrite /bet' bet_axx bet_xxa eqxx eq_sym.
move: onemx_neq0; case: (const_mx 0 =P const_mx 1) => //= _ _.
by apply /implyP.
Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof.
move=> a b c d; rewrite /bet'; case: (a =P b)=> [-> /andP[_ /eqP->]|_] /=;
rewrite ?bet_xax ?bet_xxa; first by move=> /andP[/eqP -> _]; rewrite eqxx.
by rewrite !andbT=> ? /andP[? _]; apply bet_inner_transitivity with d.
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

Lemma ColP a b c : @col R n a b c <-> independence.Col _ (@bet' (n.+1) R) a b c.
Proof.
rewrite /col /Col /bet'; case: (a =P b) => [->|] /=.
- case: (b =P c) => [->|] /=; first by rewrite eqxx andbT bet_axx; intuition.
  by rewrite bet_axx bet_xxa bet_xax (eq_sym c) => /eqP/negPf ->; intuition.
rewrite (eq_sym c); case: (b =P c) => [-> /eqP/negPf E|] /=.
- by rewrite bet_axx bet_xxa bet_xax eq_sym E; intuition.
case: (a =P c) => /= [->|]; rewrite !andbT ?andbF.
- by rewrite bet_xxa bet_axx bet_xax eq_sym => /eqP/negPf -> _; intuition.
by case: (bet a b c); case: (bet b c a); case: (bet c a b) => _ _ _; intuition.
Qed.

Lemma col__colI a b c : @col R n a b c <-> colI a b c.
Proof.
by rewrite /col /colI; case: (bet a b c);
case: (bet b c a); case: (bet c a b); intuition.
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
