(* This file proves that axiom cong_pseudo_reflexivity
is independent from the other axioms *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp
Require Import fintype finset finfun bigop order.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.
From mathcomp Require Import tuple fintype bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.counter_model_cong_pseudo_reflexivity.
Require Import GeoCoq.Algebraic.POF_to_Tarski.
Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

Section Tarski2D.

Variable R : realFieldType.

Definition Point := 'rV[R]_2.
Implicit Types (a b c d : Point).

Definition cong' a b c d := a == b.
Definition bet' a b c := bet a b c.

Lemma point_equality_decidability : point_equality_decidabilityP Point.
Proof. by move => a b; case: (a =P b); tauto. Qed.

Lemma cong_pseudo_reflexivity : ~ cong_pseudo_reflexivityP Point cong'.
Proof. apply counter_model_cong_pseudo_reflexivity.cong_pseudo_reflexivity. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point cong'.
Proof. by move=> a b; rewrite /cong'. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. by rewrite /cong'; move=> a b _ /eqP ab_eq. Qed.

Lemma segment_construction : segment_constructionP Point bet' cong'.
Proof. by move=> a b; exists b; rewrite /bet' /cong' bet_axx eqxx. Qed.

Lemma five_segment : five_segmentP Point bet' cong'.
Proof. by move=> ? ? ? ? ? ? ? ?; rewrite /cong'=> /eqP ->. Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q Hb1 Hb2 ? ? ? ? HNC.
destruct (@inner_pasch _ _ a b c p q) as [x [Hb3 Hb4]]; rewrite -?bet_betS //.
by exists x; rewrite /bet'.
Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof. unfold bet_symmetryP; apply bet_symmetry. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof. unfold bet_inner_transitivityP; apply bet_inner_transitivity. Qed.

Definition a' := (@a R 0).
Definition b' := (@b R 0).
Definition c' := (@c R 0).

Lemma lower_dim : lower_dimP Point bet' a' b' c'.
Proof.
rewrite /lower_dimP /Col /bet' /bet /betE ab_neq bc_neq ca_neq /= => H; move: H.
rewrite /betS betR_abc betR_bca; elim ((@betR_cab R 0))=> [->|->];
rewrite !ltxx ltr01 /= ![_ && false]andbC /=; firstorder.
Qed.

Lemma upper_dim : upper_dimP Point bet' cong'.
Proof.
rewrite /cong' => a b c p q ? ? ? ? /eqP -> /eqP -> /eqP ->.
by rewrite /Col /bet' bet_axx; left.
Qed.

End Tarski2D.

Section rcfTarski2D.

Variable R : rcfType.

Lemma euclid : euclidP (@Point R) (@bet' R).
Proof.
move => a b c d p q abcdP abpP abqP cdpqP.
destruct (@proclus R 0 a b c d p q) as [y [pqyP cdyP]];
[..|exists y]; [move => {abpP abqP cdpqP}|intuition..].
elim abcdP; [move => {abcdP} [abcdP niP]; left|intuition].
split; [intuition| move => [x xP]; apply niP; exists x; intuition].
Qed.

End rcfTarski2D.
