From mathcomp Require Import ssreflect.
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
Proof. exact: inner_pasch. Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof. exact: bet_symmetry. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof. exact: bet_inner_transitivity. Qed.

Definition a' := (@a R 0).
Definition b' := (@b R 0).
Definition c' := (@c R 0).

Lemma lower_dim : lower_dimP Point bet' a' b' c'.
Proof. exact: (@POF_to_Tarski.lower_dim R 0). Qed.

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