(* This file proves that axiom cong_pseudo_reflexivity
is independent from the other axioms *)
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

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section rfTarskinD.

Variable n : nat.
Variable R : realFieldType.

Definition Point := 'rV[R]_(n.+1).
Implicit Types (a b c d : Point).

Definition cong' a b c d := a == b.
Definition bet' a b c := bet a b c.

Lemma onemx_neq0 :
  @const_mx (Num.RealField.sort R) (S O) (S n) 0 !=
  @const_mx (Num.RealField.sort R) (S O) (S n) 1.
Proof.
by apply/eqP=> /matrixP/(_ 0 0)/eqP; rewrite /const_mx !mxE eq_sym oner_eq0.
Qed.

Lemma cong_pseudo_reflexivity : ~ cong_pseudo_reflexivityP Point cong'.
Proof.
move=> HF; move: onemx_neq0 (HF (const_mx 0) (const_mx 1)).
by rewrite /cong'; case: (const_mx 0 =P const_mx 1).
Qed.

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
destruct (@inner_pasch' R (n.+1) a b c p q) as [x [Hb3 Hb4]];
rewrite -?bet_betS // /bet' /bet; last by exists x; rewrite Hb3 Hb4 !orbT.
move=> HF; apply HNC; rewrite /Col /bet'; move=> [Hb3 [Hb4 Hb5]]; tauto.
Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof. unfold bet_symmetryP; apply bet_symmetry. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof. unfold bet_inner_transitivityP; apply bet_inner_transitivity. Qed.

End rfTarskinD.

Section rcfTarskinD.

Variable n : nat.
Variable R : rcfType.

Lemma ColP a b c : @col R n a b c <-> independence.Col _ (@bet' (n.+1) R) a b c.
Proof.
rewrite /Col /bet' /col.
by case: (bet a b c); case: (bet b c a); case: (bet c a b); intuition.
Qed.

Lemma euclid : euclidP (@Point (n.+1) R) (@bet' (n.+1) R) (@cong' (n.+1) R).
Proof.
move => a b c HNC; exists a; rewrite /cong'; split; [|split] => //.
exists a, b, c; split => // {HNC}.
split; first by exists a; rewrite -!ColP /col !bet_xxa; intuition.
split; first by exists b; rewrite -!ColP /col !bet_xxa; intuition.
split; first by exists a; rewrite -!ColP /col !bet_xxa; intuition.
by exists a; rewrite -!ColP /col !bet_xxa; intuition.
Qed.

End rcfTarskinD.
