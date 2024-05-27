(* This file proves that axiom cong_identity
   is independent from the other axioms *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.

Definition point := 'I_2.
Definition bet (a b c : point) := true.
Definition cong (a b c d : point) := true.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP point cong.
Proof. by rewrite /cong_pseudo_reflexivityP /cong. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP point cong.
Proof. by rewrite /cong_inner_transitivityP /cong. Qed.

Lemma cong_identity : ~ cong_identityP point cong.
Proof.
move=> H; suff: (@ord0 1 <> @ord_max 1) => [HF|//].
by apply HF, (H _ _ ord0); rewrite /cong.
Qed.

Lemma segment_construction : segment_constructionP point bet cong.
Proof. by move=> a b c d; exists a; rewrite /bet /cong. Qed.

Lemma five_segment : five_segmentP point bet cong.
Proof. by rewrite /five_segmentP /cong. Qed.

Lemma inner_pasch : inner_paschP point bet.
Proof.
move=> ? ? ? ? ? _ _ _ _ _ _ Hnc; exfalso.
apply Hnc; rewrite /Col /bet; intuition.
Qed.

Lemma bet_symmetry : bet_symmetryP point bet.
Proof. by rewrite /bet_symmetryP /bet. Qed.

Lemma bet_inner_transitivityP : bet_inner_transitivityP point bet.
Proof. by rewrite /bet_inner_transitivityP /bet. Qed.

Lemma lower_dim : forall n, lower_dimP point bet cong n ord0 ord0
                                       (nseq_tuple n ord_max).
Proof.
rewrite /lower_dimP /orthonormal_basis /bet /cong => n /=.
case: n => // n; rewrite !tnth_nseq; split; [|split] => //.
split; [apply big_andb_and|apply big_pairs_andb_and]; rewrite big_all;
by apply /seq.allP => ? ?; rewrite /cong // big_all; apply /seq.allP.
Qed.

Lemma upper_dim : forall n,
  upper_dimP _ bet cong n.+1 ord0 ord0 (nseq_tuple n.+1 ord_max).
Proof.
rewrite /upper_dimP /no_more_orthogonal_point /Col /bet.
by move => n; case n => //; intuition.
Qed.

Lemma euclid : euclidP point bet cong.
Proof.
by move=> ? ? ? Hnc; exfalso; apply Hnc; rewrite /Col /bet; intuition.
Qed.

Lemma continuity : continuityP point bet.
Proof. by move=> ? ? [a _]; exists a; rewrite /bet. Qed.
