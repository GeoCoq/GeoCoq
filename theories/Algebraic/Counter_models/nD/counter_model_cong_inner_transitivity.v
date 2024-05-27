(* This file proves that axiom cong_inner_transitivity
   is independent from the other axioms *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp Require Import tuple fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix.
From mathcomp Require Import zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.

Section counter_model_cong_inner_transitivity.

Definition point := 'I_2.

Definition bet (a b c : point) := (a == b) || (b == c).
Definition cong (a b c d : point) := (a == b) || ((b == c) && (a == d)).

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP point cong.
Proof. by move=> ? ?; rewrite /cong_pseudo_reflexivityP /cong !eqxx orbT. Qed.

Lemma cong_inner_transitivity : ~ cong_inner_transitivityP point cong.
Proof.
move=> HF; have: ((@ord0 1 == @ord_max 1) = false) => [|H]; first by apply /eqP.
move: (HF ord0 ord_max ord_max ord_max ord_max ord0); clear HF.
by rewrite /cong !eqxx orbT /= H => HF; have: false by apply HF.
Qed.

Lemma cong_identity : cong_identityP point cong.
Proof.
by rewrite /cong_identityP /cong=> ? ? ? /orP[/eqP->|/andP[/eqP-> /eqP->]].
Qed.

Lemma segment_construction : segment_constructionP point bet cong.
Proof.
rewrite /segment_constructionP /bet /cong=> ? b.
exists b; rewrite eqxx; intuition auto with bool.
Qed.

Lemma five_segment : five_segmentP point bet cong.
Proof.
move=> ? ? ? ? ? ? ? ? /orP[/eqP-> //|/andP[/eqP<- /eqP<-]] Hc2 Hc3 Hc4.
by move=> /orP[/eqP-> //|/eqP <-] /orP[/eqP-> //|/eqP <-].
Qed.

Lemma inner_pasch : inner_paschP point bet.
Proof. by move=> ? ? ? ? ? /orP[/eqP->|/eqP->]. Qed.

Lemma bet_symmetry : bet_symmetryP point bet.
Proof. by move=> ? ? ? /orP[/eqP->|/eqP->]; rewrite /bet eqxx ?orbT. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP point bet.
Proof.
move=> ? ? ? ? /orP[/eqP->|/eqP->] /orP[/eqP->|/eqP->];
by rewrite /bet eqxx ?orbT.
Qed.

Lemma lower_dim :  forall n, lower_dimP point bet cong n ord0 ord0
                                       (nseq_tuple n ord_max).
Proof.
rewrite /lower_dimP /orthonormal_basis /bet /cong => n /=.
case: n => // n; rewrite !tnth_nseq; split; [|split] => //.
split; [apply big_andb_and|apply big_pairs_andb_and]; rewrite big_all.
- by rewrite eqxx; apply /seq.allP.
apply /seq.allP => i iP; rewrite big_all; apply /seq.allP => j jP.
by rewrite !tnth_nseq eqxx.
Qed.

Lemma upper_dim : forall n,
  upper_dimP _ bet cong n.+1 ord0 ord0 (nseq_tuple n.+1 ord_max).
Proof.
move => n p; case: n => // [[HNC _]|n]; first by apply HNC; rewrite /bet eqxx.
rewrite /no_more_orthogonal_point /orthonormal_basis !tnth_nseq /bet.
case: p => p; case: p => [pP|p] ; [|case: p => // pP].
- by rewrite (@ord_inj _ (Ordinal pP) ord0) // eqxx orbT.
by rewrite (@ord_inj _ (Ordinal pP) ord_max).
Qed.

Lemma cong_axay a b c : cong a b a c -> a = b.
Proof. by move=> /orP[/eqP->|/andP[/eqP-> ?]]. Qed.

Lemma euclid : euclidP point bet cong.
Proof.
move=> a b c Hnc; exfalso; apply Hnc; rewrite /Col /bet; clear Hnc.
case: a => []; case: b => []; case: c => [].
move=> [|[|//]] pa; [rewrite (@ord_inj _ (Ordinal pa) 0) //|].
  move=> [|[|//]] pb; [rewrite (@ord_inj _ (Ordinal pb) 0) ?eqxx; intuition|].
  move=> [|[|//]] pc; [rewrite (@ord_inj _ (Ordinal pc) 0) ?eqxx; intuition|].
  by rewrite 2?(@ord_inj _ (Ordinal _) 1) ?eqxx; intuition.
move=> [|[|//]] pb; [|rewrite 2?(@ord_inj _ (Ordinal _) 1) ?eqxx; intuition].
rewrite (@ord_inj _ (Ordinal pa) 1) 1?(@ord_inj _ (Ordinal pb) 0) //.
move => [|[|//]] pc; [rewrite (@ord_inj _ (Ordinal _) 0) ?eqxx; intuition|].
by rewrite (@ord_inj _ (Ordinal pc) 1) ?eqxx; intuition.
Qed.

Lemma continuity : continuityP point bet.
Proof.
intros ? ? [a Ha]; exists a => x y Hx Hy Hf1 _ Hf2.
by move: (Ha x y Hx Hy) Hf1 Hf2 => /orP[/eqP->|/eqP->].
Qed.

End counter_model_cong_inner_transitivity.
