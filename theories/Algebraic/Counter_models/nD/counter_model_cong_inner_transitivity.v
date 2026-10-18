From mathcomp Require Import ssreflect.
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
move=> /(_ ord0 ord_max ord_max ord_max ord_max ord0).
by rewrite /cong !eqxx orbT => /(_ isT isT).
Qed.

Lemma cong_identity : cong_identityP point cong.
Proof.
by rewrite /cong_identityP /cong=> ? ? ? /orP[/eqP->|/andP[/eqP-> /eqP->]].
Qed.

Lemma segment_construction : segment_constructionP point bet cong.
Proof.
by move=> a b c d; exists b; rewrite /bet /cong !eqxx orbT.
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
case: p => [[|[|//]] pP] _ _ H; last by exfalso; apply: H; apply: val_inj.
by apply/orP; right; apply/eqP; apply: val_inj.
Qed.

Lemma cong_axay a b c : cong a b a c -> a = b.
Proof. by move=> /orP[/eqP->|/andP[/eqP-> ?]]. Qed.

Lemma euclid : euclidP point bet cong.
Proof.
move=> a b c Hnc; exfalso; apply: Hnc.
have: [|| a == b, b == c | c == a].
  by move: a b c => [[|[|//]] ?] [[|[|//]] ?] [[|[|//]] ?].
rewrite /bet => + [H1 [H2 _]].
by case/or3P => E; [apply: H1|apply: H1|apply: H2]; rewrite E ?orbT.
Qed.

Lemma continuity : continuityP point bet.
Proof.
intros ? ? [a Ha]; exists a => x y Hx Hy Hf1 _ Hf2.
by move: (Ha x y Hx Hy) Hf1 Hf2 => /orP[/eqP->|/eqP->].
Qed.

End counter_model_cong_inner_transitivity.