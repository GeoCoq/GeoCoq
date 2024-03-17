(* This file proves that axiom segment_construction
is independent from the other axioms *)

Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

(* Definition of the counter-model *)

Inductive Point := P0.
Definition Bet (A B C : Point) := False.
Definition Cong (A B C D : Point) := True.
Definition PA := P0.
Definition PB := P0.
Definition PC := P0.

(* Proof that the following axiom does not hold in the given model *)

Lemma segment_construction : ~ segment_constructionP Point Bet Cong.
Proof.
unfold segment_constructionP, Bet; intro H.
destruct (H P0 P0 P0 P0) as [E [HBet _]]; tauto.
Qed.

(* Proof that the following axioms hold in the given model *)

Lemma point_equality_decidability : point_equality_decidability Point.
Proof. unfold point_equality_decidability; destruct A, B; auto. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point Bet.
Proof. unfold bet_inner_transitivityP; tauto. Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point Cong.
Proof. unfold cong_pseudo_reflexivityP, Cong; auto. Qed.

Lemma cong_identity : cong_identityP Point Cong.
Proof. unfold cong_identityP; destruct A, B; auto. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point Cong.
Proof. unfold cong_inner_transitivityP; tauto. Qed.

Lemma inner_pasch : inner_paschP Point Bet.
Proof. unfold inner_paschP; tauto. Qed.

Lemma bet_symmetry : bet_symmetryP Point Bet.
Proof. unfold bet_symmetryP; tauto. Qed.

Lemma euclid : euclidP Point Bet.
Proof. unfold euclidP; tauto. Qed.

Lemma five_segment : five_segmentP Point Bet Cong.
Proof. unfold five_segmentP; tauto. Qed.

Lemma lower_dim : lower_dimP Point Bet PA PB PC.
Proof. unfold lower_dimP, Col, Bet; tauto. Qed.

Lemma upper_dim : upper_dimP Point Bet Cong.
Proof. unfold upper_dimP; destruct P, Q; tauto. Qed.

Lemma continuity : continuityP Point Bet.
Proof. unfold continuityP, Bet; firstorder. Qed.
