(* This file proves that axiom bet_inner_transitivity
is independent from the other axioms *)

Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

(* Definition of the counter-model *)

Inductive Point := P0 | P1 | P2.
Definition Bet (A B C : Point) := (A = B) \/ (A = C) \/ (B = C).
Definition Cong (A B C D : Point) :=
  ((A = B) /\ (C = D)) \/ ((A <> B) /\ (C <> D)).
Definition PA := P0.
Definition PB := P1.
Definition PC := P2.

(* Proof that the following axiom does not hold in the given model *)
Lemma bet_inner_transitivity : ~ bet_inner_transitivityP Point Bet.
Proof.
unfold bet_inner_transitivityP, Bet.
intro H; elim (H P0 P1 P2 P1); intuition discriminate.
Qed.

(* Proof that the following axioms hold in the given model *)

Lemma point_equality_decidability : point_equality_decidabilityP Point.
Proof.
unfold point_equality_decidabilityP;
destruct A, B; try tauto; right; discriminate.
Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point Cong.
Proof.
unfold cong_pseudo_reflexivityP, Cong; destruct A, B; intuition discriminate.
Qed.

Lemma cong_identity : cong_identityP Point Cong.
Proof. unfold cong_identityP, Cong; tauto. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point Cong.
Proof. unfold  cong_inner_transitivityP, Cong; tauto. Qed.

Lemma inner_pasch : inner_paschP Point Bet.
Proof. unfold inner_paschP, Bet; intuition. Qed.

Lemma bet_symmetry : bet_symmetryP Point Bet.
Proof. unfold bet_symmetryP, Bet; intuition. Qed.

Lemma col_alt_def : forall A B C, Col Point Bet A B C <->
  A = B \/ B = C \/ A = C.
Proof.
split.
unfold Col.
intros [? | [? | ?]];
destruct H as [? | [? | ?]]; subst ; tauto.
unfold Col, Bet.
tauto.
Qed.

Lemma proclus : euclidP Point Bet.
Proof.
unfold euclidP, Par.
intros A B C D P Q [Hpar | Hpar].
  unfold Par_strict in Hpar.
  destruct Hpar as [ AB_neq [ CD_ned [_ Ncol]]].
  exfalso.
  apply Ncol.
  destruct A, B, C, D ; try tauto;
  try (
  exists P0;
  split;
  apply col_alt_def; tauto);
  try (
  exists P1;
  split;
  apply col_alt_def; tauto);
  try (
  exists P2;
  split;
  apply col_alt_def; tauto).
intros.
exists P.
destruct Hpar as [ AB_neq [ CD_ned [Col_ACD Col_BCD]]].
split.
  apply col_alt_def; tauto.
apply col_alt_def.
apply col_alt_def in H.
destruct H as [ ? | [ ? | ? ]]; try tauto ; subst.
apply col_alt_def in Col_BCD.
destruct Col_BCD as [ ? | [ ? | ?]]; subst ; tauto.
apply col_alt_def in Col_ACD.
destruct Col_ACD as [ ? | [ ? | ?]]; subst ; tauto.
Qed.

Lemma five_segment : five_segmentP Point Bet Cong.
Proof. unfold five_segmentP, Cong, Bet; intuition; repeat subst; tauto. Qed.

Lemma segment_construction : segment_constructionP Point Bet Cong.
Proof.
unfold segment_constructionP, Bet, Cong.
destruct A, B, C, D;
try (exists P0; solve [intuition discriminate]);
try (exists P1; solve [intuition discriminate]);
exists P2; intuition discriminate.
Qed.

Lemma lower_dim : lower_dimP Point Bet PA PB PC.
Proof. unfold lower_dimP, Col, Bet, PA, PB, PC; intuition discriminate. Qed.

Lemma upper_dim : upper_dimP Point Bet Cong.
Proof. unfold upper_dimP, Col, Bet, Cong; destruct P, Q, A, B, C; tauto. Qed.

Lemma continuity : continuityP Point Bet.
Proof.
unfold continuityP, Bet; intros Xi Upsilon [A H]; exists A; intros X Y HX HY.
assert (HBet := H _ _ HX HY); destruct A, X, Y; tauto.
Qed.
