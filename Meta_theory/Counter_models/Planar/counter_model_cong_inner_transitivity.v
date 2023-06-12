(* This file proves that axiom cong_inner_transitivity
is independent from the other axioms *)

Require Import GeoCoq.Meta_theory.Counter_models.Planar.independence.

(* Definition of the counter-model *)

Inductive Point := P0 | P1 | P2.
Definition Bet (A B C : Point) := A = B \/ B = C.
Definition Cong (A B C D : Point) := (A = B) \/ (B = C /\ A = D).
Definition PA := P0.
Definition PB := P1.
Definition PC := P2.

(* Proof that the following axiom does not hold in the given model *)

Lemma cong_inner_transitivity : ~ cong_inner_transitivityP Point Cong.
Proof.
unfold cong_inner_transitivityP, Cong; intro H.
elim (H P0 P1 P2 P2 P1 P0); try tauto; [intro HF|intros [H1 H2]]; discriminate.
Qed.

(* Proof that the following axioms hold in the given model *)

Lemma point_equality_decidability : point_equality_decidability Point.
Proof.
unfold point_equality_decidability;
destruct A, B; try tauto; right; discriminate.
Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point Bet.
Proof.
unfold bet_inner_transitivityP, Bet;
destruct A, B, C, D; intuition discriminate.
Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point Cong.
Proof. unfold cong_pseudo_reflexivityP, Cong; destruct A, B; tauto. Qed.

Lemma cong_identity : cong_identityP Point Cong.
Proof.
unfold cong_identityP, Cong; destruct A, B, C; intro; intuition discriminate.
Qed.

Lemma inner_pasch : inner_paschP Point Bet.
Proof. unfold inner_paschP, Bet; intuition. Qed.

Lemma bet_symmetry : bet_symmetryP Point Bet.
Proof. unfold bet_symmetryP, Bet; destruct A, B, C; intuition. Qed.

Lemma col_alt_def : forall A B C, Col Point Bet A B C <->
  A = B \/ B = C \/ A = C.
Proof.
split.
unfold Col.
intros [? | [? | ?]];
destruct H as [? | ?]; subst ; tauto.
unfold Col, Bet.
intros [? | [? | ?]]; subst ;
tauto.
Qed.

Lemma euclid : euclidP Point Bet.
Proof.
unfold euclidP; intros A B C D P Q HPar HC HNC HCop.
destruct HPar as [HParS|[HAB [HCD [HC1 HC2]]]].
  {
  destruct HParS as [HAB [HCD [_ HNI]]].
  exfalso; apply HNI.
  destruct A, B, C, D; try tauto;
  try (exists P0; split; apply col_alt_def; tauto);
  try (exists P1; split; apply col_alt_def; tauto);
  try (exists P2; split; apply col_alt_def; tauto).
  }

  {
  exists P; split; apply col_alt_def; [tauto|].
  apply col_alt_def in HC.
  destruct HC as [? | [ ? | ?]]; (try tauto); subst.

    {
    apply col_alt_def in HC2.
    destruct HC2 as [ ? | [ ? | ?]]; subst; tauto.
    }

    {
    apply col_alt_def in HC1.
    destruct HC1 as [ ? | [ ? | ?]]; subst ; tauto.
    }
  }
Qed.


Lemma five_segment : five_segmentP Point Bet Cong.
Proof.
unfold five_segmentP, Bet, Cong.
intros A A' B B' C C' D D' HCong1 HCong2 HCong3 HCong4 [H|H] HBet2 HNEq;
[contradiction|subst].
destruct HCong1 as [H|[H1 H2]]; [contradiction|subst].
destruct HCong4 as [H|[H1 H2]]; [auto|subst].
destruct HBet2 as [H|H]; [intuition|subst; tauto].
Qed.

Lemma segment_construction : segment_constructionP Point Bet Cong.
Proof.
unfold segment_constructionP, Bet, Cong.
destruct A, B, C, D; firstorder;
try (exists P0; tauto);
try (exists P1; tauto);
exists P2; tauto.
Qed.

Lemma lower_dim : lower_dimP Point Bet PA PB PC.
Proof. unfold lower_dimP, Col, Bet; intuition discriminate. Qed.

Lemma upper_dim : upper_dimP Point Bet Cong.
Proof. unfold upper_dimP, Col, Bet, Cong; destruct P, Q, A, B, C; tauto. Qed.

Require Import Classical.

Lemma continuity : continuityP Point Bet.
Proof.
unfold continuityP, Bet; intros Xi Upsilon.
elim (classic (Xi P0)); intro HXiP0;
elim (classic (Xi P1)); intro HXiP1;
elim (classic (Xi P2)); intro HXiP2;
elim (classic (Upsilon P0)); intro HUpsilonP0;
elim (classic (Upsilon P1)); intro HUpsilonP1;
elim (classic (Upsilon P2)); intros HUpsilonP2 [A H];
destruct A;
try (exfalso;
     try assert (HP0P0 := H _ _ HXiP0 HUpsilonP0);
     try assert (HP0P1 := H _ _ HXiP0 HUpsilonP1);
     try assert (HP0P2 := H _ _ HXiP0 HUpsilonP2);
     try assert (HP1P0 := H _ _ HXiP1 HUpsilonP0);
     try assert (HP1P1 := H _ _ HXiP1 HUpsilonP1);
     try assert (HP1P2 := H _ _ HXiP1 HUpsilonP2);
     try assert (HP2P0 := H _ _ HXiP2 HUpsilonP0);
     try assert (HP2P1 := H _ _ HXiP2 HUpsilonP1);
     try assert (HP2P2 := H _ _ HXiP2 HUpsilonP2); intuition discriminate);
try (exists P0; intros X Y HX HY; destruct X, Y; try tauto;
     assert (HFalse := H _ _ HX HY); simpl in *; contradiction);
try (exists P1; intros X Y HX HY; destruct X, Y; try tauto;
     assert (HFalse := H _ _ HX HY); simpl in *; contradiction);
exists P2; intros X Y HX HY; destruct X, Y; try tauto;
assert (HFalse := H _ _ HX HY); simpl in *; contradiction.
Qed.
