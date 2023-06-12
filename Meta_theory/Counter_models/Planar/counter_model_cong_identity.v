(* This file proves that axiom cong_identity
is independent from the other axioms *)

Require Import GeoCoq.Meta_theory.Counter_models.Planar.independence.

(* Definition of the counter-model *)

Inductive Point := P0 | P1 | P2.
Definition Bet (A B C : Point) :=
  match A, B, C with
    | P0, P0, P0
    | P0, P0, P1
    | P0, P0, P2
    | P0, P1, P2
    | P0, P2, P2
    | P1, P0, P0
    | P1, P1, P1
    | P1, P2, P2
    | P2, P0, P0
    | P2, P1, P0
    | P2, P2, P0
    | P2, P2, P1
    | P2, P2, P2 => True
    | _ , _ , _  => False
end.
Definition Cong (A B C D : Point) := True.
Definition PA := P0.
Definition PB := P1.
Definition PC := P1.

(* Proof that the following axiom does not hold in the given model *)

Lemma cong_identity : ~ cong_identityP Point Cong.
Proof. intro H; assert (HFalse := H P0 P1 P2); firstorder; discriminate. Qed.

(* Proof that the following axioms hold in the given model *)

Lemma point_equality_decidability : point_equality_decidability Point.
Proof.
unfold point_equality_decidability; destruct A, B; auto; right; discriminate.
Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point Bet.
Proof. unfold bet_inner_transitivityP, Bet; destruct A, B, C, D; tauto. Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point Cong.
Proof. unfold cong_pseudo_reflexivityP, Cong; auto. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point Cong.
Proof. unfold cong_inner_transitivityP, Cong; tauto. Qed.

Lemma inner_pasch : inner_paschP Point Bet.
Proof. unfold inner_paschP; destruct P, B, Q, A, C; firstorder. Qed.

Lemma bet_symmetry : bet_symmetryP Point Bet.
Proof. unfold bet_symmetryP, Bet; destruct A, B, C; tauto. Qed.

Ltac spliter := repeat
match goal with
   | H:(?X1 /\ ?X2) |- _ => induction H
end.

Lemma col_alt_def :  forall A B C, Col Point Bet A B C <->
  (A = P1 /\ B = P1 /\ C = P1) \/
  (A <> P1 /\ B <> P1) \/
  (B <> P1 /\ C <> P1) \/
  (A <> P1 /\ C <> P1).
Proof.
unfold Col.
split.
  destruct A, B, C ; unfold Bet ;  try tauto; intros;
  right; try (left ; split ; discriminate);
  right; try (left ; split ; discriminate);
  right; split ; discriminate.
destruct A, B, C; simpl; try tauto; intro ;
intuition; spliter ; discriminate.
Qed.

Lemma euclid : euclidP Point Bet.
Proof.
unfold euclidP; intros A B C D P Q HPar HC HNC HCop.
exists P0; split; apply col_alt_def.
  {
  assert (H : P <> Q); [intro; subst; auto|].
  destruct P, Q; simpl; try tauto;
  right; try (left ; split ; discriminate);
  right; try (left ; split ; discriminate);
  right; split ; discriminate.
  }

  {
  assert (H : C <> D).
    {
    unfold Par, Par_strict in HPar; induction HPar; spliter; auto.
    }
  destruct C, D; simpl; try tauto;
  right; try (left ; split ; discriminate);
  right; try (left ; split ; discriminate);
  right; split ; discriminate.
  }
Qed.

Lemma five_segment : five_segmentP Point Bet Cong.
Proof. unfold five_segmentP; tauto. Qed.

Lemma segment_construction : segment_constructionP Point Bet Cong.
Proof.
unfold segment_constructionP, Bet, Cong; destruct A, B; intros C D;
try (exists P0; tauto); try (exists P1; tauto); exists P2; tauto.
Qed.

Lemma lower_dim : lower_dimP Point Bet PA PB PC.
Proof. unfold lower_dimP, Col, Bet; tauto. Qed.

Lemma upper_dim : upper_dimP Point Bet Cong.
Proof. unfold upper_dimP, Col, Bet; destruct A, B, C; tauto. Qed.

Require Import Classical.

Lemma continuity : continuityP Point Bet.
Proof.
unfold continuityP; intros Xi Upsilon.
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
     try assert (HP2P2 := H _ _ HXiP2 HUpsilonP2); simpl in *; contradiction);
try (exists P0; intros X Y HX HY; destruct X, Y; try tauto;
     assert (HFalse := H _ _ HX HY); simpl in *; contradiction);
try (exists P1; intros X Y HX HY; destruct X, Y; try tauto;
     assert (HFalse := H _ _ HX HY); simpl in *; contradiction);
exists P2; intros X Y HX HY; destruct X, Y; try tauto;
assert (HFalse := H _ _ HX HY); simpl in *; contradiction.
Qed.
