Require Import GeoCoq.Meta_theory.Counter_models.nD.independence.
Require Import GeoCoq.Meta_theory.Counter_models.nD.independent_version.
Require Import GeoCoq.Meta_theory.Counter_models.nD.bet_identity.
Require Import GeoCoq.Meta_theory.Counter_models.nD.stability_properties.
Require Import GeoCoq.Meta_theory.Counter_models.nD.stronger_pasch.
Require Import GeoCoq.Axioms.beeson_s_axioms.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Section altIT_to_IT.

Variable n : nat.

Context `{ITn : independent_Tarski_neutral_dimensionless}.
Context {ES : Eq_stability(ITn)}.
Context {ITnD : independent_Tarski_nD(S (S n))(ITn)}.

Lemma cong_stability : forall A B C D, ~ ~ Cong A B C D -> Cong A B C D.
Proof.
exact (point_equality_stability__cong_stability (S n) point_equality_stability).
Qed.

Lemma bet_stability : forall A B C,
  ~ ~ BetS A B C -> BetS A B C.
Proof.
exact (point_equality_stability__betS_stability point_equality_stability).
Qed.

Lemma ITcong_inner_transitivity : forall A B C D E F,
  Cong A B C D -> Cong A B E F -> Cong C D E F.
Proof. intros; apply cong_inner_transitivity with A B; apply g2_2; auto. Qed.

Definition IT A B C := ~ (A <> B /\ B <> C /\ ~ BetS A B C).

Lemma ITsegment_construction : forall A B C D,
  A <> B -> exists E, IT A B E /\ Cong B E C D.
Proof.
intros; destruct (segment_construction A B C D) as [E []]; [auto|].
exists E; split; [intros [HAB [HBC HF]]|auto].
apply HF; split; [auto|split; auto].
Qed.

Lemma weak_Bstability : forall A B C, A <> B -> ~ ~ Bet A B C -> Bet A B C.
Proof.
intros A B C HAB HB1.
destruct (segment_construction A B B C HAB) as [D [HB2 HC]].
cut (C = D); [intro; subst; auto|].
apply point_equality_stability; intro HCD; apply HB1; clear HB1; intro HB1.
apply HCD, g2_8 with A B; auto; apply g2_2; auto.
Qed.

Lemma ITfive_segment  : forall A A' B B' C C' D D',
  Cong A B A' B' -> Cong B C B' C' -> Cong A D A' D' -> Cong B D B' D' ->
  IT A B C -> IT A' B' C' -> A <> B ->
  Cong C D C' D'.
Proof.
intros A A' B B' C C' D D' HC1 HC2 HC3 HC4 HT1 HT2 HAB.
assert (HA'B' : A' <> B')
  by (intro; subst; apply HAB; apply cong_identity with B'; auto).
apply five_segment with A A' B B'; auto; apply weak_Bstability; auto;
intro HB; [apply HT1|apply HT2]; split; auto; split; intro HF;
try (subst; apply HB, g2_6_1; assumption); destruct HF as [_ [_ HF]]; auto.
Qed.

Lemma ITbetween_identity : forall A B, ~ BetS A B A.
Proof. intros A B [HAB [_ HABA]]; apply (bet_identity_aux n) in HABA; auto. Qed.

Lemma ITbetween_symmetry : forall A B C,
  BetS A B C -> BetS C B A.
Proof.
intros A B C [HAB [HBC HB]]; split; [|split; [|apply bet_symmetry]]; auto.
Qed.

Lemma ITbetween_inner_transitivity : forall A B C D,
  BetS A B D -> BetS B C D -> BetS A B C.
Proof.
intros A B C D [HAB [_ HB1]] [HBC [_ HB2]].
split; [|split; [|apply bet_inner_transitivity with D]]; auto.
Qed.

Definition ICol A B C :=  ~ (~ IT C A B /\ ~ IT A C B /\ ~ IT A B C).

Lemma ITinner_pasch : forall A B C P Q,
  BetS A P C -> BetS B Q C -> ~ ICol A B C ->
  exists X, BetS P X B /\ BetS Q X A.
Proof.
intros A B C P Q [? [? HB1]] [? [? HB2]] HNC.
destruct (stronger_inner_pasch n A B C P Q) as [X []]; [..|exists X]; auto.
intros HF; apply HNC; clear HNC; intros [HI1 [HI2 HI3]].
apply HF; clear HF; split; [intro HB|split; intro HB];
[apply HI3|apply HI2|apply HI1]; intros [HNE1 [HNE2 HF]]; apply HF;
split; auto; split; auto; apply bet_symmetry; auto.
Qed.

Definition IPA := O.
Definition IPB := (tnth basis (inord 0)).
Definition IPC := (tnth basis (inord 1)).

Lemma ITlower_dim : ~ IT IPC IPA IPB /\ ~ IT IPA IPC IPB /\ ~ IT IPA IPB IPC.
Proof.
destruct lower_dim as [HF [HB2 [HBC1 HBC2]]].
assert (HC1 : Cong IPA I IPA IPB)
  by (rewrite big_ltn in HBC1; [destruct HBC1 as [HC _]|]; auto).
assert (HC2 : Cong IPA I IPA IPC).
  by (rewrite 2?big_ltn // in HBC1; destruct HBC1 as [_ [HC _]]; auto).
assert (HC3 : Cong IPB IPC I IPC)
  by (rewrite 2?big_ltn // in HBC2; destruct HBC2 as [[HC _] _]; auto).
assert (HAB : IPA <> IPB).
  {
  intro HR; apply (two_points (S n)), cong_identity with IPA, g2_2.
  rewrite -HR in HC1; apply g2_2, HC1.
  }
assert (HAC : IPA <> IPC).
  {
  intro HR; apply (two_points (S n)), cong_identity with IPA, g2_2.
  rewrite -HR in HC2; apply g2_2, HC2.
  }
assert (HBC : IPB <> IPC).
  {
  intro HR; apply HF; apply cong_identity with IPC, g2_2.
  rewrite -HR in HC3; rewrite -HR; apply HC3.
  }
clear HBC1 HBC2; split; [|split]; intro HT; apply HT; split; auto; split; auto;
clear HT; intros [_ [_ HB1]].

  {
  assert (HR : I = IPC).
    {
    apply g2_8 with IPB IPA; auto; apply bet_symmetry; auto.
    }
  apply HBC, cong_identity with I; rewrite -HR in HC3; rewrite -HR; apply HC3.
  }

  {
  assert (HOI := two_points (S n)).
  apply HBC, g2_8 with I O; auto;
  [apply bet_inner_transitivity with IPB; auto|
   apply cong_inner_transitivity with IPA I; apply g2_2; auto].
  }

  {
  assert (HOI := two_points (S n)).
  apply HBC, g2_8 with I O; auto;
  [|apply cong_inner_transitivity with IPA I; apply g2_2; auto].
  apply bet_symmetry.
  destruct (segment_construction IPC O O I) as [E [HB3 HC]]; [auto|].
  cut (E = I); [intro HR; rewrite -HR; auto|].
  apply g2_8 with IPB IPA; auto; [|apply bet_symmetry; auto].
  apply bet_symmetry, bet_inner_transitivity with IPC; auto.
  apply bet_symmetry; auto.
  }
Qed.

Instance altIT_to_IT : intuitionistic_Tarski_neutral_dimensionless.
Proof.
exact
  (Build_intuitionistic_Tarski_neutral_dimensionless
     Tpoint BetS Cong cong_stability bet_stability
     cong_identity ITcong_inner_transitivity cong_pseudo_reflexivity
     ITsegment_construction ITfive_segment ITbetween_identity
     ITbetween_symmetry ITbetween_inner_transitivity ITinner_pasch
     IPA IPB IPC ITlower_dim).
Defined.

End altIT_to_IT.
