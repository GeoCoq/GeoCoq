Require Import GeoCoq.Meta_theory.Counter_models.nD.independent_version.

Section bet_identity_1.

Context `{ITn : independent_Tarski_neutral_dimensionless}.

Lemma g2_1 : forall A B, Cong A B A B.
Proof.
intros; apply cong_inner_transitivity with B A; apply cong_pseudo_reflexivity.
Qed.

Lemma g2_2 : forall A B C D, Cong A B C D -> Cong C D A B.
Proof. intros; apply cong_inner_transitivity with C D; [apply g2_1|auto]. Qed.

Lemma g2_3 : forall A B C D, Cong A B C D -> Cong B A C D.
Proof.
intros; apply cong_inner_transitivity with A B; [|apply g2_2; auto].
apply cong_pseudo_reflexivity.
Qed.

Lemma g2_4 : forall A B C D, Cong A B C D -> Cong A B D C.
Proof. intros; apply g2_2, g2_3, g2_2; auto. Qed.

Lemma g2_5 : forall A B C D, Cong A B C D -> (A = B <-> C = D).
Proof.
intros; split; intro HE; rewrite HE in *;
[apply cong_identity with B, g2_2|apply cong_identity with D]; auto.
Qed.

Lemma g2_6_1 : forall A B, A <> B -> Bet A B B.
Proof.
intros; destruct (segment_construction A B A A) as [C [HBet HCong]]; [auto|].
assert (HE : B = C); [apply g2_5 with A A; auto|rewrite HE in *; auto].
Qed.

Lemma g2_6_2 : forall A B, A <> B -> Cong A A B B.
Proof.
intros; destruct (segment_construction B A B B) as [C [HBet HCong]]; [auto|].
assert (HE : A = C); [apply g2_5 with B B; auto|rewrite HE in *; auto].
Qed.

Lemma g2_7_1 : forall A A' B B' C C',
  Cong A B A' B' -> Cong B C B' C' ->
  Bet A B C -> Bet A' B' C' -> A <> B -> Cong A A A' A' ->
  Cong A C A' C'.
Proof.
intros; apply g2_3; apply g2_4; apply five_segment with A A' B B'; auto.
apply g2_3; apply g2_4; auto.
Qed.

Lemma g2_7_2 : forall A A' B B' C C',
  Cong A B A' B' -> Cong B C B' C' ->
  Bet A B C -> Bet A' B' C' -> A <> B ->
  ~ ~ Cong A C A' C'.
Proof.
intros; assert (~ ~ Cong A A A' A').
  {
  cut ((A = A' -> Cong A A A' A') /\ (~ A = A' -> Cong A A A' A')); [tauto|].
  split; intro; [subst; apply cong_pseudo_reflexivity|apply g2_6_2; auto].
  }
cut (Cong A A A' A' -> Cong A C A' C'); [tauto|apply g2_7_1 with B B'; auto].
Qed.

Lemma g2_8 : forall A B C D,
  Bet A B C -> Bet A B D -> Cong B C B D -> A <> B -> C = D.
Proof.
intros; assert (Cong C C C D); [|apply g2_5 with C C; auto; apply g2_2; auto].
apply five_segment with A A B B; auto; [apply g2_1..|].
apply g2_7_1 with B B; auto; apply g2_1.
Qed.

Lemma g2_9_aux : forall A B C, ~ ~ Bet A B A -> ~ ~ Bet C A B.
Proof.
intros; cut ((A = C -> ~ ~ Bet C A B) /\ (~ A = C -> ~ ~ Bet C A B)); [tauto|].
split; intro; [subst|].

  {
  cut ((B = C -> ~ ~ Bet C C B) /\ (~ B = C -> Bet C C B)); [tauto|].
  split; intro; [subst; auto|apply bet_symmetry, g2_6_1; auto].
  }

  {
  intro; cut (Bet A B A -> A <> C -> Bet C A B); [tauto|].
  intros; apply bet_inner_transitivity with A; auto; apply g2_6_1; auto.
  }
Qed.

Lemma g2_9 : forall A B C, Bet A B A -> ~ ~ Bet C A B.
Proof. intros; apply g2_9_aux; tauto. Qed.

Lemma g2_10 : forall A B C, Bet A B A -> ~ ~ Bet C B A.
Proof. intros; apply g2_9_aux, g2_9; auto. Qed.

Lemma bet_outer_trans : forall A B C D,
  A <> C -> B <> C -> Bet A B C -> Bet B C D -> Bet A C D.
Proof.
intros; destruct (segment_construction A C C D) as [D' [HT HC]]; [auto|].
assert (HBCD' : Bet B C D').
  {
  apply bet_symmetry, bet_inner_transitivity with A; apply bet_symmetry; auto.
  }
assert (D = D'); [apply g2_8 with B C; auto; apply g2_2; auto|subst; auto].
Qed.

Lemma another_point : forall (A B C : Tpoint), A <> B -> exists D, C <> D.
Proof.
intros A B C HAB; destruct (segment_construction A B A C HAB) as [D [HT1 HC1]].
exists D; intro; subst.
assert (HBD : B <> D).
  {
  intro; subst; apply HAB; apply cong_identity with D; apply g2_2; auto.
  }
destruct (segment_construction B D B D HBD) as [E [HT2 HC2]].
assert (HDE : D <> E).
  {
  intro; subst; apply HBD; apply cong_identity with E; apply g2_2; auto.
  }
apply HAB, g2_8 with E D; auto; [|apply bet_symmetry|apply g2_3, g2_2, g2_3];
[apply bet_symmetry, bet_outer_trans with B|..]; auto.
intro; subst; apply HBD, cong_identity with D; auto.
Qed.

Lemma g2_11 : forall A B C,
  Bet A B A -> A <> B ->
  exists D, ~ ~ Bet C D C /\ ~ ~ Bet D C D /\ C <> D.
Proof.
intros A B C HABA HAB; destruct (another_point A B C HAB) as [C' HCC'].
destruct (segment_construction C' C A B) as [D [HC'CD HC1]]; [auto|].
assert (HCD : C <> D)
  by (intro; apply g2_5 in HC1; apply HAB; apply HC1; auto).
exists D; assert (~ ~ Bet C D C); [|do 2 (split; auto); apply g2_9_aux; auto].
destruct (segment_construction C D B A HCD) as [E [HCDE HC2]].
assert (HC3 : ~ ~ Cong C E A A) by (apply g2_7_2 with D B; auto).
cut (~ ~ C = E); [cut (C = E -> Bet C D C); [tauto|intro; subst; auto]|].
cut (Cong C E A A -> C = E); [tauto|intro; apply cong_identity with A; auto].
Qed.

Lemma g2_12 : forall A B C, ~ ~ Bet A B A -> ~ ~ Bet A B C.
Proof.
intros; cut (Bet A B A -> ~ ~ Bet A B C); [tauto|intro].
cut (~ ~ Bet C B A); [|apply g2_10; auto].
assert (HS := bet_symmetry C B A); tauto.
Qed.

Lemma g2_13 : forall A B C, ~ ~ Bet A B A -> A <> B -> ~ ~ Bet C B C.
Proof.
intros; cut ((B = C -> ~ ~ Bet C B C) /\ (~ B = C -> ~ ~ Bet C B C)); [tauto|].
split; intro.

  {
  cut (Bet A B A -> Bet C B C); [tauto|intro].
  subst; apply bet_inner_transitivity with A; apply bet_symmetry, g2_6_1; auto.
  }

  {
  destruct (segment_construction C B B C) as [D [HCBC HC]]; [auto|].
  cut (~ ~ C = D); [cut (C = D -> Bet C B C); [tauto|intro; subst; auto]|].
  assert (HABC := g2_12 A B C); assert (HABD := g2_12 A B D).
  cut (Bet A B C -> Bet A B D -> C = D); [tauto|].
  intros; apply g2_8 with A B; auto; apply g2_2; auto.
  }
Qed.

Lemma g2_14 : forall A B C D,
  Bet A B A -> A <> B -> ~ ~ Bet C D C.
Proof.
intros; destruct (g2_11 A B D) as [E [_ []]]; auto; apply g2_13 with E; auto.
Qed.

Lemma g2_15 : forall A B C D E, Bet A B A -> A <> B -> ~ ~ Bet C D E.
Proof.
intros; cut (~ ~ Bet D E D); [|apply g2_14 with A B; auto].
assert (HB := g2_9 D E C); tauto.
Qed.

Lemma g2_16 : forall A B C D E, ~ Bet C D E -> Bet A B A -> ~ ~ A = B.
Proof.
intros; intro; cut (~ ~ Bet C D E); [tauto|apply g2_15 with A B; auto].
Qed.

End bet_identity_1.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Section bet_identity_2.

Variable n : nat.

Context `{ITnD : independent_Tarski_nD(n.+2)}.

Lemma bet_identity_aux : forall A B, Bet A B A -> ~ ~ A = B.
Proof.
pose I1aux := (tnth basis (inord 0)); pose I2aux := (tnth basis (inord 1)).
pose I1 := I1aux n.+1 Tpoint H ITnD; pose I2 := I2aux n.+1 Tpoint H ITnD.
intros A B; apply g2_16 with I1 O I2; clear A B.
intro HB1; destruct lower_dim as [HF [HB2 [HBC1 HBC2]]].
assert (HC1 : Cong O I O I1)
  by (rewrite big_ltn in HBC1; [destruct HBC1 as [HC _]|]; auto).
assert (HC2 : Cong O I O I2).
  by (rewrite 2?big_ltn // in HBC1; destruct HBC1 as [_ [HC _]]; auto).
assert (HC3 : Cong I1 I2 I I2)
  by (rewrite 2?big_ltn // in HBC2; destruct HBC2 as [[HC _] _]; auto).
assert (HOI1 : O <> I1).
  {
  intro HR; rewrite HR in HB2 HC1; apply HF, cong_identity with I1.
  apply g2_3; auto.
  }
assert (HR : I = I2) by (apply g2_8 with I1 O; auto; apply bet_symmetry; auto).
rewrite HR in HF HC3; apply HF, cong_identity with I2, g2_3; auto.
Qed.

End bet_identity_2.
