Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.Counter_models.nD.independent_version.
Require Import GeoCoq.Algebraic.Counter_models.nD.bet_identity.
Require Import GeoCoq.Algebraic.Counter_models.nD.stability_properties.

Section pasch_ndc.

Variable n : nat.

Context `{ITn : independent_Tarski_neutral_dimensionless}.
Context {ES : Eq_stability(ITn)}.
Context {ITnD : independent_Tarski_nD(S (S n))(ITn)}.

Lemma addition_segments : forall A A' B B' C C',
  Cong A B A' B' -> Cong B C B' C'->
  Bet A B C -> Bet A' B' C' ->
  Cong A C A' C'.
Proof.
intros A A' B B' C C' HC1 HC2 HB1 HB2.
apply (point_equality_stability__cong_stability (S n) point_equality_stability).
cut ((A = B -> ~ ~ Cong A C A' C') /\ (~ A = B -> ~ ~ Cong A C A' C'));
[tauto|split; intro; [subst; apply g2_5 in HC1|apply g2_7_2 with B B'; auto]].
assert (A' = B') by (apply HC1; auto); subst; auto.
Qed.

Lemma g2_24 : forall A A' B B' C C' D D',
  Cong A B A' B' -> Cong B C B' C' -> Cong A D A' D' -> Cong C D C' D' ->
  Bet A B C -> Bet A' B' C' ->
  Cong B D B' D'.
Proof.
intros A A' B B' C C' D D' ? ? ? ? HB1 HB2.
apply (point_equality_stability__cong_stability (S n) point_equality_stability).
assert (HC1 : Cong A C A' C') by (apply addition_segments with B B'; auto).
cut ((A = C -> ~ ~ Cong B D B' D') /\ (~ A = C -> ~ ~ Cong B D B' D'));
[tauto|split; intro HAC; [subst; apply g2_2, cong_identity in HC1; subst|]];
[apply (bet_identity_aux n) in HB1; apply (bet_identity_aux n) in HB2;
 intro HF; apply HB1; intro; apply HB2; intro; subst; auto|].
destruct (segment_construction A C A C HAC) as [E [? HC2]].
destruct (segment_construction A' C' A C) as [E' [? ?]];
[intro; subst; apply cong_identity in HC1; auto|].
assert (Cong E D E' D').
  {
  apply five_segment with A A' C C'; auto.
  apply cong_inner_transitivity with A C; auto.
  }
assert (Cong B D B' D'); [|auto].
apply five_segment with E E' C C'; auto; [apply g2_3, g2_4..| | |]; auto;
[apply cong_inner_transitivity with A C|apply bet_inner_transitivity with A|
 apply bet_inner_transitivity with A'|intro; subst]; auto;
[apply bet_symmetry..|apply g2_2, cong_identity in HC2; subst]; auto.
Qed.

Lemma bet_outer_connectivity : forall A B C D,
  Bet A B C -> Bet A B D -> A <> B -> ~ (~ Bet A C D /\ ~ Bet A D C).
Proof.
intros A B C D HB1 HB2 HAB.
cut ((B = C -> ~ (~ Bet A C D /\ ~ Bet A D C)) /\
     (~ B = C -> ~ (~ Bet A C D /\ ~ Bet A D C))); [tauto|].
split; intro HBC; [subst; tauto|].
cut ((B = D -> ~ (~ Bet A C D /\ ~ Bet A D C)) /\
     (~ B = D -> ~ (~ Bet A C D /\ ~ Bet A D C))); [tauto|].
split; intro HBD; [subst; tauto|].
cut ((C = D -> ~ (~ Bet A C D /\ ~ Bet A D C)) /\
     (~ C = D -> ~ (~ Bet A C D /\ ~ Bet A D C))); [tauto|].
split; intro HCD; [subst; intros [HF _]; apply HF|];
[apply g2_6_1; intro; subst; apply (bet_identity_aux n) in HB1; auto|].
assert (HAC : A <> C)
  by (intro; subst; apply (bet_identity_aux n) in HB1; auto).
assert (HAD : A <> D)
  by (intro; subst; apply (bet_identity_aux n) in HB2; auto).
destruct (segment_construction A D C D HAD) as [C' [HB3 HC1]].
assert (HAC' : A <> C')
  by (intro; subst; apply (bet_identity_aux n) in HB3; auto).
assert (HB4 : Bet B D C').
  {
  apply bet_symmetry, bet_inner_transitivity with A; apply bet_symmetry; auto.
  }
assert (HBC' : B <> C')
  by (intro; subst; apply (bet_identity_aux n) in HB4; auto).
assert (HDC' : D <> C')
  by (intro; subst; apply HCD, (g2_5 _ _ _ _ HC1); auto).
destruct (segment_construction A C C D HAC) as [D' [HB5 HC2]].
assert (HAD' : A <> D')
  by (intro; subst; apply (bet_identity_aux n) in HB5; auto).
assert (HB6 : Bet B C D').
  {
  apply bet_symmetry, bet_inner_transitivity with A; apply bet_symmetry; auto.
  }
assert (HBD' : B <> D')
  by (intro; subst; apply (bet_identity_aux n) in HB6; auto).
assert (HCD' : C <> D')
  by (intro; subst; apply HCD, (g2_5 _ _ _ _ HC2); auto).
destruct (segment_construction A C' C B HAC') as [B' [HB7 HC3]].
assert (HAB' : A <> B')
  by (intro; subst; apply (bet_identity_aux n) in HB7; auto).
assert (HB8 : Bet B C' B').
  {
  apply bet_outer_trans with D; auto.
  apply bet_symmetry, bet_inner_transitivity with A; apply bet_symmetry; auto.
  }
assert (HBB' : B <> B')
  by (intro; subst; apply (bet_identity_aux n) in HB8; auto).
assert (HDB' : D <> B').
  {
  intro; subst; assert (HF : Bet B' C' B')
    by (apply bet_inner_transitivity with A; apply bet_symmetry; auto).
  apply (bet_identity_aux n) in HF; auto.
  }
assert (HC'B' : C' <> B')
  by (intro; subst; apply HBC, eq_sym, (g2_5 _ _ _ _ HC3); auto).
destruct (segment_construction A D' D B HAD') as [B'' [HB9 HC4]].
assert (HAB'' : A <> B'')
  by (intro; subst; apply (bet_identity_aux n) in HB9; auto).
assert (HB10 : Bet B D' B'').
  {
  apply bet_outer_trans with C; auto.
  apply bet_symmetry, bet_inner_transitivity with A; apply bet_symmetry; auto.
  }
assert (HBB'' : B <> B'')
  by (intro; subst; apply (bet_identity_aux n) in HB10; auto).
assert (HCB' : C <> B'').
  {
  intro; subst; assert (HF : Bet B'' D' B'')
    by (apply bet_inner_transitivity with A; apply bet_symmetry; auto).
  apply (bet_identity_aux n) in HF; auto.
  }
assert (HD'B'' : D' <> B'')
  by (intro; subst; apply HBD, eq_sym, (g2_5 _ _ _ _ HC4); auto).
assert (HB11 : Bet B'' D' C)
  by (apply bet_inner_transitivity with A; apply bet_symmetry; auto).
assert (HB12 : Bet B'' C B).
  {
  apply bet_outer_trans with D'; auto; [intro; subst..|].
  apply bet_inner_transitivity with A; apply bet_symmetry; auto.
  }
assert (HC5 : Cong B C' B'' C).
  {
  apply addition_segments with D D'; [apply g2_2, g2_3, g2_4|..]; auto;
  [apply cong_inner_transitivity with C D; auto; apply g2_3; auto..].
  }
assert (HC6 : Cong B B' B'' B) by (apply addition_segments with C' C; auto).
assert (B' = B''); [|subst B''].
  {
  apply g2_8 with A B; [..|apply g2_4|]; auto;
  [apply bet_symmetry, bet_outer_trans with C'|
   apply bet_symmetry, bet_outer_trans with C]; auto;
  [|apply bet_outer_trans with D|]; auto; apply bet_symmetry; auto.
  }
clear HC6; assert (HC6 : Cong C' D' C D).
  {
  apply g2_3, g2_4, five_segment with B B' C C'; auto;
  [apply g2_2, g2_3, g2_4; auto| |apply g2_3, g2_1|];
  [apply cong_inner_transitivity with C D; [|apply g2_3]; auto|].
  apply bet_inner_transitivity with A; apply bet_symmetry; auto.
  }
assert (HC : Col Tpoint Bet C D B' -> ~ (~ Bet A C D /\ ~ Bet A D C)).
  {
  intros HC [HB13 HB14]; apply HC; split; [|split]; intro; clear HC.

    {
    apply HB13; apply bet_inner_transitivity with B'; auto.
    apply bet_symmetry, bet_outer_trans with D'; auto; apply bet_symmetry; auto.
    }

    {
    assert (Bet A C B').
      {
      apply bet_symmetry, bet_outer_trans with D'; auto.
      apply bet_symmetry; auto.
      }
    assert (Bet A B' C).
      {
      apply bet_outer_trans with D; auto.
      apply bet_symmetry, bet_outer_trans with C'; auto;
      [apply bet_inner_transitivity with A|]; apply bet_symmetry; auto.
      }
    assert (HF : Bet C B' C)
      by (apply bet_inner_transitivity with A; apply bet_symmetry; auto).
    apply (bet_identity_aux n) in HF; auto.
    }

    {
    apply HB14; apply bet_inner_transitivity with B';
    [|apply bet_symmetry; auto].
    apply bet_symmetry, bet_outer_trans with C'; auto;
    [|apply bet_symmetry; auto].
    apply bet_inner_transitivity with A; apply bet_symmetry; auto.
    }
  }
cut ((Col Tpoint Bet C D B' -> ~ (~ Bet A C D /\ ~ Bet A D C)) /\
     (~ Col Tpoint Bet C D B' -> ~ (~ Bet A C D /\ ~ Bet A D C))); [tauto|].
split; [auto|intro HNC]; destruct (inner_pasch C D B' D' C') as [E [HB13 HB14]];
[auto; apply bet_symmetry..| |]; auto;
[apply bet_inner_transitivity with A; apply bet_symmetry; auto|clear HC].
assert (HC7 : Cong E C E C').
  {
  apply g2_24 with D' D' D D; auto; [apply g2_1..| |]; apply g2_2, g2_4; auto.
  apply g2_3, cong_inner_transitivity with C D; auto.
  }
assert (HC8 : Cong E D E D').
  {
  apply g2_24 with C' C' C C; auto; [apply g2_1..| |]; apply g2_2; auto.
  apply g2_4, cong_inner_transitivity with C D; auto.
  }
cut ((C' = C -> ~ (~ Bet A C D /\ ~ Bet A D C)) /\
     (~ C' = C -> ~ (~ Bet A C D /\ ~ Bet A D C))); [tauto|].
split; intro HCC'; [subst; intuition|].
destruct (segment_construction C' C C D' HCC') as [P [HB15 HC9]].
destruct (segment_construction D' C C E) as [R [HB16 HC10]]; [auto|].
assert (HC11 : Cong P R E D).
  {
  apply cong_inner_transitivity with E D'; auto.
  apply g2_3, five_segment with D' P C C; auto; [apply g2_4..|];
  [apply g2_2, g2_4; auto|apply g2_1|].
  apply bet_inner_transitivity with C'; apply bet_symmetry; auto.
  }
cut ((D = D' -> ~ (~ Bet A C D /\ ~ Bet A D C)) /\
     (~ D = D' -> ~ (~ Bet A C D /\ ~ Bet A D C))); [tauto|].
split; intro HDD'; [subst; intuition|].
destruct (segment_construction P R P R) as [Q [HB17 HC12]];
[intro; subst; apply g2_2, cong_identity in HC11; subst;
 apply g2_2, cong_identity in HC8; subst; auto|].
assert (HC13 : Cong P Q D D').
  {
  apply addition_segments with R E; auto; [apply g2_4| |apply bet_symmetry];
  auto; apply cong_inner_transitivity with P R; auto; apply g2_2.
  apply cong_inner_transitivity with E D; auto; apply g2_2; auto.
  }
assert (Cong C P C Q).
  {
  apply cong_inner_transitivity with C D'; auto.
  apply cong_inner_transitivity with C D; auto.
  apply g2_3, g2_4, five_segment with P D' R E; auto;
  [apply g2_4, cong_inner_transitivity with E D|
   apply cong_inner_transitivity with P R|apply g2_3, g2_4; auto..|];
  [auto; apply g2_2; auto..|].
  intro; subst; apply cong_identity in HC12; subst.
  apply g2_2, cong_identity in HC13; subst; auto.
  }
assert (Cong D' P D' Q).
  {
  apply five_segment with R R C C; auto; [apply g2_1..|apply g2_2, g2_4| | |];
  [auto|apply bet_symmetry; auto..|intro; subst].
  apply g2_2, cong_identity in HC10; subst.
  apply g2_2, cong_identity in HC7; subst; auto.
  }
assert (Cong B P B Q).
  {
  apply five_segment with D' D' C C; auto; [apply g2_1..| |];
  apply bet_symmetry; auto.
  }
assert (Cong B' P B' Q).
  {
  apply five_segment with C C D' D'; auto; [apply g2_1..| |];
  apply bet_symmetry; auto.
  }
assert (Cong C' P C' Q)
  by (apply g2_24 with B B B' B'; auto; apply g2_1).
exfalso; apply HDD', (g2_5 _ _ _ _ HC13), cong_identity with P.
apply g2_2, five_segment with C' C' C C; auto; apply g2_1.
Qed.

Lemma stronger_inner_pasch : forall A B C P Q,
  Bet A P C -> Bet B Q C ->
  A <> P -> P <> C -> B <> Q -> Q <> C -> ~ Col _ Bet A B C ->
  exists X, (P <> X /\ X <> B /\ Bet P X B) /\ (Q <> X /\ X <> A /\ Bet Q X A).
Proof.
intros A B C P Q HB1 HB2 ? ? ? ? HNC.
destruct (inner_pasch A B C P Q) as [X []]; [auto..|]; [split; auto..|].
assert (HAC : A <> C).
  {
  intro; subst; apply HNC; intros [_ [HF _]]; apply HF, g2_6_1; intro; subst.
  apply (bet_identity_aux n) in HB1; auto.
  }
assert (HBC : B <> C).
  {
  intro; subst; apply HNC; intros [HF _]; apply HF, g2_6_1; intro; subst.
  apply (bet_identity_aux n) in HB1; auto.
  }
exists X; split; split; try split; auto; intro; subst;
[|apply HNC; intros [HF _]; apply HF;
  apply bet_symmetry, bet_outer_trans with Q; auto; apply bet_symmetry; auto|
 |apply HNC; intros [_ [_ HF]]; apply HF;
  apply bet_outer_trans with P; auto; apply bet_symmetry; auto].

  {
  apply (bet_outer_connectivity A X C Q); [|apply bet_symmetry| |]; [auto..|].
  split; intro HB3.

    {
    apply HNC; intros [_ [HF _]]; apply HF, bet_outer_trans with Q; auto.
    apply bet_symmetry; auto.
    }

    {
    apply (bet_outer_connectivity C Q A B); auto; [apply bet_symmetry; auto..|].
    split; intro; apply HNC; unfold Col; [intros [_ [_ HF]]|intros [HF _]];
    apply HF; auto; apply bet_symmetry; auto.
    }
  }

  {
  apply (bet_outer_connectivity B X C P); [|apply bet_symmetry| |]; [auto..|].
  split; intro HB3.

    {
    apply HNC; intros [_ [HF _]]; apply HF, bet_symmetry.
    apply bet_outer_trans with P; auto; apply bet_symmetry; auto.
    }

    {
    apply (bet_outer_connectivity C P A B); auto; [apply bet_symmetry; auto..|].
    split; intro; apply HNC; unfold Col; [intros [_ [_ HF]]|intros [HF _]];
    apply HF; auto; apply bet_symmetry; auto.
    }
  }
Qed.

End pasch_ndc.
