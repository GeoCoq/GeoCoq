Require Import GeoCoq.Main.Tarski_dev.Ch13_4_cos.
Require Import GeoCoq.Main.Annexes.project.
Require Import GeoCoq.Main.Annexes.half_angles.
Require Import GeoCoq.Main.Highschool.incenter.
Require Import GeoCoq.Main.Highschool.orthocenter.

Section Beeson.

Context `{TE : Tarski_euclidean}.

(* Clears the context except for the given hypotheses (and the section instances). *)
#[local] Tactic Notation "keep" ne_hyp_list(l) := clear - Tn TnEQD TE l.

Definition EqRT A B C a b c :=
  exists B' C',
    Cong a b A B' /\ Out A B B' /\ Cong a c A C' /\ Out A C C' /\
    Perp_at A A B A C /\ Par B C B' C'.

Definition EqF P Q R S p q r s :=
  exists A B C a b c,
    Cong A B P Q /\ Cong A C R S /\ Cong a b p q /\ Cong a c r s /\
    EqRT A B C a b c.

Lemma EqRT_diffs A B C a b c :
  EqRT A B C a b c ->
  A <> B /\ A <> C /\ a <> b /\ a <> c.
Proof. intros [B' [C' H]]; spliter; assert_diffs; auto. Qed.

Lemma EqF_diffs P Q R S p q r s :
  EqF P Q R S p q r s ->
  P <> Q /\ R <> S /\ p <> q /\ r <> s.
Proof.
intros [A [B [C [a [b [c [HC1 [HC2 [HC3 [HC4 HEQ]]]]]]]]]].
apply EqRT_diffs in HEQ; spliter; assert_diffs; auto.
Qed.

Lemma per2_cong2__conga2 A B C a b c :
  A <> B -> A <> C -> Per B A C -> Per b a c -> Cong A B a b -> Cong A C a c ->
  CongA A B C a b c /\ CongA A C B a c b.
Proof.
intros HAB HAC HPer1 HPer2 HC1 HC2.
destruct (l11_49 B A C b a c) as [_ HCA]; Cong.
- apply l11_16; auto; intro; treat_equalities; auto.
- destruct HCA as [HCA1 HCA2]; [apply per_distinct with A; auto|split; CongA].
Qed.

Lemma EqRT_cong A B C a b c a' b' c' :
  EqRT A B C a b c -> Cong a b a' b' -> Cong a c a' c' -> EqRT A B C a' b' c'.
Proof.
intros [B' [C' [HC1 [HO1 [HC2 HP]]]]] HC3 HC4.
exists B', C'; split; [CongR|split; [auto|split; [CongR|auto]]].
Qed.

Lemma EqRT_sym A B C a b c :
  Perp_at a a b a c -> EqRT A B C a b c -> EqRT a b c A B C.
Proof.
intros HPer1 HEQ.
assert (HD : A <> B /\ A <> C /\ a <> b /\ a <> c) by (apply EqRT_diffs; auto).
destruct HD as [HAB [HAC [Hab Hac]]].
destruct HEQ as [B' [C' [HC1 [HO1 [HC2 [HO2 [HPer2 HPar]]]]]]].
destruct (segment_construction_3 a b A B Hab HAB) as [b' [HO3 HC3]].
destruct (segment_construction_3 a c A C Hac HAC) as [c' [HO4 HC4]].
exists b', c'; do 4 (split; Cong); split; auto.
assert (HNC : ~ Col a b c) by (apply perp_not_col; Perp).
assert (HOS : OS a b c c') by (apply out_one_side_1 with a; Col).
apply (l12_22_b b c b' c' a); auto.
destruct (per2_cong2__conga2 a b c A B' C') as [HCongA1 _]; Cong; Perp.
  {
  cut (Perp A B' A C'); Perp.
  apply perp_col4 with A B A C; Col; Perp; assert_diffs; auto.
  }
destruct (per2_cong2__conga2 a b' c' A B C) as [HCongA2 _]; Cong; Perp;
  [assert_diffs; auto..|].
  {
  cut (Perp a b' a c'); Perp.
  apply perp_col4 with a b a c; Col; Perp; assert_diffs; auto.
  }
apply conga_trans with A B C; [|CongA].
apply conga_trans with A B' C'; [CongA|].
cut (CongA C B A C' B' A); [intro H; CongA|].
apply (l12_22_a B C B' C' A); Par.
apply out_one_side_1 with A; Col.
apply perp_not_col; Perp.
Qed.

Lemma EqF_sym P Q R S p q r s :
  EqF P Q R S p q r s <-> EqF p q r s P Q R S.
Proof.
cut (forall P Q R S p q r s, EqF P Q R S p q r s -> EqF p q r s P Q R S).
- intros H; split; intro HP; apply H; auto.
- clear P Q R S p q r s; intros P Q R S p q r s.
  intros [A [B [C [a [b [c [HC1 [HC2 [HC3 [HC4 HEQ]]]]]]]]]].
  destruct HEQ as [B' [C' HEQ]].
  exists A, B', C', A, B, C; spliter; do 4 (split; [CongR|]).
  exists B, C; split; Cong; split; [apply l6_6; auto|].
  split; Cong; split; [apply l6_6; auto|]; split; Par.
  cut (Perp A B' A C'); Perp.
  apply perp_col4 with A B A C; Col; [assert_diffs; auto..|].
  apply perp_in_perp with A; Perp.
Qed.

Lemma EqRT_abc_acb A B C a b c :
  EqRT A B C a b c <-> EqRT A C B a c b.
Proof.
cut (forall A B C a b c, EqRT A B C a b c -> EqRT A C B a c b).
- intros H; split; intro HP; apply H; auto.
- clear A B C a b c; intros A B C a b c.
  intros [B' [C' H]]; spliter; exists C', B'.
  repeat (split; Cong; Col; Perp; Par).
Qed.

Lemma EqF_abcd_badc P Q R S p q r s :
  EqF P Q R S p q r s <-> EqF R S P Q r s p q.
Proof.
cut (forall P Q R S p q r s,
       EqF P Q R S p q r s -> EqF R S P Q r s p q).
- intros H; split; intro HP; apply H; auto.
- clear P Q R S p q r s; intros P Q R S p q r s.
  intros [A [B [C [a [b [c [HC1 [HC2 [HC3 [HC4 HEQ]]]]]]]]]].
  exists A, C, B, a, c, b; repeat (split; Cong; Col; Perp; Par).
  apply EqRT_abc_acb; auto.
Qed.

Lemma EqF_cong P Q R S p q r s P' Q' R' S' p' q' r' s' :
  EqF P Q R S p q r s ->
  Cong P Q P' Q' -> Cong R S R' S' -> Cong p q p' q' -> Cong r s r' s' ->
  EqF P' Q' R' S' p' q' r' s'.
Proof.
intros [A [B [C [a [b [c [HC1 [HC2 [HC3 [HC4 HE]]]]]]]]]] HC5 HC6 HC7 HC8.
exists A, B, C, a, b, c; repeat split; [CongR..|assumption].
Qed.

Lemma Per_EqRT__CongA A1 B1 C1 A2 B2 C2 :
  Per B2 A2 C2 ->
  EqRT A1 B1 C1 A2 B2 C2 ->
  CongA A1 B1 C1 A2 B2 C2 /\ CongA A1 C1 B1 A2 C2 B2.
Proof.
intros HPer1 HEQ.
assert (HD : A1 <> B1 /\ A1 <> C1 /\ A2 <> B2 /\ A2 <> C2)
  by (apply EqRT_diffs in HEQ; spliter; repeat (split; auto)).
destruct HEQ as [B [C [HC1 [HO1 [HC2 [HO2 [HPer2 HPar]]]]]]].
destruct HD as [HA1B1 [HA1C1 [HA2B2 HA2C2]]].
assert (HNC1 : ~ Col A1 B1 C1) by (apply perp_not_col; Perp).
assert (HOS1 : OS A1 B1 C1 C) by (apply out_one_side_1 with A1; Col).
assert (HOS2 : OS A1 C1 B1 B) by (apply out_one_side_1 with A1; Col).
destruct (per2_cong2__conga2 A1 B C A2 B2 C2) as [HCongA1 HCongA2]; Cong;
  [assert_diffs; auto..|].
  {
  cut (Perp A1 B A1 C); Perp.
  apply perp_col4 with A1 B1 A1 C1; Col; Perp; assert_diffs; auto.
  }
assert (HCongA3 : CongA B1 C1 A1 B C A1)
  by (apply (l12_22_a C1 B1 C B A1); Par).
assert (HCongA4 : CongA C1 B1 A1 C B A1)
  by (apply (l12_22_a B1 C1 B C A1); Par).
split; [apply conga_trans with A1 B C|apply conga_trans with A1 C B]; CongA.
Qed.

Lemma Per2_EqF__CongA A1 B1 C1 A2 B2 C2 :
  Per B1 A1 C1 -> Per B2 A2 C2 ->
  EqF A1 B1 A1 C1 A2 B2 A2 C2 ->
  CongA A1 B1 C1 A2 B2 C2 /\ CongA A1 C1 B1 A2 C2 B2.
Proof.
intros HPer1 HPer2 HE.
assert (HD := HE); apply EqF_diffs in HD; destruct HD as [HAB [HAC [Hab Hac]]].
destruct HE as [A [B [C [a [b [c HE]]]]]].
destruct HE as [HC1 [HC2 [HC3 [HC4 HE]]]].
cut (EqRT A1 B1 C1 A2 B2 C2); [intro; apply Per_EqRT__CongA; auto|].
destruct HE as [B' [C' [HC5 [HO1 [HC6 [HO2 [HPerp1 HPar]]]]]]].
destruct (segment_construction_3 A1 B1 A2 B2) as [B3 [HO3 HC7]]; auto.
destruct (segment_construction_3 A1 C1 A2 C2) as [C3 [HO4 HC8]]; auto.
exists B3, C3; do 4 (split; Cong); split; [Perp|].
assert (HOS : OS A1 B1 C1 C3).
  {
  apply out_one_side_1 with A1; Col.
  cut (~ Col B1 A1 C1); Col.
  apply per_not_col; Perp.
  }
apply l12_22_b with A1; auto.
destruct (per2_cong2__conga2 A1 B1 C1 A B C) as [HCongA1 _]; Cong; Perp.
destruct (per2_cong2__conga2 A1 B3 C3 A B' C') as [HCongA2 _];
  try solve [assert_diffs; auto|CongR].
- apply col_col_per_per with B1 C1; Col; Perp.
- cut (Perp A B' A C'); Perp.
  apply perp_col4 with A B A C; Col; [assert_diffs; auto..|exists A; Perp].
- apply conga_trans with A B C; CongA.
  apply conga_trans with A B' C'; CongA.
  cut (CongA C B A C' B' A); [CongA|].
  apply l12_22_a; auto.
  apply out_one_side_1 with A; Col.
  cut (~ Col B A C); Col.
  apply per_not_col; Perp; assert_diffs; auto.
Qed.

Lemma EqRT_trans A1 B1 C1 A2 B2 C2 A3 B3 C3 :
  EqRT A1 B1 C1 A2 B2 C2 ->
  EqRT A2 B2 C2 A3 B3 C3 ->
  EqRT A1 B1 C1 A3 B3 C3.
Proof.
intros HEQ1 HEQ2.
assert (HD : A1 <> B1 /\ A1 <> C1 /\
             A2 <> B2 /\ A2 <> C2 /\
             A3 <> B3 /\ A3 <> C3).
  {
  apply EqRT_diffs in HEQ1; apply EqRT_diffs in HEQ2.
  spliter; repeat (split; auto).
  }
destruct HEQ1 as [B2' [C2' [HC1 [HO1 [HC2 [HO2 [HPer1 HPar1]]]]]]].
destruct HEQ2 as [B3' [C3' [HC3 [HO3 [HC4 [HO4 [HPer2 HPar2]]]]]]].
destruct HD as [HA1B1 [HA1C1 [HA2B2 [HA2C2 [HA3B3 HA3C3]]]]].
destruct (segment_construction_3 A1 B1 A3 B3 HA1B1 HA3B3) as [B4 [HO5 HC5]].
destruct (segment_construction_3 A1 C1 A3 C3 HA1C1 HA3C3) as [C4 [HO6 HC6]].
exists B4, C4; do 5 (split; Cong).
cut (Par B2' C2' B4 C4); [apply par_trans; Par|].
assert (HNC1 : ~ Col A1 B1 C1) by (apply perp_not_col; Perp).
assert (HNC2 : ~ Col A2 B2 C2) by (apply perp_not_col; Perp).
assert (HPerp : forall B C, Out A1 B1 B -> Out A1 C1 C -> Per B A1 C).
  {
  intros B C HO7 HO8; cut (Perp A1 B A1 C); [Perp|].
  apply perp_col4 with A1 B1 A1 C1; Col; Perp; assert_diffs; auto.
  }
assert (HNC3 : ~ Col A1 B2' C2')
  by (cut (~ Col B2' A1 C2'); [Col|];
      apply per_not_col; [assert_diffs; auto..|apply HPerp; auto]).
destruct (per2_cong2__conga2 A1 B4 C4 A2 B3' C3') as [HCongA1 _];
  [assert_diffs; auto..|CongR|CongR|].
  {
  cut (Perp A2 B3' A2 C3'); [Perp|].
  apply perp_col4 with A2 B2 A2 C2; Col; Perp; assert_diffs; auto.
  }
destruct (per2_cong2__conga2 A1 B2' C2' A2 B2 C2) as [HCongA2 _];
  [assert_diffs; auto..|Perp|Cong|Cong|].
apply l12_22_b with A1.
- apply l6_7 with B1; [apply l6_6|]; auto.
- apply out_one_side_1 with A1; Col.
  apply l6_7 with C1; [apply l6_6|]; auto.
- apply conga_trans with A2 B3' C3'; CongA.
  apply conga_trans with A2 B2 C2; CongA.
  cut (CongA C2 B2 A2 C3' B3' A2); CongA.
  apply (l12_22_a B2 C2 B3' C3' A2); auto.
  apply out_one_side_1 with A2; Col.
Qed.

Lemma EqF_trans A1 A2 B1 B2 C1 C2 D1 D2 E1 E2 F1 F2 :
  EqF A1 A2 B1 B2 C1 C2 D1 D2 ->
  EqF C1 C2 D1 D2 E1 E2 F1 F2 ->
  EqF A1 A2 B1 B2 E1 E2 F1 F2.
Proof.
intros [A [B [C [a [b [c [HC1 [HC2 [HC3 [HC4 HEQ1]]]]]]]]]].
intros [A' [B' [C' [a' [b' [c' [HC5 [HC6 [HC7 [HC8 HEQ2]]]]]]]]]].
exists A, B, C, a', b', c'; do 4 (split; [assumption|]).
apply EqRT_trans with A' B' C'; [|assumption].
apply EqRT_cong with a b c; [assumption|CongR..].
Qed.

Lemma Fourth_EqF_exists : forall A1 A2 B1 B2 C1 C2,
  A1 <> A2 -> B1 <> B2 -> C1 <> C2 ->
  exists X1 X2, EqF A1 A2 B1 B2 C1 C2 X1 X2.
Proof.
intros A1 A2 B1 B2 C1 C2 HNE1 HNE2 HNE3.
destruct two_distinct_points as [A [B3 HAB3]].
destruct (perp_exists A A B3 HAB3) as [C3 HP].
destruct (segment_construction_2 B3 A A1 A2) as [B4 [HBet1 HC1]]; [auto|].
destruct (segment_construction_2 B3 A C1 C2) as [B5 [HBet2 HC2]]; [auto|].
assert (HAC3 : C3 <> A) by (assert_diffs; auto).
destruct (segment_construction_2 C3 A B1 B2 HAC3) as [C4 [HBet3 HC3]].
assert (HCol1 : Col A B3 B4) by (destruct HBet1; Col).
assert (HCol2 : Col A B3 B5) by (destruct HBet2; Col).
assert (HCol3 : Col A C3 C4) by (destruct HBet3; Col).
assert (HNC : ~ Col A B3 C3) by (apply perp_not_col; Perp).
assert (HB4C4 : B4 <> C4).
  {
  assert (HAB4 : A <> B4) by (intro; treat_equalities; apply HNE1; auto).
  intro; treat_equalities; apply HNC; ColR.
  }
assert (HAB4 : A <> B4) by (assert_diffs; auto).
assert (HAC4 : A <> C4) by (assert_diffs; auto).
assert (HPA : Perp_at A A B4 A C4).
  {
  apply l8_14_2_1b_bis; [|ColR..].
  apply perp_col4 with A B3 A C3; Col; Perp.
  }
assert (HED : B4 = B5 -> exists X1 X2 : Tpoint, EqF A1 A2 B1 B2 C1 C2 X1 X2).
  {
  intro H; treat_equalities.
  exists A, C4, A, B4, C4, A, B4, C4; do 4 (split; Cong).
  exists B4, C4; split; Cong.
  split; [apply out_trivial; auto|split; Cong].
  split; [apply out_trivial; auto|split; Par].
  }
elim (eq_dec_points B4 B5); [apply HED|intro HB4B5; clear HED].
destruct (parallel_existence B4 C4 B5 HB4C4) as [E1 [E2 [_ [HPar HCol4]]]].
assert (HNP : ~ Par A C3 E1 E2).
  {
  assert (HNP :  ~ Par E1 E2 A C3); [|intro HF; apply HNP; Par].
  apply par_not_par with B4 C4; Par.
  apply inter_uniqueness_not_par with C4; Col.
  intro; apply HNC; ColR.
  }
assert (HCop : Coplanar A C3 E1 E2).
  {
  assert (HCop : Coplanar A B5 C4 B4) by CopR.
  apply coplanar_pseudo_trans with A B4 C4; [intro; apply HNC; ColR|..]; Cop.
  - apply coplanar_pseudo_trans with B4 B5 C4; [intro; apply HNC; ColR|..]; Cop.
    elim (eq_dec_points B5 E1); intro HB5E1; subst; Cop.
    cut (Coplanar B4 C4 B5 E1); Cop.
    apply par__coplanar, par_col4__par with B4 C4 E1 E2; Par; Col.
  - apply coplanar_pseudo_trans with B4 B5 C4; [intro; apply HNC; ColR|..]; Cop.
    elim (eq_dec_points B5 E2); intro HB5E2; subst; Cop.
    cut (Coplanar B4 C4 B5 E2); Cop.
    apply par__coplanar, par_col4__par with B4 C4 E1 E2; Par; Col.
  }
  assert (HCop1 : Coplanar A C3 B4 C4) by Cop.
  assert (HCop2 : Coplanar B4 C4 E1 E2) by Cop.
  assert (HNC1 : ~ Col B4 C4 B5) by (intro; apply HNC; ColR).
  assert (HNC2 : ~ Col A B4 C4) by (intro; apply HNC; ColR).
destruct (cop_npar__inter_exists A C3 E1 E2 HCop HNP) as [C5 [HCol5 HCol6]].
exists A, C5, A, B4, C4, A, B5, C5; do 4 (split; Cong).
assert (HAB5 : A <> B5) by (assert_diffs; auto).
assert (HB5C5 : B5 <> C5) by (intro; treat_equalities; apply HNC; ColR).
assert (HParS : Par_strict B4 C4 B5 C5).
  {
  apply par_not_col_strict with B5; Col.
  apply par_col4__par with B4 C4 E1 E2; Col; Par.
  }
assert (HOut1 : Out A B4 B5).
  {
  repeat (split; auto).
  destruct HBet1 as [HBet1|HBet1]; destruct HBet2 as [HBet2|HBet2].
  - apply l5_1 with B3; Between.
  - right; apply between_exchange4 with B3; Between.
  - left; apply between_exchange4 with B3; Between.
  - apply l5_3 with B3; Between.
  }
assert (HOS : OS A B3 C4 C5).
  {
  keep HAB3 HP HBet1 HBet2 HAC3 HBet3 HCol1 HCol2 HCol3 HNC HB4C4 HAB4 HAC4 HPA HB4B5 HCop1 HNC1 HNC2 HCol5 HAB5 HB5C5 HParS HOut1.
  apply col2_os__os with B4 B5; Col; [ColR..|].
  assert (HNC3 : ~ Col C4 B4 B5) by (intro; apply HNC; ColR).
  assert (HNC4 : ~ Col C5 B4 B5)
    by (apply par_strict_not_cols in HParS; spliter; Col).
  elim (cop__one_or_two_sides B4 B5 C4 C5); Cop; intro HTS1; exfalso.
  assert (HOS1 : OS C4 C5 B4 B5).
    {
    keep HAB3 HP HBet1 HBet2 HAC3 HBet3 HCol1 HCol2 HCol3 HNC HB4C4 HAB4 HAC4 HPA HB4B5 HCop1 HNC1 HNC2 HCol5 HAB5 HB5C5 HParS HOut1 HNC3 HNC4 HTS1.
    apply l9_19 with A; [ColR..|].
    split; [auto|intro; apply HNC; ColR].
    }
  assert (HOS2 : OS B4 C4 B5 C5) by Side.
  apply os_ts1324__os in HOS2; Side.
  assert (HTS2 : TS C5 B5 C4 B4) by (apply l9_31; Side).
  apply l9_9 in HTS2.
  apply HTS2; Side.
  }
assert (HOut2 : Out A C4 C5) by (apply col_one_side_out with B3; [ColR|Side]).
exists B5, C5; do 4 (split; Cong); Par.
Qed.

Lemma Fourth_EqF_uniqueness : forall A1 A2 B1 B2 C1 C2 X1 X2 Y1 Y2,
  EqF A1 A2 B1 B2 C1 C2 X1 X2 ->
  EqF A1 A2 B1 B2 C1 C2 Y1 Y2 ->
  Cong X1 X2 Y1 Y2.
Proof.
intros A1 A2 B1 B2 C1 C2 X1 X2 Y1 Y2 H1 H2.
apply EqF_sym in H1.
assert (HEQ : EqF C1 C2 Y1 Y2 C1 C2 X1 X2)
 by (apply EqF_sym; apply EqF_trans with A1 A2 B1 B2; auto).
unfold EqF in HEQ.
destruct HEQ as [A [B [C [a [b [c H]]]]]]; spliter.
assert (HC1 : Cong A B a b) by CongR.
unfold EqRT in H5.
destruct H5 as [B' [C' H5]].
cut (C = C'); [intro; spliter; treat_equalities; CongR|].
spliter.
assert (HC2 : Cong A B A B') by CongR.
assert (HBB' : B = B').
apply (l6_11_uniqueness A A B B); Cong.
apply out_trivial; assert_diffs; auto.
apply l6_6; auto.

treat_equalities.
cut (~ Col A B C).
- intro HNC; apply (l6_21 A C B C); Col; assert_diffs; auto.
- apply perp_not_col, perp_in_perp with A; Perp.
Qed.

Lemma perp_bet_per__eq O P Q X :
  Perp O P O X -> Bet O P Q -> Per P X Q -> P = Q.
Proof.
intros HPerp HBet HPer.
destruct (eq_dec_points P Q) as [|HPQ]; [assumption|exfalso].
destruct (perp_not_col2 _ _ _ _ HPerp) as [HNC|HNC]; [exfalso; apply HNC; Col|].
assert (HXQ : X <> Q) by (intro; treat_equalities; apply HNC; Col).
apply (acute_comp_not_acute O P Q X); auto.
- apply l11_43_aux; [assert_diffs; auto..|left; Perp].
- apply acute_sym, l11_43_aux; [assert_diffs; auto..|left; Perp].
Qed.

Lemma perp_out_per__eq O P Q X :
  Perp O P O X -> Out O P Q -> Per P X Q -> P = Q.
Proof.
intros HPerp [HOP [HOQ [HBet|HBet]]] HPer.
- apply perp_bet_per__eq with O X; auto.
- symmetry; apply perp_bet_per__eq with O X; [|auto|Perp].
  apply perp_col4 with O P O X; Col; assert_diffs; auto.
Qed.
Lemma Pascal_Kupffer_s_version O A B C A' B' C' :
  Perp O A O A' -> Out O A B -> Out O B C -> Out O A' B' -> Out O B' C' ->
  Par A B' B A' -> Par B C' C B' -> Par A C' C A'.
Proof.
intros HPerp1 HO1 HO2 HO3 HO4 HPar1 HPar2.
assert (HA'C : A' <> C).
  {
  intro; treat_equalities; cut (Col O A A'); [|ColR].
  apply perp_not_col2 in HPerp1; destruct HPerp1; Col.
  }
destruct (ex_perp_cop A' C B O HA'C) as [D [HPerp2 HCop1]].
assert (HD : O <> A  /\ O <> B  /\ O <> C /\
             O <> A' /\ O <> B' /\ O <> C')
  by (assert_diffs; repeat split; auto).
destruct HD as [HOA [HOB [HOC [HOA' [HOB' HOC']]]]].
assert (HNC : ~ Col O A' C).
  {
  cut (Perp O A' O C); [intro H; apply perp_not_col2 in H; destruct H; Col|].
  apply perp_col4 with O A' O A; Col; Perp; ColR.
  }
assert (HCop2 : Coplanar O A' B D) by CopR.
assert (HNP : ~ Par O A' B D).
  {
  intro HF.
  assert (HPerp3 : Perp O A' A' C)
    by (apply cop_par_perp__perp with B D; Cop; Par; Perp).
  cut (Col C A' O); Col.
  apply cop_perp2__col with O A'; Cop; Perp.
  apply perp_col4 with O A O A'; Col; ColR.
  }
destruct (cop_npar__inter_exists O A' B D HCop2 HNP) as [D' [HCol1 HCol2]].
assert (HEP : A = C -> A' = C' -> Par A C' C A')
  by (intros; treat_equalities; Par).
cut (A <> C \/ A' <> C' -> Par A C' C A');
[intro HNEP; elim (eq_dec_points A C); elim (eq_dec_points A' C'); tauto|].
clear HEP; intro HNE.
assert (HAC : A <> C).
  {
  intro; treat_equalities.
  assert (HPar3 : Par A' B B C') by (apply par_trans with A B'; Par).
  apply (not_strict_par _ _ _ _ B) in HPar3; Col.
  destruct HPar3 as [_ HCol3].
  destruct HNE as [|HA'C']; auto.
  cut (O = B); [intro; treat_equalities; assert_diffs; auto|].
  apply l6_21 with A' C' B O; Col; [intro; apply HNC; ColR|ColR].
  }
assert (HA'C' : A' <> C').
  {
  intro; treat_equalities.
  assert (HPar3 : Par A B' B' C) by (apply par_trans with A' B; Par).
  apply (not_strict_par _ _ _ _ B') in HPar3; Col.
  destruct HPar3 as [_ HCol3].
  cut (O = B'); [intro; treat_equalities; assert_diffs; auto|].
  apply l6_21 with O A' C A; Col; ColR.
  }
clear HNE.
assert (HEP : B = C -> B' = C' -> Par A C' C A')
  by (intros; treat_equalities; Par).
cut (B <> C \/ B' <> C' -> Par A C' C A');
[intro HNEP; elim (eq_dec_points B C); elim (eq_dec_points B' C'); tauto|].
clear HEP; intro HNE.
assert (HBC : B <> C).
  {
  intro; treat_equalities.
  apply (not_strict_par _ _ _ _ B) in HPar2; Col.
  destruct HPar2 as [_ HCol3].
  destruct HNE as [|HB'C']; auto.
  cut (O = B); [intro; treat_equalities; assert_diffs; auto|].
  apply l6_21 with B' C' B O; Col; intro; apply HNC; ColR.
  }
assert (HB'C' : B' <> C').
  {
  intro; treat_equalities.
  apply (not_strict_par _ _ _ _ B') in HPar2; Col.
  destruct HPar2 as [HCol3 _].
  cut (O = B'); [intro; treat_equalities; assert_diffs; auto|].
  apply l6_21 with O A' C A; Col; ColR.
  }
clear HNE.
assert (HA'D' : A' <> D').
  {
  intro; treat_equalities; apply HBC, perp_out_per__eq with O A'; auto.
  - apply perp_col4 with O A O A'; Col.
  - cut (Perp A' B A' C); [Perp|].
    apply perp_col4 with B D A' C; Col; Perp; assert_diffs; auto.
  }
assert (HOD' : O <> D').
  {
  intro; treat_equalities.
  assert (HPar3 : Par O A' A' C).
    {
    apply l12_9 with B D; Cop; Perp.
    apply perp_col4 with O A' O A; Col; Perp; [|ColR]; assert_diffs; auto.
    }
  apply (not_strict_par _ _ _ _ A') in HPar3; Col; destruct HPar3; Col.
  }
assert (HAC' : A <> C').
  {
  cut (Perp O A O C'); [|apply perp_col4 with O A O A'; Col; Perp; ColR].
  intro H; destruct (perp_not_col2 _ _ _ _ H); Col; assert_diffs; auto.
  }
assert (HAD' : A <> D').
  {
  cut (Perp O A O D'); [|apply perp_col4 with O A O A'; Col; Perp; ColR].
  intro H; destruct (perp_not_col2 _ _ _ _ H); Col; assert_diffs; auto.
  }
assert (HBD' : B <> D').
  {
  cut (Perp O B O D'); [|apply perp_col4 with O A O A'; Col; Perp; ColR].
  intro H; destruct (perp_not_col2 _ _ _ _ H); Col; assert_diffs; auto.
  }
assert (HCD' : C <> D').
  {
  cut (Perp O C O D'); [|apply perp_col4 with O A O A'; Col; Perp; ColR].
  intro H; destruct (perp_not_col2 _ _ _ _ H); Col; assert_diffs; auto.
  }
assert (HPerp3 : Perp A' B C D').
  {
  destruct (perp_exists D' A' B) as [D'' HD'']; [assert_diffs; auto|].
  cut (Col C D' D'').
  - intro; apply perp_col4 with A' B D' D''; Col; Perp; assert_diffs; auto.
  - apply (altitude_intersect A' C B C D' D'' C); Col; Perp.
    + intro; apply HNC; ColR.
    + apply perp_col4 with A' C B D; Col; Perp.
    + apply perp_col4 with O A O A'; Col; Perp; ColR.
  }
assert (HPerp4 : Perp A B' C D').
  {
  keep HPerp1 HO1 HO2 HO3 HPar1 HA'C HOA HOB HOC HOA' HOB' HNC HCol1 HAC HBC HA'D' HOD' HAD' HBD' HCD' HPerp3.
  apply cop_par_perp__perp with A' B; Par.
  apply coplanar_pseudo_trans with O C A'; Col; Cop.
  cut (Col O A C); [Cop|ColR].
  }
assert (HB'D' : B' <> D').
  {
  intro; treat_equalities; apply HAC, perp_out_per__eq with O B'; Perp.
  - apply perp_col4 with O A O A'; Col.
  - apply l6_7 with B; auto.
  }
assert (HPerp5 : Perp A D' B' C).
  {
  destruct (perp_exists B' A D') as [C'' HC'']; [assert_diffs; auto|].
  cut (Col C B' C'').
  - intro; apply perp_col4 with A D' B' C''; Col; Perp; assert_diffs; auto.
  - apply (altitude_intersect A C D' C B' C'' C); Col; Perp.
    + intro; apply HNC; ColR.
    + apply perp_col4 with O A O A'; Col; Perp; ColR.
  }
assert (HPerp6 : Perp A D' B C').
  {
  apply perp_sym, cop_par_perp__perp with B' C; Par; Perp.
  apply coplanar_pseudo_trans with O C A'; Col; Cop.
  - cut (Col O A' C'); [Cop|ColR].
  - cut (Col O A C); [Cop|ColR].
  }
assert (HEP : A = B -> Par A C' C A').
  {
  intro; treat_equalities; cut (A' = B'); [intro; treat_equalities; Par|].
  destruct (not_strict_par _ _ _ _ A HPar1) as [_ HCol3]; Col.
  apply l6_21 with O A' A B'; Col; [|assert_diffs; auto].
  intro; apply HNC; ColR.
  }
elim (eq_dec_points A B); [auto|clear HEP; intro HAB].
assert (HC'D' : C' <> D').
  {
  intro; treat_equalities; apply HAB, perp_out_per__eq with O C'; Perp.
  apply perp_col4 with O A O A'; Col.
  }
assert (HPerp7 : Perp A C' B D').
  {
  destruct (perp_exists D' A C') as [B'' HB'']; [assert_diffs; auto|].
  cut (Col B D' B'').
  - intro; apply perp_col4 with A C' B'' D'; Col; Perp; assert_diffs; auto.
  - apply (altitude_intersect A B C' B D' B'' B); Col; Perp.
    + assert (HPerp7 : Perp C' D' O A)
        by (apply perp_col4 with O A' O A; Col; Perp; ColR).
      destruct (perp_not_col2 _ _ _ _ HPerp7) as [HF|]; Col.
      intro; apply HF; ColR.
    + apply perp_col4 with O A O A'; Col; Perp; ColR.
  }
apply l12_9 with B D'; Perp.
- keep HPerp1 HO1 HO2 HA'C HOA HOB HOC HOA' HNC HCol1 HAC HBC HA'D' HOD' HAD' HBD' HCD' HPerp3 HAB. apply coplanar_pseudo_trans with O C A'; Col; Cop.
  cut (Col O A C); [Cop|ColR].
- keep HPerp1 HO1 HO2 HA'C HOA HOB HOC HOA' HNC HCol1 HAC HBC HA'D' HOD' HAD' HBD' HCD' HPerp3 HAB. apply coplanar_pseudo_trans with O C A'; Col; Cop.
  cut (Col O A C); [Cop|ColR].
- apply coplanar_pseudo_trans with O C A'; Col; Cop.
  cut (Col O A' C'); [Cop|ColR].
- apply coplanar_pseudo_trans with O C A'; Col; Cop.
  cut (Col O A' C'); [Cop|ColR].
- apply perp_col4 with A' C B D; Col; Perp.
Qed.

Lemma out2_cong2_par O A B a b :
  ~ Col O A B -> Out O A a -> Out O B b ->
  Cong O A O B -> Cong O a O b ->
  Par A B a b.
Proof.
intros HNC HO1 HO2 HC1 HC2.
apply (l12_22_b A B a b O); auto; [apply out_one_side_1 with O; Col|].
assert (HRS : hypothesis_of_right_saccheri_quadrilaterals).
  {
  cut postulate_of_existence_of_a_right_saccheri_quadrilateral.
  - intros [C [D [E [F [HSac HPer]]]]]; apply (per_sac__rah C D E F); auto.
  - cut playfair_s_postulate; [|intro; apply parallel_uniqueness].
    apply stronger_postulates_bis; simpl; tauto.
  }
assert (HD : O <> A /\ A <> B /\ O <> B) by (assert_diffs; auto).
destruct HD as [HOA [HAB HOB]].
assert (HD : O <> a /\ a <> b /\ O <> b).
  {
  assert_diffs; split; [|split]; auto.
  intro; treat_equalities; apply HNC; ColR.
  }
destruct HD as [HOa [Hab HOb]].
destruct (ex_trisuma O A B) as [D [E [F HSumA1]]]; auto.
assert (HBet1 : Bet D E F) by (apply (t22_14__bet HRS O A B); auto).
destruct HSumA1 as [G [H [I [HSumA1 HSumA2]]]].
destruct (ex_trisuma O a b) as [d [e [f HSumA3]]]; auto.
assert (HBet2 : Bet d e f) by (apply (t22_14__bet HRS O a b); auto).
destruct HSumA3 as [g [h [i [HSumA3 HSumA4]]]].
assert (HSumA5 : SumA O A B O A B G H I).
  {
  apply (conga3_suma__suma O A B A B O G H I); [CongA..| |assert_diffs; CongA].
  destruct (l11_49 A O B B O A) as [_ HCongA]; Cong; CongA.
  destruct (HCongA HAB) as []; CongA.
  }
assert (HSumA6 : SumA O a b O a b G H I).
  {
  assert (HCongA1 : CongA b O a B O A) by (apply out2__conga; auto).
  assert (HCongA2 : CongA g h i G H I).
    {
    apply sams2_suma2__conga123 with B O A D E F; auto.
    - apply bet_suma__sams with d e f; auto.
       apply conga3_suma__suma with g h i b O a d e f; auto;
       assert_diffs; apply conga_refl; auto.
    - apply bet_suma__sams with D E F; auto.
    - apply conga3_suma__suma with g h i b O a d e f; auto.
      + assert_diffs; apply conga_refl; auto.
      + assert_diffs; apply conga_line; auto.
    }
  apply (conga3_suma__suma O a b a b O g h i); [CongA..| |assert_diffs; CongA].
  destruct (l11_49 a O b b O a) as [_ HCongA3]; Cong; CongA.
  destruct (HCongA3 Hab) as []; CongA.
  }
apply conga_comm, (sams2_suma2__conga O A B G H I); auto;
apply acute__sams, cong__acute; Cong.
Qed.

Theorem interchange_theorem A1 A2 B1 B2 P1 P2 Q1 Q2 :
  EqF A1 A2 B1 B2 P1 P2 Q1 Q2 ->
  EqF A1 A2 P1 P2 B1 B2 Q1 Q2.
Proof.
intros [A [B [C [a [b [c [HC1 [HC2 [HC3 [HC4 HE]]]]]]]]]].
assert (HD : A <> B /\ A <> C /\ a <> b /\ a <> c) by (apply EqRT_diffs; auto).
destruct HD as [HAB [HAC [Hab Hac]]].
destruct HE as [B' [C' [HC5 [HO1 [HC6 [HO2 [HPer1 HPar]]]]]]].
destruct (segment_construction_3 A C a b) as [D  [HO3 HC7]]; auto.
destruct (segment_construction_3 A B a c) as [D' [HO4 HC8]]; auto.
exists A, B, D, A, C, D'; do 4 (split; [CongR|]).
assert (HAD : A <> D) by (assert_diffs; auto).
assert (HAD' : A <> D') by (assert_diffs; auto).
destruct (segment_construction_3 A B A C ) as [E  [HO5 HC9 ]]; auto.
destruct (segment_construction_3 A D A D') as [E' [HO6 HC10]]; auto.
assert (HAE' : A <> E') by (assert_diffs; auto).
assert (C' = E'); [|treat_equalities].
  {
  apply (l6_11_uniqueness A A C' C); Cong; [apply l6_6; auto| |CongR].
  apply l6_7 with D; apply l6_6; auto.
  }
exists E, C'; do 4 (split; Cong).
split; [cut (Perp A B A D); Perp; apply perp_col4 with A B A C; Col; Perp|].
assert (HPer2 : Perp A B A C')
  by (apply perp_col4 with A B A C; Col; Perp; ColR).
assert (HO7 : Out A B' E) by (apply l6_7 with B; [apply l6_6|]; auto).
assert (HO8 : Out A C' C) by (apply l6_6; auto).
apply (Pascal_Kupffer_s_version A B B' E C' C D); auto.
apply (out2_cong2_par A); Cong; [|apply l6_6; auto|CongR].
assert (HPerp : Perp A B' A D)
  by (apply perp_col4 with A B A C; Col; Perp; assert_diffs; auto).
apply perp_not_col2 in HPerp; destruct HPerp; Col.
Qed.

Lemma Per2_CongA__EqF A1 B1 C1 A2 B2 C2 :
  A1 <> C1 -> A2 <> C2 -> Per B1 A1 C1 -> Per B2 A2 C2 ->
  CongA A1 B1 C1 A2 B2 C2 ->
  EqF A1 B1 A1 C1 A2 B2 A2 C2.
Proof.
intros HA1C1 HA2C2 HPer1 HPer2 HCA.
assert (HD : A1 <> B1 /\ C1 <> B1 /\ A2 <> B2 /\ C2 <> B2) by (assert_diffs; auto).
destruct HD as [HA1B1 [HC1B1 [HA2B2 HC2B2]]].
destruct (segment_construction_3 A1 B1 A2 B2 HA1B1 HA2B2) as [B3 [HO1 HC1]].
destruct (segment_construction_3 A1 C1 A2 C2 HA1C1 HA2C2) as [C3 [HO2 HC2]].
assert (HA1B3 : A1 <> B3) by (assert_diffs; auto).
assert (HA1C3 : A1 <> C3) by (assert_diffs; auto).
assert (HPer3 : Per B3 A1 C3).
  {
  apply l8_3 with B1; [|auto|apply out_col in HO1; Col].
  apply l8_2, l8_3 with C1; [apply l8_2; auto|auto|apply out_col in HO2; Col].
  }
assert (HC3 : Cong B3 C3 B2 C2) by (apply (l10_12 B3 A1 C3 B2 A2 C2); Cong).
assert (HB3C3 : B3 <> C3) by (intro; subst C3; apply HA1B3; symmetry; apply l8_8; auto).
assert (HCA2 : CongA A1 B3 C3 A2 B2 C2)
  by (destruct (l11_51 A1 B3 C3 A2 B2 C2) as [_ [HCA2 _]]; Cong).
exists A1, B1, C1, A2, B2, C2; do 4 (split; [Cong|]).
exists B3, C3; do 4 (split; [Cong|]).
split; [apply perp_in_left_comm, per_perp_in; auto|].
apply l12_22_b with A1; [auto| |].
- apply out_one_side_1 with A1; [|Col|auto].
  intro; apply (per_not_col B1 A1 C1); auto; Col.
- apply conga_comm, conga_trans with A2 B2 C2; [auto|apply conga_sym; auto].
Qed.

Lemma EqF_sum X1 Y1 Z1 X2 Y2 Z2 U1 V1 U2 V2 :
  Bet X1 Y1 Z1 -> Bet X2 Y2 Z2 ->
  EqF X1 Y1 U1 V1 X2 Y2 U2 V2 -> EqF Y1 Z1 U1 V1 Y2 Z2 U2 V2 ->
  EqF X1 Z1 U1 V1 X2 Z2 U2 V2.
Proof.
intros HB1 HB2 HE1 HE2.
destruct (EqF_diffs _ _ _ _ _ _ _ _ HE1) as [HX1Y1 [HU1V1 [HX2Y2 HU2V2]]].
destruct (EqF_diffs _ _ _ _ _ _ _ _ HE2) as [HY1Z1 [_ [HY2Z2 _]]].
apply interchange_theorem in HE1; apply interchange_theorem in HE2.
apply interchange_theorem.
destruct (ex_perp_cop X1 Y1 X1 X1 HX1Y1) as [E [HPerp _]].
assert (HX1E : X1 <> E) by (assert_diffs; auto).
destruct (segment_construction_3 X1 E X2 Y2 HX1E HX2Y2) as [A' [HO1 HC1]].
destruct (segment_construction_3 X1 Y1 U1 V1 HX1Y1 HU1V1) as [R [HO2 HC2]].
destruct (segment_construction_3 X1 E U2 V2 HX1E HU2V2) as [R' [HO3 HC3]].
destruct (vector_construction Y1 Z1 X1) as [B HV].
assert (HO4 : Out X1 Y1 B).
  {
  assert (HSD : Same_dir X1 Y1 X1 B).
    {
    apply same_dir_trans with Y1 Z1; [apply bet_same_dir2; auto|].
    destruct HV as [HP|[? ?]]; [apply plg_opp_dir; auto|subst; exfalso; auto].
    }
  destruct (same_dir_out X1 Y1 B HSD) as [|[? ?]]; [auto|subst; exfalso; auto].
  }
assert (HC4 : Cong X1 B Y1 Z1) by (apply eqv_cong, eqv_sym; auto).
assert (HX1B : X1 <> B) by (assert_diffs; auto).
destruct (segment_construction_3 X1 E Y2 Z2 HX1E HY2Z2) as [B' [HO5 HC5]].
assert (HP0 : Per Y1 X1 E) by (apply perp_per_1; auto).
assert (HPer : forall P Q, Out X1 Y1 P -> Out X1 E Q -> Per P X1 Q).
  {
  intros P Q HP HQ.
  assert (HP1 : Per Y1 X1 Q) by (apply per_col with E; Col).
  apply l8_2, per_col with Y1; [auto|apply l8_2; auto|Col].
  }
assert (HNCol : forall P Q, Out X1 Y1 P -> Out X1 E Q -> ~ Col P X1 Q).
  {
  intros P Q HP HQ; apply per_not_col; [assert_diffs; auto..|apply HPer; auto].
  }
assert (HOS : forall P Q, Out X1 E P -> Out X1 E Q -> OS X1 Y1 P Q).
  {
  intros P Q HP HQ; apply out_one_side_1 with X1; [|Col|].
  - intro; apply (HNCol Y1 P); [apply out_trivial; auto|auto|Col].
  - apply l6_7 with E; [apply l6_6|]; auto.
  }
assert (HPar1 : Par Y1 A' R R').
  {
  destruct (Per2_EqF__CongA X1 Y1 A' X1 R R') as [HCA _];
    [apply HPer; [apply out_trivial|]; auto|apply HPer; auto|
     apply EqF_cong with X1 Y1 X2 Y2 U1 V1 U2 V2; Cong|].
  apply l12_22_b with X1; [auto|apply HOS; auto|apply conga_comm; auto].
  }
assert (HO6 : Out X1 B R) by (apply l6_7 with Y1; [apply l6_6|]; auto).
assert (HPar2 : Par B B' R R').
  {
  destruct (Per2_EqF__CongA X1 B B' X1 R R') as [HCA _];
    [apply HPer; auto|apply HPer; auto|
     apply EqF_cong with Y1 Z1 Y2 Z2 U1 V1 U2 V2; Cong|].
  apply l12_22_b with X1; [auto|apply col_one_side with Y1; [Col|auto|apply HOS; auto]|apply conga_comm; auto].
  }
assert (HX1B' : X1 <> B') by (assert_diffs; auto).
destruct (segment_construction X1 A' X1 B') as [Z' [HB3 HC6']].
assert (HV' : EqV X1 B' A' Z').
  {
  assert (HX1A' : X1 <> A') by (assert_diffs; auto).
  assert (HA'Z' : A' <> Z') by (intro; treat_equalities; auto).
  assert (HSD : Same_dir X1 B' A' Z').
    {
    apply same_dir_trans with X1 A'; [|apply bet_same_dir2; auto].
    right; exists B'; split; [apply l6_7 with E; [apply l6_6|]; auto|apply eqv_refl].
    }
  destruct HSD as [[]|[D' [HO HV1]]]; [exfalso; auto|].
  assert (D' = Z'); [|subst; auto].
  apply (l6_11_uniqueness A' X1 B' Z'); [apply l6_6; auto|apply eqv_cong in HV1; Cong|apply out_trivial; auto|Cong].
  }
assert (HC6 : Cong X1 Z' X2 Z2) by (apply l2_11 with A' Y2; [auto|auto|auto|CongR]).
assert (HX1A' : X1 <> A') by (assert_diffs; auto).
assert (HO7 : Out X1 E Z') by (apply l6_7 with A'; [auto|apply bet_out; auto]).
assert (HO8 : Out X1 Y1 Z1) by (apply bet_out; auto).
assert (HBB' : B <> B') by (intro; subst; apply (HNCol B' B'); [auto|auto|Col]).
assert (HZ1Z' : Z1 <> Z') by (intro; subst; apply (HNCol Z' Z'); [auto|auto|Col]).
destruct (vector_construction B' B Z') as [T HT].
assert (HV2 : EqV T Z1 A' Y1).
  {
  apply eqv_sum with B X1.
  - apply eqv_trans with Z' B'.
    + apply eqv_comm, eqv_permut, eqv_comm; auto.
    + apply eqv_sym, eqv_comm, eqv_permut; auto.
  - apply eqv_sym, eqv_permut, eqv_sym; auto.
  }
assert (HPar4 : Par Z' T R R').
  {
  apply par_trans with B' B; [|apply par_left_comm; auto].
  apply par_symmetry, eqv_par; auto.
  }
assert (HA'Y1 : A' <> Y1) by (intro; subst; apply (HNCol Y1 Y1); [apply out_trivial; auto|auto|Col]).
assert (HPar5 : Par T Z1 R R').
  {
  apply par_trans with A' Y1; [|apply par_left_comm; auto].
  apply par_symmetry, eqv_par; [auto|apply eqv_sym; auto].
  }
assert (HCol : Col Z1 Z' T)
  by (destruct (parallel_uniqueness R R' Z' T T Z1 T) as [_ HC]; Par; Col).
assert (HPar3 : Par Z1 Z' R R').
  {
  apply par_left_comm, par_col_par_2 with T; [auto|Col|auto].
  }
assert (HCA : CongA Z' Z1 X1 R' R X1).
  {
  apply l12_22_a; [apply l6_7 with Y1; [apply l6_6|]; auto|
                  apply col_one_side with Y1; [Col|assert_diffs; auto|apply HOS; auto]|auto].
  }
apply EqF_cong with X1 Z1 X1 Z' X1 R X1 R'; [|Cong..].
apply Per2_CongA__EqF; [assert_diffs; auto|assert_diffs; auto|apply HPer; auto|apply HPer; auto|].
apply conga_comm; auto.
Qed.

Lemma halfa2__EqF A B C b c I i :
  ~ Col A B C -> Out A B b -> Out A C c -> CongA A B C A b c ->
  HalfA I B A C -> HalfA I A B C -> HalfA i b A c -> HalfA i A b c ->
  exists P p, Col A B P /\ Perp A B I P /\ Col A b p /\ Perp A b i p /\
              EqF A B P I A b p i.
Proof.
intros HNC HO1 HO2 HCA HH1 HH2 HH3 HH4.
assert (HD : A <> B /\ A <> b /\ A <> C /\ A <> c) by (assert_diffs; auto).
destruct HD as [HAB [HAb [HAC HAc]]].
assert (HNC' : ~ Col A b c)
  by (intro; apply HNC; apply out_col in HO1; apply out_col in HO2; ColR).
assert (HNC1 : ~ Col A B I).
  {
  destruct (halfa_distincts I B A C HH1) as [_ [_ HAI]].
  destruct HH1 as [_ [_ HCA1]].
  intro; apply HNC.
  assert (Col C A I) by (apply col_conga_col with B A I; Col).
  ColR.
  }
assert (HNC2 : ~ Col A b i).
  {
  destruct (halfa_distincts i b A c HH3) as [_ [_ HAi]].
  destruct HH3 as [_ [_ HCA1]].
  intro; apply HNC'.
  assert (Col c A i) by (apply col_conga_col with b A i; Col).
  ColR.
  }
destruct (l8_18_existence A B I HNC1) as [P [HC1 HP1]].
destruct (l8_18_existence A b i HNC2) as [p [HC2 HP2]].
exists P, p; do 4 (split; [auto|]).
assert (HO3 : Out A P B)
  by (apply acute_col_perp__out with I; [apply acute_sym, halfa__acute with C|..]; auto).
assert (HO4 : Out B P A)
  by (apply acute_col_perp__out with I; [apply acute_sym, halfa__acute with C|Col|Perp]; auto).
assert (HO5 : Out A p b)
  by (apply acute_col_perp__out with i; [apply acute_sym, halfa__acute with c|..]; auto).
assert (HO6 : Out b p A)
  by (apply acute_col_perp__out with i; [apply acute_sym, halfa__acute with c|Col|Perp]; auto).
assert (HPI : P <> I) by (intro; subst; apply HNC1; Col).
assert (Hpi : p <> i) by (intro; subst; apply HNC2; Col).
assert (HAP : A <> P) by (assert_diffs; auto).
assert (HBP : B <> P) by (assert_diffs; auto).
assert (HAp : A <> p) by (assert_diffs; auto).
assert (Hbp : b <> p) by (assert_diffs; auto).
assert (HPer1 : Per A P I)
  by (apply perp_per_2; assert (Perp A P I P) by (apply perp_col with B; auto); Perp).
assert (HPer2 : Per B P I)
  by (apply perp_per_2; assert (Perp B P I P) by (apply perp_col with A; Perp; Col); Perp).
assert (HPer3 : Per A p i)
  by (apply perp_per_2; assert (Perp A p i p) by (apply perp_col with b; auto); Perp).
assert (HPer4 : Per b p i)
  by (apply perp_per_2; assert (Perp b p i p) by (apply perp_col with A; Perp; Col); Perp).
assert (HCA1 : CongA P A I p A i).
  {
  apply l11_10 with B I b i; [|auto|apply out_trivial; assert_diffs; auto|auto|
                              apply out_trivial; assert_diffs; auto].
  apply conga_halfa__conga2 with C c; [auto|auto|apply out2__conga; apply l6_6; auto].
  }
assert (HCA2 : CongA P B I p b i).
  {
  apply l11_10 with A I A i; [|auto|apply out_trivial; assert_diffs; auto|auto|
                              apply out_trivial; assert_diffs; auto].
  apply conga_halfa__conga2 with C c; auto.
  }
apply EqF_sum with P p.
- apply out2__bet; [auto|apply l6_6; auto].
- apply out2__bet; [auto|apply l6_6; auto].
- apply EqF_cong with P A P I p A p i; [|Cong..].
  apply Per2_CongA__EqF; auto.
- apply Per2_CongA__EqF; auto.
Qed.

Theorem fundamental_theorem_of_proportion A B C b c :
  ~ Col A B C -> Out A B b -> Out A C c -> Par B C b c -> EqF A B A b A C A c.
Proof.
intros HNC HO1 HO2 HPar.
assert (HD : A <> B /\ A <> b /\ A <> C /\ A <> c) by (assert_diffs; auto).
destruct HD as [HAB [HAb [HAC HAc]]].
assert (HNC' : ~ Col A b c)
  by (intro; apply HNC; apply out_col in HO1; apply out_col in HO2; ColR).
assert (HCA1 : CongA A B C A b c).
  {
  apply conga_comm, l12_22_a; [auto|apply out_one_side_1 with A; Col|auto].
  }
assert (HCA2 : CongA A C B A c b).
  {
  apply conga_comm, l12_22_a; [auto|apply out_one_side_1 with A; Col|Par].
  }
destruct (incenter_exists_inangle A B C HNC)
  as [I [[_ [HI1 [HI2 HI3]]] [HIn1 [HIn2 HIn3]]]].
destruct (incenter_exists_inangle A b c HNC')
  as [i [[_ [Hi1 [Hi2 Hi3]]] [Hin1 [Hin2 Hin3]]]].
assert (HNB1 : ~ Bet B A C) by (intro; apply HNC; Col).
assert (HNB2 : ~ Bet b A c) by (intro; apply HNC'; Col).
assert (HH1 : HalfA I B A C) by (split; [auto|split; [auto|CongA]]).
assert (HH2 : HalfA I A B C) by (split; [intro; apply HNC; Col|split; [auto|CongA]]).
assert (HH3 : HalfA i b A c) by (split; [auto|split; [auto|CongA]]).
assert (HH4 : HalfA i A b c) by (split; [intro; apply HNC'; Col|split; [auto|CongA]]).
assert (HH5 : HalfA I C A B) by (split; [intro; Between|split; [apply l11_24; auto|CongA]]).
assert (HH6 : HalfA I A C B) by (split; [intro; apply HNC; Col|split; [auto|CongA]]).
assert (HH7 : HalfA i c A b) by (split; [intro; Between|split; [apply l11_24; auto|CongA]]).
assert (HH8 : HalfA i A c b) by (split; [intro; apply HNC'; Col|split; [auto|CongA]]).
destruct (halfa2__EqF A B C b c I i HNC HO1 HO2 HCA1 HH1 HH2 HH3 HH4)
  as [P [p [HC1 [HP1 [HC2 [HP2 HE1]]]]]].
assert (HNC'' : ~ Col A C B) by Col.
destruct (halfa2__EqF A C B c b I i HNC'' HO2 HO1 HCA2 HH5 HH6 HH7 HH8)
  as [Q [q [HC3 [HP3 [HC4 [HP4 HE2]]]]]].
assert (HC5 : Cong I P I Q).
  {
  apply (bisector_perp_equality B A C I P Q); Col; Perp.
  apply inangle__coplanar in HIn2; Cop.
  }
assert (HC6 : Cong i p i q).
  {
  apply (bisector_perp_equality b A c i p q); Col; Perp.
  apply inangle__coplanar in Hin2; Cop.
  }
apply EqF_trans with P I p i; [apply interchange_theorem; auto|].
apply EqF_sym, interchange_theorem, EqF_cong with A C Q I A c q i; Cong.
Qed.

Lemma CongA2__EqF A1 A2 B1 B2 C1 C2 :
  ~ Col A1 B1 C1 ->
  CongA A1 B1 C1 A2 B2 C2 ->
  CongA B1 A1 C1 B2 A2 C2 ->
  EqF A1 B1 A1 C1 A2 B2 A2 C2.
Proof.
intros HNC HCA1 HCA2.
assert (HD : A1 <> B1 /\ A1 <> C1 /\ B1 <> C1 /\
             A2 <> B2 /\ A2 <> C2 /\ B2 <> C2)
  by (assert_diffs; repeat (split; auto)).
destruct HD as [HA1B1 [HA1C1 [HB1C1 [HA2B2 [HA2C2 HB2C2]]]]].
destruct (segment_construction_3 A1 B1 A2 B2) as [B3 [HO1 HC1]]; auto.
destruct (segment_construction_3 A1 C1 A2 C2) as [C3 [HO2 HC2]]; auto.
assert (HE : EqF A2 B2 A2 C2 A1 B3 A1 C3).
  {
  destruct (perp_exists A1 A1 B1) as [C HPerp]; auto.
  assert (HA1C : A1 <> C) by (assert_diffs; auto).
  assert (HA1C3 : A1 <> C3) by (assert_diffs; auto).
  destruct (segment_construction_3 A1 C A2 C2) as [C4 [HO3 HC3]]; auto.
  assert (HA1C4 : A1 <> C4) by (assert_diffs; auto).
  destruct (segment_construction_3 A1 C4 A1 C3) as [C5 [HO4 HC4]]; auto.
  exists A1, B3, C4, A1, B3, C5; do 4 (split; [CongR|]).
  exists B3, C5. split; Cong; split; [apply out_trivial; assert_diffs; auto|].
  split; Cong; split; auto.
  assert (HPerp' : Perp A1 B3 A1 C4)
    by (apply perp_col4 with A1 B1 A1 C; Col; Perp; assert_diffs; auto).
  assert (HPer : Per B3 A1 C4) by Perp.
  assert (HB3C4 : B3 <> C4) by (assert_diffs; apply per_distinct in HPer; auto).
  cut (C4 = C5); [intro; subst; split; Perp; apply par_reflexivity; auto|].
  apply (l6_11_uniqueness A1 A2 C2 C4); [|CongR|apply l6_6; auto|CongR].
  apply out_trivial; auto.
  }
apply EqF_trans with A1 B3 A1 C3; [|apply EqF_sym; auto].
apply interchange_theorem, fundamental_theorem_of_proportion; auto.
apply l12_22_b with A1; auto; [apply out_one_side_1 with A1; Col|].
apply conga_trans with A2 B2 C2; CongA.
assert (HCA4 : CongA B2 A2 C2 B3 A1 C3).
  {
  apply conga_trans with B1 A1 C1; CongA.
  apply out2__conga; apply l6_6; auto.
  }
destruct (l11_49 B2 A2 C2 B3 A1 C3) as [_ HCA5]; Cong.
destruct (HCA5 HB2C2) as [HCA6 _]; CongA.
Qed.

Lemma Per2_EqF_hypo_leg__CongA A B C a b c :
  ~ Col A B C -> ~ Col a b c ->
  Per A B C -> Per a b c ->
  EqF A B a b A C a c ->
  CongA B A C b a c.
Proof.
intros HNC1 HNC2 HPer1 HPer2 HE; assert (HD := HE); apply EqF_diffs in HD.
destruct HD as [HAB [Hab [HAC Hac]]].
destruct (segment_construction_3 A B a b) as [B' [HO1 HC1]]; auto.
destruct (l10_15 A B B' C) as [C'' [HPerp HOS]]; Col.
assert (HBC : B <> C) by (assert_diffs; auto).
assert (HB'C'' : B' <> C'') by (assert_diffs; auto).
assert (Hbc : b <> c) by (assert_diffs; auto).
destruct (segment_construction_3 B' C'' b c) as [C' [HO2 HC2]]; auto.
assert (HOS' : OS A B C C').
  {
  apply one_side_transitivity with C''; [Side|].
  apply out_one_side_1 with B'; Col.
  apply one_side_not_col124 with C; Side.
  }
assert (HPerp' : Perp A B B' C').
  {
  apply perp_col4 with A B B' C''; Col; Perp.
  intro; treat_equalities; apply one_side_not_col124 in HOS'; apply HOS'; Col.
  }
clear C'' HPerp HOS HB'C'' HO2; rename HOS' into HOS; rename HPerp' into HPerp.
assert (HCongA1 : CongA A B' C' a b c).
  {
  apply l11_16; Perp; [|assert_diffs; auto..].
  cut (Perp A B' B' C'); Perp.
  apply perp_col4 with A B B' C'; Col; assert_diffs; auto.
  }
assert (HNC2' : ~ Col A B' C') by (apply ncol_conga_ncol with a b c; CongA).
assert (HPer2' : Per A B' C') by (apply l11_17 with a b c; CongA).
assert (HCongA2 : CongA B' A C' b a c).
  {
  apply l11_49 in HCongA1; Cong.
  destruct HCongA1 as [_ HCongA1].
  destruct HCongA1; [assert_diffs; auto|CongA].
  }
assert (HE' : EqF A B A B' A C A C').
  {
  apply interchange_theorem, EqF_trans with a b a c;
  [apply interchange_theorem; auto|apply EqF_sym].
  apply CongA2__EqF; [|CongA..].
  apply one_side_not_col124 in HOS; intro; apply HOS; ColR.
  }
apply conga_trans with B' A C'; [|CongA].
clear a b c HNC2 HPer2 HE Hab Hac HC1 Hbc HC2 HCongA1 HCongA2.
rename HNC2' into HNC2; rename HPer2' into HPer2; rename HE' into HE.
apply out2__conga; apply l6_6; [auto|].
assert (IPP : inverse_projection_postulate).
  {
  cut tarski_s_parallel_postulate; [|intro; apply euclid].
  apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
  simpl; tauto.
  }
assert (HAcute : Acute B A C) by (apply l11_43_aux; Perp).
assert (HB'C' : B' <> C') by (assert_diffs; auto).
assert (HCop : Coplanar B A C C') by Cop.
destruct (IPP B A C B' C' HAcute HO1 HB'C' HPer2 HCop) as [P [HO2 HCol]].
cut (C' = P); [intro; treat_equalities; auto|].
assert (HC1 : Cong A C' A P).
  {
  apply (Fourth_EqF_uniqueness A B A B' A C); [auto|].
  apply fundamental_theorem_of_proportion; Col.
  apply l12_9 with A B; Cop; Perp.
  apply perp_col4 with B' C' A B; Col; Perp.
  intro; treat_equalities; apply HNC1; ColR.
  }
assert (HC2 : Cong B' C' B' P).
  {
  destruct (cong2_per2__cong_conga2 C' B' A P B' A); Cong; Perp.
  - assert_diffs; auto.
  - cut (Perp A B' B' P); Perp.
    apply perp_col4 with A B B' C'; Col; Perp; [assert_diffs; auto|].
    intro; treat_equalities; apply HNC1; ColR.
  }
assert (HB'P : B' <> P) by (assert_diffs; auto).
apply (l6_11_uniqueness B' B' P P); Cong; [|apply out_trivial; auto].
split; [|split]; [auto..|].
destruct HCol as [|[|HBet]]; Between.
exfalso; apply (l9_9_bis _ _ _ _ HOS).
apply l9_8_2 with P.
- split; [intro; apply HNC1; ColR|].
  split; [intro; apply HNC1; ColR|].
  exists B'; split; [Col|Between].
- apply out_one_side_1 with A; [|Col|apply l6_6; auto].
  intro; apply HNC1; ColR.
Qed.

Lemma Bernays_s_first A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 :
  EqF A1 A2 B1 B2 A3 A4 B3 B4 ->
  EqF B1 B2 C1 C2 B3 B4 C3 C4 ->
  EqF A1 A2 C1 C2 A3 A4 C3 C4.
Proof.
intros HEQ1 HEQ2; apply interchange_theorem.
apply EqF_trans with B1 B2 B3 B4; apply interchange_theorem; auto.
Qed.

Lemma Bernays_s_second A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 :
  EqF A1 A2 B1 B2 B3 B4 A3 A4 ->
  EqF B1 B2 C1 C2 C3 C4 B3 B4 ->
  EqF A1 A2 C1 C2 C3 C4 A3 A4.
Proof.
intros HEQ1 HEQ2.
assert (HA1A2 : A1 <> A2) by (apply EqF_diffs in HEQ1; spliter; auto).
assert (HB1B2 : B1 <> B2) by (apply EqF_diffs in HEQ1; spliter; auto).
assert (HC3C4 : C3 <> C4) by (apply EqF_diffs in HEQ2; spliter; auto).
destruct (Fourth_EqF_exists A1 A2 B1 B2 C3 C4) as [U1 [U2 HEQ3]]; auto.
assert (HEQ4 : EqF C3 C4 U1 U2 A1 A2 B1 B2) by (apply EqF_sym; auto).
assert (HEQ5 : EqF C3 C4 U1 U2 B3 B4 A3 A4)
  by (apply EqF_trans with A1 A2 B1 B2; auto).
assert (HEQ6 : EqF C3 C4 B3 B4 U1 U2 A3 A4)
  by (apply interchange_theorem; auto).
assert (HEQ7 : EqF U1 U2 A3 A4 B1 B2 C1 C2)
  by (apply EqF_sym; apply EqF_trans with C3 C4 B3 B4; auto).
assert (HEQ8 : EqF C3 C4 U1 U2 A1 A2 B1 B2)
  by (apply EqF_trans with B3 B4 A3 A4; auto; apply EqF_sym; auto).
apply EqF_sym; apply Bernays_s_first with U1 U2 B1 B2; auto.
Qed.

Definition EqR C D P Q c d p q :=
  C <> D /\ D <> P /\ Rectangle C D P Q /\
  c <> d /\ d <> p /\ Rectangle c d p q /\
  exists A B E F G H K L M,
    Rectangle A B M L /\ Cong C D A B /\ Cong D P B M /\
    Rectangle B E F G /\ Cong c d B E /\ Cong d p E F /\
    Bet H A L /\ Bet H G F /\ Bet F E K /\ Bet K M L /\
    Bet A B E /\ Bet G B M /\ Bet H B K.

Lemma EqR_diffs A B C D a b c d :
  EqR A B C D a b c d ->
  A <> B /\ B <> C /\ a <> b /\ b <> c.
Proof. intros [HAB [HBC [_ [Hab [Hbc _]]]]]; auto. Qed.

Lemma placed_rects__corner_rect G H I J K L M O :
  G <> H -> H <> I -> H <> K -> K <> L ->
  Rectangle G H I J -> Rectangle H K L M ->
  Bet L K O -> Bet O I J -> Bet G H K -> Bet M H I ->
  H <> O /\ I <> O /\ K <> O /\ Rectangle I H K O.
Proof.
intros HGH HHI HHK HKL HR5 HR6 HB7 HB8 HB9 HB10.
assert (HHO : H <> O).
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram G H I J HR5).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs__pars, (par_not_col _ _ _ _ H) in HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with J; auto.
  }
assert (HIO : I <> O).
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram H K L M HR6).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs_pars_2, (par_not_col _ _ _ _ I) in HPlg; Col.
    apply HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with M; auto.
  }
assert (HIJ : I <> J).
  {
  intro; treat_equalities; apply rect_permut in HR5.
  apply degenerated_rect_eq in HR5; treat_equalities; auto.
  }
assert (HKO : K <> O).
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram G H I J HR5).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs__pars, (par_not_col _ _ _ _ K) in HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with J; auto.
  }
split; [|split; [|split]]; auto.
apply rect_permut, cop_perp3__rect.
- cut (Par O I K H); [Cop|].
  apply par_col4__par with I J G H; Col.
  apply Rectangle_Parallelogram, plg_par in HR5; spliter; Par.
- apply perp_col4 with J I I H; Col.
  cut (Per J I H); [apply per_perp; assert_diffs; auto|].
  apply rect_per3 with G; apply rect_comm2; do 3 apply rect_permut; auto.
- apply perp_col4 with I H H G; Col.
  cut (Per I H G); [apply per_perp; assert_diffs; auto|].
  apply rect_per4 with J; do 2 apply rect_permut; auto.
- apply perp_col4 with H K K L; Col.
  cut (Per H K L); [apply per_perp; assert_diffs; auto|].
  apply rect_per3 with M; do 3 apply rect_permut; auto.
Qed.

Lemma placed_rects_diag__conga G H I J K L M N O :
  G <> H -> H <> I -> H <> K -> K <> L ->
  Rectangle G H I J -> Rectangle H K L M ->
  Bet N G J -> Bet N M L -> Bet L K O -> Bet O I J -> Bet G H K -> Bet M H I ->
  Bet N H O ->
  CongA G N H I H O.
Proof.
intros HGH HHI HHK HKL HR5 HR6 HB5 HB6 HB7 HB8 HB9 HB10 HB11.
destruct (placed_rects__corner_rect G H I J K L M O) as [HHO [HIO _]]; auto.
assert (HIJ : I <> J).
  {
  intro; treat_equalities; apply rect_permut in HR5.
  apply degenerated_rect_eq in HR5; treat_equalities; auto.
  }
assert (HGN : G <> N).
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram H K L M HR6).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs__pars, (par_not_col _ _ _ _ G) in HPlg; Col.
    apply HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with M; auto.
  }
assert (HHN : H <> N).
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram G H I J HR5).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs_pars_2, (par_not_col _ _ _ _ H) in HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with J; auto.
  }
assert (HGJ : G <> J).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR5.
  apply degenerated_rect_eq in HR5; treat_equalities; auto.
  }
assert (HNC : ~ Col G J I)
  by (apply per_not_col; auto; apply rect_per4 with H; auto).
apply conga_trans with G N O.
- apply out2__conga; [apply out_trivial; auto|].
  split; [|split]; Between; assert_diffs; auto.
- apply l12_22_a; [split; [|split]; Between; assert_diffs; auto|..].
  + apply one_side_transitivity with J.
    * apply out_one_side_1 with N; try solve [Col|intro; apply HNC; ColR].
      split; [|split]; Between; assert_diffs; auto.
    * apply out_one_side_1 with O; try solve [Col|intro; apply HNC; ColR].
      split; [|split]; Between; assert_diffs; auto.
  + apply Rectangle_Parallelogram, plg_par in HR5; [spliter|assert_diffs; auto..].
    apply par_col4__par with G J H I; Col; Par; assert_diffs; auto.
Qed.

Lemma rect_extend__rect G H I J P Q :
  Bet G P H -> Bet J Q I -> Cong G P J Q ->
  P <> H -> H <> I -> Rectangle P H I Q ->
  Rectangle J G P Q.
Proof.
intros HB1 HB2 HC HPH HHI HR.
elim (eq_dec_points G P); [intro; treat_equalities|intro HGP].
- apply rect_permut, Rectangle_triv.
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR; auto.
- apply rect_permut, sac_rectangle; split; [|split; [|split]]; Cong.
  + apply l8_3 with I; [apply rect_per3 with H, rect_permut; auto| |Col].
    intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR; auto.
  + apply l8_2, l8_3 with H; [apply rect_per1 with I|..]; Col.
  + assert (HNC1 : ~ Col P Q H).
      {
      cut (~ Col H P Q); [Col|apply per_not_col; [auto|..]].
      - intro; treat_equalities.
        apply rect_permut, rect_permut, degenerated_rect_eq in HR; auto.
      - apply rect_per1 with I; auto.
      }
    assert (HNC2 : ~ Col P Q I).
      {
      apply per_not_col; [assert_diffs; auto| |apply rect_per4 with H; auto].
      intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR; auto.
      }
    apply l9_8_1 with I; [|apply l9_2, l9_8_2 with H].
    * split; [intro; apply HNC2; ColR|].
      split; [Col|exists Q; split; [Col|Between]].
    * split; [Col|split; [intro; apply HNC1; ColR|]].
      exists P; split; [Col|Between].
    * apply l12_6, par_not_col_strict with H; Col.
      apply Rectangle_Parallelogram, plg_par in HR; spliter; Par.
Qed.

Lemma Bet_Rect2__Bet A B C D E F :
  Bet B C E ->
  Rectangle A B C D -> Rectangle D C E F ->
  Bet A D F.
Proof.
intros HB HR1 HR2.
elim (eq_dec_points A D); [intro; treat_equalities; Between|intro HAD].
elim (eq_dec_points D F); [intro; treat_equalities; Between|intro HDF].
elim (eq_dec_points A B); [intro|intro HAB].
- apply Rectangle_Parallelogram, plg_cong in HR1.
  apply Rectangle_Parallelogram, plg_cong in HR2.
  spliter; treat_equalities; Between.
- assert (HBC : B <> C).
    {
    apply Rectangle_Parallelogram, plg_cong in HR1.
    apply Rectangle_Parallelogram, plg_cong in HR2.
    intro; spliter; treat_equalities; auto.
    }
  assert (HCD : C <> D).
    {
    apply Rectangle_Parallelogram, plg_cong in HR1.
    apply Rectangle_Parallelogram, plg_cong in HR2.
    intro; spliter; treat_equalities; auto.
    }
  assert (HCE : C <> E).
    {
    apply Rectangle_Parallelogram, plg_cong in HR1.
    apply Rectangle_Parallelogram, plg_cong in HR2.
    intro; spliter; treat_equalities; auto.
    }
  apply col_two_sides_bet with C; [apply par_id|].
  + apply Rectangle_Parallelogram, plg_par in HR1; auto.
    spliter; apply par_trans with B C; Par.
    apply Rectangle_Parallelogram, plg_par in HR2; auto.
    apply par_col4__par with C E D F; Col; spliter; Par.
  + assert (HNC1 : ~ Col B C D)
      by (apply per_not_col; auto; apply rect_per3 with A; auto).
    assert (HNC2 : ~ Col D C E)
      by (apply per_not_col; auto; apply rect_per2 with F; auto).
    apply l9_8_2 with B; [apply l9_2, l9_8_2 with E|]; [|apply l12_6..].
    * split; [Col|split; [Col|exists C; split; [Col|Between]]].
    * apply par_not_col_strict with E; [|Col..].
      apply Rectangle_Parallelogram, plg_par in HR2; spliter; Par.
    * apply par_not_col_strict with B; [|Col..].
      apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
Qed.

Lemma CongA_OS_ParTS__Bet A B C a b :
  CongA a A B b B C -> OS A B a b -> Par A a B b -> TS b B A C ->
  Bet A B C.
Proof.
intros HC1 HOS HP HTS.
elim (eq_dec_points B C); [intro; treat_equalities; Between|intro HBC].
assert (HNC1 : ~ Col a A B) by (apply one_side_not_col123 in HOS; Col).
assert (HNC2 : ~ Col b B C)
  by (intro HF; apply HNC1, col_conga_col with b B C; CongA).
apply (par_not_col_strict _ _ _ _ B) in HP; Col.
destruct (point_construction_different A B) as [C' [HC' HBC']].
assert (HC2 : CongA a A B b B C').
  {
  apply conga_trans with a A C'.
  - apply out2__conga; [apply out_trivial; assert_diffs; auto|].
    assert_diffs; repeat (split; Between).
  - apply l12_22_a; [assert_diffs; repeat (split; Between)| |Par].
    apply col2_os__os with A B; Col; assert_diffs; auto.
  }
assert (HC3 : CongA b B C b B C') by (apply conga_trans with a A B; CongA).
apply conga_os__out in HC3.
- apply between_symmetry, (bet_out__bet C' C A B); [|apply l6_6]; Between.
- apply l9_8_1 with A; [Side|split].
  + cut (~ Col b B C'); [Col|apply ncol_conga_ncol with a A B; Col].
  + split; [apply (par_not_col _ _ _ _ A) in HP; Col|].
    exists B; split; [Col|Between].
Qed.

Lemma B5_2_1_1 A B C D a b c d :
  Rectangle A B C D -> Rectangle a b c d ->
  EqR A B C D a b c d -> EqF A B a b b c B C.
Proof.
intros RABCD Rabcd HR.
assert (HD : A <> B /\ a <> b /\ B <> C /\ b <> c)
  by (apply EqR_diffs in HR; spliter; auto).
destruct HD as [HNbc [HNBC [HNab HNAB]]].
destruct HR as [_ [_ [_ [_ [_ [_ HR]]]]]].
destruct HR as [I [J [E [F [G [H [K [L [M HR]]]]]]]]].
destruct HR as [HR1 [HC1 [HC2 [HR2 [HC3 [HC4 HR]]]]]].
destruct HR as [HB1 [HB2 [HB3 [HB4 [HB5 [HB6 HB7]]]]]].
assert (HD : I <> J /\ J <> M /\ J <> E /\ E <> F)
  by (assert_diffs; repeat split; auto).
destruct HD as [HIJ [HJM [HJE HEF]]].
destruct (placed_rects__corner_rect I J M L E F G K)
  as [_ [HMK [_ HR3]]]; auto.
assert (HJG : J <> G).
  {
  intro; treat_equalities.
  apply rect_comm2, degenerated_rect_eq in HR2; auto.
  }
assert (HIL : I <> L).
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR1; auto.
  }
destruct (placed_rects__corner_rect E J G F I L M H)
  as [_ [HGH [HIH HR4]]]; try solve [Between|apply rect_comm2; auto].
assert (HCA1 : CongA I H J M J K)
  by (apply (placed_rects_diag__conga I J M L E F G H K); auto).
assert (HEQF : EqF M J M K I H I J).
  {
  apply CongA2__EqF; [|CongA|].
  - cut (~ Col J M K); [Col|].
    apply per_not_col; [intro; subst; auto..|apply rect_per1 with E; auto].
  - apply l11_16; try solve [intro; subst; auto].
    + apply rect_per1 with E; auto.
    + apply l8_2, rect_per3 with G; auto.
  }
apply EqF_abcd_badc, interchange_theorem in HEQF.
destruct HEQF as [N [O [P [n [o [p [HC5 [HC6 [HC7 [HC8 HE]]]]]]]]]].
assert (HC9 : Cong I H b c).
  {
  apply Rectangle_Parallelogram, plg_cong in HR2.
  apply Rectangle_Parallelogram, plg_cong in HR4; spliter; CongR.
  }
assert (HC10 : Cong M K a b)
  by (apply Rectangle_Parallelogram, plg_cong in HR3; spliter; CongR).
apply EqF_abcd_badc.
exists N, O, P, n, o, p; do 4 (split; [CongR|]); assumption.
Qed.

Lemma B5_2_1_2 A B C D a b c d :
  Rectangle A B C D -> Rectangle a b c d ->
  EqF A B a b b c B C -> EqR A B C D a b c d.
Proof.
intros RABCD Rabcd HE.
assert (H : EqF a b A B B C b c) by (apply EqF_abcd_badc; auto).
destruct H as [N [O [P [n [o [p [H1 [H2 [H3 [H4 H5]]]]]]]]]].
destruct (segment_construction A B a b) as [E [HABE HC1]].
destruct (segment_construction C B b c) as [G [HGBC HC2]].
destruct (segment_construction D C a b) as [K [HKML HC3]].
destruct (segment_construction D A b c) as [H [HHAL HC4]].
destruct (segment_construction K E b c) as [F [HKEF HC5]].
assert (HD : A <> B /\ B <> C /\ a <> b /\ b <> c)
  by (apply EqRT_diffs in H5; spliter; assert_diffs; auto).
destruct HD as [HAB [HBC [Hab Hbc]]].
do 6 (split; auto); exists A, B, E, F, G, H, K, D, C.
assert (HBE : B <> E) by (assert_diffs; auto).
assert (HBG : B <> G) by (assert_diffs; auto).
assert (HCD : C <> D).
  {
  intro; treat_equalities.
  apply rect_permut in RABCD.
  apply degenerated_rect_eq in RABCD; auto.
  }
assert (HCK : C <> K) by (assert_diffs; auto).
assert (HPer1 : Per C B E).
  {
  apply rect_per in RABCD; spliter.
  apply per_suppa__per with A B C; auto.
  apply bet__suppa; auto.
  }
assert (HPer3 : Per B C K).
  {
  apply rect_per in RABCD; spliter.
  apply per_suppa__per with D C B; Perp.
  apply bet__suppa; auto.
  }
assert (HPar1 : Par A D B C)
  by (apply Rectangle_Parallelogram in RABCD; apply plg_par_2 in RABCD; auto).
assert (HPar2 : Par A B C D)
  by (apply Rectangle_Parallelogram in RABCD; apply plg_par_1 in RABCD; auto).
assert (HPar3 : Par B E C K) by (apply par_col4__par with A B C D; Col).
assert (HEK : E <> K)
  by (intro; treat_equalities; apply per_not_col in HPer1; Col).
assert (HC6 : Cong B E K C) by (apply cong_inner_transitivity with a b; Cong).
assert (HAD : A <> D)
  by (intro; treat_equalities; apply rect_permut, rect_permut, degenerated_rect_eq in RABCD; auto).
assert (HR1 : Rectangle B E K C).
  {
  apply rect_comm2, rect_permut, (rect_extend__rect E A D K B C); Between; Cong.
  apply rect_comm2; assumption.
  }
assert (HR2 : Rectangle B E F G).
  {
  apply rect_comm2, rect_permut, rect_permut, (rect_extend__rect F K C G E B); Between; [CongR|].
  apply rect_permut; assumption.
  }
do 6 (split; Cong).
assert (HPer5 : Per H A B).
  {
  apply rect_per in RABCD; spliter.
  apply per_suppa__per with B A D; Perp.
  apply suppa_sym, bet__suppa; Between; assert_diffs; auto.
  }
assert (HPer6 : Per G B A).
  {
  apply rect_per in RABCD; spliter.
  apply per_suppa__per with A B C; Perp.
  apply suppa_sym, bet__suppa; Between; assert_diffs; auto.
  }
assert (HR3 : Rectangle A B G H).
  {
  apply rect_comm2, rect_permut, rect_permut, (rect_extend__rect G C D H B A); Between; [CongR|].
  apply rect_permut; assumption.
  }
assert (HHGF : Bet H G F).
  {
  apply (Bet_Rect2__Bet H A B G E F); [assumption| |];
  apply rect_permut, rect_permut, rect_permut; assumption.
  }
repeat (split; Between).
assert (HTS: TS B C H K).
  {
  assert (HAH : A <> H) by (assert_diffs; auto).
  assert (HNC1 : ~ Col B C E) by (apply per_not_col in HPer1; Col).
  assert (HNC2 : ~ Col A B C) by (intro; apply HNC1; ColR).
  assert (HOS1 : OS B C A H).
    {
    apply l12_6, par_not_col_strict with A; Col.
    apply par_col4__par with B C A D; Col.
    apply Rectangle_Parallelogram in RABCD.
    apply plg_par in RABCD; spliter; Par.
    }
  apply l9_8_2 with A; [|Side].
  assert (HOS2 : OS B C A D).
    {
    apply l12_6, par_not_col_strict with A; Col.
    apply Rectangle_Parallelogram in RABCD.
    apply plg_par in RABCD; spliter; Par.
    }
  apply l9_8_2 with D; [|Side].
  assert (HNC3 : ~ Col B C D).
    {
    keep RABCD HAB HBC HCD HPar1 HPar2 HNC2 HOS2.
    apply per_not_col; [assert_diffs; auto..|].
    apply rect_per3 with A; auto.
    }
  assert (HNC4 : ~ Col K B C) by (intro; apply HNC3; ColR).
  split; [Col|]; split; [Col|].
  exists C; split; [Col|Between].
  }
apply interchange_theorem in HE.
clear H1 H2 H3 H4 H5 N O P n o p.
destruct HE as [N [O [P [n [o [p HE]]]]]].
destruct HE as [HC7 [HC8 [HC9 [HC10 HE']]]].
assert (HE : EqF A B A H C K C B)
  by (exists N, O, P, n, o, p; do 4 (split; [CongR|]); auto).
assert (HCongA1 : CongA A H B C B K)
  by (destruct (Per2_EqF__CongA A B H C K B); CongA; Perp).
assert (HOS : OS H B A C).
  {
  assert (HNC : ~ Col A B G)
    by (apply per_not_col; Perp; assert_diffs; auto).
  apply l9_8_1 with G.
  - apply invert_two_sides.
    assert (HP := Rectangle_Parallelogram A B G H HR3).
    apply plg_par in HP; [destruct HP as [HP1 HP2]|assumption..].
    destruct (l12_19 A B G H) as [_ [_ [HTS' _]]]; [assumption|Par|Par|assumption].
  - assert (HNC1 : ~ Col B C E) by (apply per_not_col in HPer1; Col).
    assert (HNC2 : ~ Col B C H) by (apply two_sides_not_col with K; Side).
    split; [intro; apply HNC2; ColR|].
    split; [|exists B; split; [Col|Between]].
    cut (~ Col B G H); [Col|].
    apply per_not_col; [auto| |apply rect_per3 with A; assumption].
    intro; treat_equalities; apply rect_permut, degenerated_rect_eq in HR3; auto.
  }
apply (CongA_OS_ParTS__Bet H B K A C); [assumption..| |Side].
apply par_col4__par with A D B C; Col; assert_diffs; auto.
Qed.

Lemma B5_2_1 A B C D a b c d :
  Rectangle A B C D -> Rectangle a b c d ->
  EqR A B C D a b c d <-> EqF A B a b b c B C.
Proof. intros; split; [apply B5_2_1_1|apply B5_2_1_2]; auto. Qed.

Lemma B5_2_2 A B C D a b c d :
  Rectangle A B C D -> Rectangle a b c d ->
  EqR A B C D a b c d <-> EqF A B b c a b B C.
Proof.
intros HR1 HR2; rewrite B5_2_1; auto.
split; intro HEQ; apply interchange_theorem; auto.
Qed.

Lemma EqRT_BAC_BAC A B C : A <> B -> B <> C -> Per A B C -> EqRT B A C B A C.
Proof.
intros HNAB HNBC HP.
unfold EqRT.
exists A, C.
split; Cong.
split. apply out_trivial; auto.
split; Cong.
split. apply out_trivial; auto.
split; Perp.
apply par_reflexivity.
intro; treat_equalities; apply l8_8 in HP; auto.
Qed.

Lemma EqR_sym A B C D E F G H : EqR A B C D E F G H -> EqR E F G H A B C D.
Proof.
intro H1.
assert (HR1 : Rectangle A B C D) by (destruct H1 as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]; auto).
assert (HR2 : Rectangle E F G H) by (destruct H1 as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]; auto).
apply B5_2_1; auto.
apply B5_2_1 in H1; auto.
apply EqF_abcd_badc; auto.
Qed.

Lemma EqR_refl A B C D : A <> B -> B <> C -> Rectangle A B C D -> EqR A B C D A B C D.
Proof.
intros HNAB HNBC HR.
apply B5_2_1; auto.
apply interchange_theorem.
unfold EqF.
exists B, A, C, B, A, C.
do 4 (split; Cong).
apply EqRT_BAC_BAC; auto.
apply rect_per2 in HR; auto.
Qed.

Lemma EqR_trans A B C D E F G H I J K L :
  EqR A B C D E F G H ->
  EqR E F G H I J K L ->
  EqR A B C D I J K L.
Proof.
intros HEQR1 HEQR2.
assert (HR1 : Rectangle A B C D) by (destruct HEQR1 as [H1 [H2 [H3 H4]]]; auto).
assert (HR2 : Rectangle E F G H) by (destruct HEQR2 as [H1 [H2 [H3 H4]]]; auto).
assert (HR3 : Rectangle I J K L) by (destruct HEQR2 as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]; auto).
apply B5_2_1; auto.
apply B5_2_1 in HEQR1; auto.
apply B5_2_1 in HEQR2; auto.
apply Bernays_s_second with E F F G; auto.
Qed.

Lemma EqR_abcd_bcda A B C D : A <> B -> B <> C -> Rectangle A B C D -> EqR A B C D B C D A.
Proof.
(* This simplifies the paper's proof of Lemma 5.4, which places the rectangles
   as in Fig. 9 and shows that B is the common midpoint of the diagonals.
   By Lemma 5.2 (B5_2_1), it is enough to show AB : BC = CD : BC, which is
   trivial since CD = AB.  The same applies to EqR_abcd_adcb. *)
intros HNAB HNBC HR.
apply B5_2_1; auto.
apply rect_permut; auto.
unfold EqF.
exists B, A, C, B, A, C.
assert (HC1 :Cong A B C D) by (apply Rectangle_Parallelogram in HR; apply plg_cong_1; auto).
do 4 (split; Cong).
apply EqRT_BAC_BAC; auto.
apply rect_per2 in HR; auto.
Qed.

Lemma EqR_abcd_adcb A B C D : A <> B -> B <> C -> Rectangle A B C D -> EqR A B C D A D C B.
Proof.
intros HNAB HNBC HR.
apply B5_2_1; auto.
apply rect_permut; apply rect_comm2; auto.
assert (HP : Parallelogram A B C D) by (apply Rectangle_Parallelogram in HR; auto).
apply plg_cong in HP; spliter.
unfold EqF.
exists A, B, D, A, B, D.
do 4 (split; Cong).
apply EqRT_BAC_BAC; auto.
intro; treat_equalities; auto.
apply rect_per1 in HR; auto.
Qed.

Lemma EqR_perm A B C D :
  A <> B -> B <> C -> Rectangle A B C D ->
  EqR A B C D A B C D /\ EqR A B C D B C D A /\
  EqR A B C D C D A B /\ EqR A B C D D A B C /\
  EqR A B C D A D C B /\ EqR A B C D D C B A /\
  EqR A B C D C B A D /\ EqR A B C D B A D C.
Proof.
intros HNAB HNBC HR.
assert (HNAD : A <> D).
  {
  intro; treat_equalities.
  do 2 (apply rect_permut in HR).
  apply degenerated_rect_eq in HR; auto.
  }
assert (HNCD : C <> D)
  by (intro; treat_equalities;
      apply rect_permut, degenerated_rect_eq in HR; auto).
split; [apply EqR_refl; auto|].
assert (HE1 : EqR A B C D B C D A) by (apply EqR_abcd_bcda; auto).
assert (HE2 : EqR A B C D C D A B).
  {
  apply EqR_trans with B C D A; auto.
  apply EqR_abcd_bcda; auto.
  apply rect_permut; auto.
  }
assert (HE3 : EqR A B C D D A B C).
  {
  apply EqR_trans with C D A B; auto.
  apply EqR_abcd_bcda; auto.
  do 2 apply rect_permut; auto.
  }
assert (HE4 : EqR A B C D A D C B) by (apply EqR_abcd_adcb; auto).
assert (HE5 : EqR A B C D D C B A).
  {
  apply EqR_trans with A D C B; auto.
  apply EqR_abcd_bcda; auto.
  apply rect_comm2, rect_permut, rect_permut, rect_permut; auto.
  }
assert (HE6 : EqR A B C D C B A D).
  {
  apply EqR_trans with D C B A; auto.
  apply EqR_abcd_bcda; auto.
  apply rect_comm2, rect_permut, rect_permut; auto.
  }
assert (HE7 : EqR A B C D B A D C).
  {
  apply EqR_trans with C B A D; auto.
  apply EqR_abcd_bcda; auto.
 apply rect_comm2, rect_permut; auto.
  }
tauto.
Qed.

Lemma B5_5 A B C D E F G H :
  A <> B -> B <> C ->
  Rectangle A B C D -> Rectangle E F G H -> Cong A B E F ->
  EqR A B C D E F G H <-> Cong B C F G.
Proof.
intros HNAB HNBC HR1 HR2 HC1.
split; intro HEQR.
- destruct (EqR_diffs A B C D E F G H) as [_ [_ [HEF HFG]]]; auto.
  apply B5_2_1 in HEQR; auto.
  apply (Fourth_EqF_uniqueness A B E F F G); [assumption|].
  apply interchange_theorem.
  exists F, E, G, F, E, G; do 4 (split; Cong).
  apply EqRT_BAC_BAC; auto.
  apply rect_per2 in HR2; auto.
- apply B5_2_1; auto.
  apply interchange_theorem.
  exists B, A, C, B, A, C; do 4 (split; Cong).
  apply EqRT_BAC_BAC; auto.
  apply rect_per2 in HR1; auto.
Qed.

Lemma B5_6 A B C D a b c d :
  A <> B -> B <> C -> a <> b -> b <> c ->
  Rectangle A B C D -> Rectangle a b c d -> Lt a b A B -> Lt b c B C ->
  ~ EqR A B C D a b c d.
Proof.
intros HNAC HNBC HNab HNbc RABCD Rabcd HLAa HLBb H.
assert (HLeAa : Le a b A B) by (destruct HLAa; auto).
assert (HLeBb : Le b c B C) by (destruct HLBb; auto).
destruct HLAa as [HLAa1 HNC1].
destruct HLBb as [HLBb1 HNC2].
destruct HLAa1 as [E [HBet1 HC1]].
destruct HLBb1 as [F [HBet2 HC2]].
apply B5_2_1 in H; auto.
apply interchange_theorem in H.
destruct H as [G [H [I [g [h [i HEQT]]]]]]; spliter.
destruct H4 as [J [K HI]]; spliter.

assert (HNIK : I <> K).
  {
  intro; treat_equalities.
  assert (HC : Cong B C b c)
    by (apply cong_transitivity with G I; auto; apply cong_transitivity with g i; auto; Cong).
  CongR.
  }
assert (HNGI : G <> I) by (intro; treat_equalities; apply out_diff1 in H7; auto).
assert (HNCol1 : ~ Col G H I).
  {
  intro; treat_equalities.
  apply perp_in_comm, perp_in_right_comm, perp_in_per, per_not_col in H8; Col.
  assert_diffs; auto.
  }

assert (HNCol2 : ~ Col K I H).
  {
  intro; treat_equalities.
  assert (HCol1 : Col I G H) by (apply col_transitivity_1 with K; auto; Col).
  ColR.
  }

assert (HBet3 : Bet G I K).
  {
  apply l6_13_1; auto.
  apply l5_6 with b c B C; Cong.
  apply cong_transitivity with g i; Cong.
  }
assert (HBet4 : Bet G J H).
  {
  apply l6_13_1.
  apply l6_6; auto.
  apply l5_6 with a b A B; Cong.
  apply cong_transitivity with g h; Cong.
  }

assert (HX : exists X : Tpoint, Bet J X K /\ Bet I X H) by (apply inner_pasch with G; Between).
destruct HX as [X [HBet5 HBet6]].

assert (HI :Inter I H J K X).
unfold Inter; split; auto.
assert_diffs; auto.
split.
exists K; split; Col.
split; apply bet_col in HBet5; apply bet_col in HBet6; Col.
assert (HNP : ~ Par H I J K) by (apply inter__npar with X; apply inter_left_comm; auto).
Par.
Qed.

Lemma rect_cut__rect A B C D E F :
  Bet B C E -> B <> C -> D <> C -> C <> E -> A <> B -> B <> E ->
  Rectangle D C E F -> Rectangle A B E F ->
  D <> F /\ E <> F /\ A <> F /\ Bet A D F /\ Rectangle A B C D.
Proof.
intros HB1 HBC HDC HCE HAB HBE HR1 HR2.
assert (HDF : D <> F).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR1.
  apply degenerated_rect_eq in HR1; auto.
  }
assert (HEF : E <> F).
  {
  intro; treat_equalities; apply rect_permut in HR1.
  apply degenerated_rect_eq in HR1; auto.
  }
assert (HAF : A <> F).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR2.
  apply degenerated_rect_eq in HR2; auto.
  }
assert (HB3 : Bet A D F).
  {
  assert (HCol : Col A D F).
    {
    cut (Col F A D); Col.
    cut (Par F A F D); [apply par_id|].
    apply par_trans with B E.
    - apply plg_par_1; auto.
      do 3 apply plg_permut; apply Rectangle_Parallelogram; auto.
    - apply par_col4__par with C E F D; Col.
      apply plg_par_1; auto.
      apply plg_permut; apply Rectangle_Parallelogram; auto.
    }
  apply col_two_sides_bet with C; [Col|].
  assert (HNC : ~ Col D C E)
    by (apply per_not_col; [..|apply rect_per2 with F]; auto).
  apply l9_8_2 with B; [apply l9_2, l9_8_2 with E|].
  - split; [intro; apply HNC; ColR|].
    split; [intro; apply HNC; ColR|].
    exists C; split; [Col|Between].
  - apply l12_6, ncol123_plg__pars1234; [Col|].
    apply Rectangle_Parallelogram; auto.
  - apply l12_6, par_not_col_strict with B; [|Col|].
    + apply par_trans with E F.
      * apply plg_par_1; [..|apply Rectangle_Parallelogram]; auto.
      * cut (Par A B E F); [Par|].
        apply plg_par_1; [..|apply Rectangle_Parallelogram]; auto.
    + intro HF; apply HBC; apply l6_21 with D C E C; Col.
  }
assert (HR5 : Rectangle A B C D).
  {
  apply plg_per_rect2.
  - apply parallelogram_to_plg; do 3 apply plg_permut.
    assert (HC : Cong B C A D).
      {
      apply l4_3 with E F; Between;
      apply plg_cong_2, plg_comm2, Rectangle_Parallelogram; auto.
      }
    apply plg_out_plg with E F; Cong.
    + apply plg_permut, Rectangle_Parallelogram; auto.
    + split; [|split]; Between.
    + split; [auto|split]; assert_diffs; Between.
  - cut (Perp A B B C); Perp.
    apply perp_col4 with A B B E; Col.
    cut (Per A B E); [apply per_perp; assert_diffs; auto|].
    apply rect_per2 with F; auto.
  }
repeat (split; [assumption|]); assumption.
Qed.

Lemma rect_cut_exists A B C D P :
  A <> B -> B <> C -> Rectangle A B C D -> Bet A P B -> A <> P -> P <> B ->
  exists Q, Bet D Q C /\ Rectangle A P Q D /\ Rectangle P B C Q.
Proof.
intros HAB HBC HR HB HAP HPB.
destruct (plg_existence P B C) as [Q HPlg]; [auto|].
assert (HR1 : Rectangle P B C Q).
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  apply per_col with A; [auto|apply l8_2, rect_per2 with D; auto|Col].
  }
assert (HAD : A <> D)
  by (intro; treat_equalities; apply rect_permut, rect_permut, degenerated_rect_eq in HR; auto).
assert (HPQ : P <> Q)
  by (intro; treat_equalities; apply rect_permut, rect_permut, degenerated_rect_eq in HR1; auto).
destruct (rect_cut__rect D A P Q B C) as [_ [_ [_ [HB1 HR2]]]];
  try solve [auto|intro; subst; auto|apply rect_permut; assumption
            |do 3 apply rect_permut; assumption].
exists Q; split; [assumption|split; [|assumption]].
apply rect_permut; assumption.
Qed.

Lemma placed_rects__rect G H I J K L M N O :
  G <> H -> H <> I -> H <> K -> K <> L ->
  Rectangle G H I J -> Rectangle H K L M ->
  Bet N G J -> Bet N M L -> Bet L K O -> Bet O I J -> Bet G H K -> Bet M H I ->
  Cong O I M L /\ Cong N G K L /\ Per N G H /\ Per N J O /\ Per H I O.
Proof.
intros HGH HHI HHK HKL HR1 HR2 HB1 HB2 HB3 HB4 HB5 HB6.
assert (HGJ : G <> J).
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR1; auto.
  }
assert (HHM : H <> M).
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR2; auto.
  }
assert (HLM : L <> M).
  {
  intro; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR2; auto.
  }
split; [|split; [|split; [|split]]].
- apply t22_8__cong with K H; Between.
  + split; [|split; [|split]].
    * apply rect_per2 with K, rect_permut, rect_permut; auto.
    * apply rect_per2 with L; do 3 apply rect_permut; auto.
    * apply Rectangle_Parallelogram, plg_cong in HR2; spliter; Cong.
    * apply l12_6, ncol234_plg__pars1423.
      -- cut (~ Col H K L); [Col|].
         apply per_not_col; auto; apply rect_per2 with M; auto.
      -- apply plg_comm2, plg_permut, plg_permut.
         apply Rectangle_Parallelogram; auto.
  + apply l8_3 with H; Col; apply l8_2, l8_3 with J; Col.
    * apply rect_per1 with G, rect_permut, rect_permut; auto.
    * intro; treat_equalities; apply rect_permut in HR1.
      apply degenerated_rect_eq in HR1; auto.
  + apply rect_per1 with H, rect_permut, rect_permut; auto.
- apply t22_8__cong with M H; Between.
  + split; [|split; [|split]].
    * apply rect_per1 with M, rect_permut; auto.
    * apply rect_per4 with L, rect_permut; auto.
    * apply Rectangle_Parallelogram, plg_cong in HR2; spliter; Cong.
    * apply l12_6, ncol234_plg__pars1423.
      -- apply per_not_col; auto.
         apply rect_per2 with K, rect_permut, rect_permut; auto.
      -- apply plg_permut, Rectangle_Parallelogram; auto.
  + apply l8_3 with H; Col; apply l8_2, l8_3 with J; Col.
    apply rect_per2 with I; do 3 apply rect_permut; auto.
  + apply rect_per2 with H, rect_permut; auto.
- elim (eq_dec_points G N); [intro; treat_equalities; Perp|intro HGN].
  cut (Perp N G G H); [Perp|].
  apply perp_col4 with J G G H; Col.
  cut (Per J G H); [apply per_perp; [|assert_diffs; auto]|].
  + intro; treat_equalities; apply rect_permut, rect_permut in HR1.
    apply degenerated_rect_eq in HR1; treat_equalities; auto.
  + apply rect_per2 with I; do 3 apply rect_permut; auto.
- elim (eq_dec_points J N); [intro; treat_equalities; Perp|intro HJN].
  elim (eq_dec_points J O); [intro; treat_equalities; Perp|intro HJO].
  cut (Perp N J J O); [Perp|].
  apply perp_col4 with G J J I; Col.
  cut (Per G J I); [apply per_perp|].
  + intro; treat_equalities; apply rect_permut, rect_permut in HR1.
    apply degenerated_rect_eq in HR1; treat_equalities; auto.
  + intro; treat_equalities; apply rect_permut in HR1.
    apply degenerated_rect_eq in HR1; treat_equalities; auto.
  + apply rect_per1 with H; do 3 apply rect_permut; auto.
- elim (eq_dec_points I O); [intro; treat_equalities; Perp|intro HIO].
  cut (Perp H I I O); [Perp|].
  apply perp_col4 with H I I J; Col.
  cut (Per H I J); [apply per_perp; auto|].
  + intro; treat_equalities; apply rect_permut in HR1.
    apply degenerated_rect_eq in HR1; treat_equalities; auto.
  + apply rect_per2 with G, rect_permut; auto.
Qed.

Lemma EqR_placed__bet G H I J K L M N O :
  EqR G H I J H K L M ->
  Bet N G J -> Bet N M L -> Bet L K O ->
  Bet O I J -> Bet G H K -> Bet M H I ->
  Bet N H O.
Proof.
intros HE HB1 HB2 HB3 HB4 HB5 HB6.
destruct HE as [HGH [HHI [HR1 [HHK [HKL [HR2 HE]]]]]].
destruct HE as [G' [H' [K' [L' [M' [N' [O' [J' [I' HE]]]]]]]]].
destruct HE as [HR3 [HC1 [HC2 [HR4 [HC3 [HC4 HE]]]]]].
destruct HE as [HB7 [HB8 [HB9 [HB10 [HB11 [HB12 HB13]]]]]].
destruct (placed_rects__rect G H I J K L M N O)
  as [HC5 [HC6 [HP1 [HP2 HP3]]]]; auto.
destruct (placed_rects__rect G' H' I' J' K' L' M' N' O')
  as [HC5' [HC6' [HP1' [HP2' HP3']]]]; Between; assert_diffs; auto.
assert (HC7 : Cong O I O' I').
  {
  apply Rectangle_Parallelogram, plg_cong in HR2.
  apply Rectangle_Parallelogram, plg_cong in HR4; spliter; CongR.
  }
assert (HC8 : Cong N G N' G').
  {
  apply Rectangle_Parallelogram, plg_cong in HR2.
  apply Rectangle_Parallelogram, plg_cong in HR4; spliter; CongR.
  }
apply (l4_6 N' H' O'); Between; split; [|split].
- apply l10_12 with G' G; Cong.
- apply l10_12 with J' J; Cong.
  + apply l2_11 with G' G; Between; Cong.
    apply Rectangle_Parallelogram, plg_cong in HR1.
    apply Rectangle_Parallelogram, plg_cong in HR3; spliter; CongR.
  + apply l2_11 with I' I; Between; Cong.
    apply Rectangle_Parallelogram, plg_cong in HR1.
    apply Rectangle_Parallelogram, plg_cong in HR3; spliter; CongR.
- apply l10_12 with I' I; Cong.
Qed.

Lemma placed_rects_cut__figure G H I J K L M N O P R :
  G <> H -> H <> I -> H <> K -> K <> L ->
  Rectangle G H I J -> Rectangle H K L M ->
  Bet N G J -> Bet N M L -> Bet L K O -> Bet O I J -> Bet G H K -> Bet M H I ->
  Bet G P H -> G <> P -> H <> P -> Bet L R K -> L <> R -> K <> R ->
  exists Q S T U V,
    Rectangle I H P Q /\ Rectangle J G P Q /\ Bet J Q I /\
    Rectangle H K R S /\ Rectangle M L R S /\ Bet M S H /\
    Rectangle I H K O /\ Rectangle H P T S /\ Rectangle G P T U /\
    Rectangle M S T V /\ Rectangle N U T V /\
    Bet T P Q /\ Bet T S R /\ Bet U T S /\ Bet V T P /\ Bet N U G /\ Bet N V M /\
    P <> T /\ S <> T /\ M <> S /\ H <> S /\ K <> O /\ T <> U /\ G <> U.
Proof.
intros HGH HHI HHK HKL HR7 HR8 HB5 HB6 HB7 HB8 HB9 HB10 HB12 HGP HHP HB14 HLR HKR.
assert (HGJ : G <> J).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR7.
  apply degenerated_rect_eq in HR7; treat_equalities; auto.
  }
assert (HLM : L <> M).
  {
  intro; treat_equalities; apply rect_permut in HR8.
  apply degenerated_rect_eq in HR8; treat_equalities; auto.
  }
destruct (rect_cut_exists G H I J P) as [Q [HB13 [HQ1 HQ2]]]; auto.
destruct (rect_cut_exists L K H M R) as [S [HB15 [HS1 HS2]]];
  try solve [Between|intro; subst; auto|apply rect_comm2, rect_permut; assumption].
assert (HR9 : Rectangle I H P Q) by (apply rect_comm2, rect_permut; assumption).
assert (HR10 : Rectangle J G P Q) by (do 3 apply rect_permut; assumption).
assert (HR11 : Rectangle H K R S) by (apply rect_comm2, rect_permut; assumption).
assert (HR12 : Rectangle M L R S) by (do 3 apply rect_permut; assumption).
destruct (placed_rects__corner_rect G H I J K L M O) as [_ [HIO [HKO HR13]]]; auto.
assert (HMS : M <> S).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR12.
  apply degenerated_rect_eq in HR12; auto.
  }
assert (HHS : H <> S).
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR11; auto.
  }
destruct (plg_existence S H P) as [T HP]; auto.
assert (HR14 : Rectangle H P T S).
  {
  apply plg_per_rect1; [apply parallelogram_to_plg, plg_permut; auto|].
  cut (Perp S H H P); [Perp|].
  apply perp_col4 with I H H P; Col; [ColR|].
  cut (Per I H P); [apply per_perp; assert_diffs; auto|].
  apply rect_per2 with Q; auto.
  }
clear HP.
destruct (plg_existence G P T) as [U HP]; [assert_diffs; auto|].
assert (HIS : I <> S).
  {
  intro; treat_equalities; do 3 apply rect_permut in HR9.
  apply degenerated_rect_eq in HR9; treat_equalities; auto.
  }
assert (HPQ : P <> Q).
  {
  intro; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR9; treat_equalities; auto.
  }
assert (HPT : P <> T)
  by (intro; treat_equalities; apply degenerated_rect_eq in HR14; auto).
assert (HR15 : Rectangle G P T U).
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  cut (Perp T P P G); [Perp|].
  apply perp_col4 with Q P P G; Col; [assert_diffs; auto|..].
  - cut (Col P Q T); [Col|cut (Par P Q P T); [apply par_id|]].
    apply par_trans with I S.
    + apply par_col4__par with P Q H I; Col; [|ColR].
      apply Rectangle_Parallelogram, plg_par in HR9; spliter; Par.
    + apply par_col4__par with H S P T; Col; [..|ColR].
      apply Rectangle_Parallelogram, plg_par in HR14; spliter; Par.
  - cut (Per Q P G); [apply per_perp; assert_diffs; auto|].
    apply rect_per1 with J, rect_permut, rect_permut; auto.
  }
clear HP.
destruct (plg_existence M S T) as [V HP]; auto.
assert (HST : S <> T).
  {
  intro; treat_equalities; apply rect_permut in HR14.
  apply degenerated_rect_eq in HR14; auto.
  }
assert (HR16 : Rectangle M S T V).
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  cut (Perp T S S M); [Perp|].
  apply perp_col4 with T S S H; Col.
  cut (Per T S H); [apply per_perp; assert_diffs; auto|].
  apply rect_per2 with P, rect_permut, rect_permut; auto.
  }
clear HP.
assert (HB16 : Bet T P Q).
  {
  apply (Bet_Rect2__Bet T S H P I Q);
    [apply (between_exchange3 M); Between|apply rect_permut, rect_permut; assumption|apply rect_comm2, rect_permut; assumption].
  }
assert (HB17 : Bet T S R).
  {
  apply (Bet_Rect2__Bet T P H S K R);
    [apply (between_exchange3 G); Between|apply rect_comm2, rect_permut; assumption|apply rect_permut, rect_permut, rect_permut; assumption].
  }
assert (HTU : T <> U).
  {
  intro; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR15; treat_equalities.
  apply degenerated_rect_eq in HR10; auto.
  }
assert (HGU : G <> U).
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR15; auto.
  }
assert (HB19 : Bet U T S).
  {
  apply (Bet_Rect2__Bet U G P T H S); [Between|apply rect_permut, rect_permut, rect_permut; assumption|apply rect_comm2, rect_permut; assumption].
  }
assert (HB20 : Bet V T P).
  {
  apply (Bet_Rect2__Bet V M S T H P); [Between|apply rect_permut, rect_permut, rect_permut; assumption|apply rect_permut, rect_permut; assumption].
  }
assert (HR17 : Rectangle N U T V).
  {
  assert (HCol1 : Col N G J) by Col.
  assert (HCol2 : Col V P Q) by ColR.
  assert (HCol3 : Col N M L) by Col.
  assert (HCol4 : Col U S R) by ColR.
  assert (HCol5 : Col L M V).
    {
    cut (Col M L V); [Col|cut (Par M L M V); [apply par_id|]].
    apply par_trans with R S.
    - apply Rectangle_Parallelogram, plg_par in HR12; spliter; Par.
    - apply par_col4__par with S T M V; Col.
      + intro; treat_equalities.
        apply rect_permut, degenerated_rect_eq in HR12; auto.
      + intro; treat_equalities.
        apply rect_permut, rect_permut, degenerated_rect_eq in HR16; auto.
      + apply Rectangle_Parallelogram, plg_par in HR16; spliter; Par.
    }
  assert (HCol6 : Col U G J).
    {
    cut (Col G U J); [Col|cut (Par G U G J); [apply par_id|]].
    apply par_trans with P Q.
    - apply par_col4__par with G U P T; Col.
      apply Rectangle_Parallelogram, plg_par in HR15; spliter; Par.
    - apply Rectangle_Parallelogram, plg_par in HR10; spliter; Par.
    }
  assert (HP1 : Par L M R S)
    by (apply Rectangle_Parallelogram, plg_par in HR12; spliter; Par).
  assert (HP2 : Par P Q G J)
    by (apply Rectangle_Parallelogram, plg_par in HR10; spliter; Par).
  assert (HPer : Per U N V).
    {
    elim (eq_dec_points N U); [intro; treat_equalities; Perp|intro HNU].
    elim (eq_dec_points N V); [intro; treat_equalities; Perp|intro HNV].
    cut (Perp U N N V); [Perp|].
    apply cop_par_perp__perp with P T; Cop.
    - apply par_col4__par with P Q G J; Col.
    - cut (Perp N V P T); [Perp|].
      apply cop_par_perp__perp with S T; Cop.
      + apply par_col4__par with R S L M; Col; Par.
      + cut (Perp P T T S); [Perp|].
        cut (Per P T S); [apply per_perp; assert_diffs; auto|].
        apply rect_per2 with H, rect_permut; auto.
    }
  assert (HNU : N <> U).
    {
    apply (par_not_col_strict _ _ _ _ R) in HP1; Col.
    - intro; treat_equalities; apply (par_not_col L M R S N HP1); Col.
    - cut (~ Col M L R); [Col|apply per_not_col; [assert_diffs; auto..|]].
      apply rect_per2 with S; auto.
    }
  assert (HNV : N <> V).
    {
    apply (par_not_col_strict _ _ _ _ G) in HP2; Col.
    - intro; treat_equalities; apply (par_not_col P Q G J N HP2); Col.
    - cut (~ Col Q P G); [Col|apply per_not_col; [assert_diffs; auto..|]].
      apply rect_per1 with J, rect_permut, rect_permut; auto.
    }
  assert (HTV : T <> V).
    {
    apply (par_not_col_strict _ _ _ _ R) in HP1; Col.
    - intro; treat_equalities; apply (par_not_col L M R S T HP1); Col.
    - cut (~ Col M L R); [Col|apply per_not_col; [assert_diffs; auto..|]].
      apply rect_per2 with S; auto.
    }
  apply plg_per_rect1; [apply parallelogram_to_plg|Perp].
  apply plg_permut, par_2_plg.
  - apply per_not_col; Perp.
  - apply par_col4__par with L M R S; Col.
  - apply par_col4__par with P Q G J; Col.
  }
assert (HB21 : Bet N U G).
  {
  apply (Bet_Rect2__Bet N V T U P G); [Between|apply rect_permut, rect_comm2; assumption|apply rect_permut, rect_permut, rect_comm2; assumption].
  }
assert (HB22 : Bet N V M).
  {
  apply (Bet_Rect2__Bet N U T V S M); [Between|assumption|apply rect_permut, rect_permut, rect_comm2; assumption].
  }
exists Q, S, T, U, V; repeat (split; [assumption|]); assumption.
Qed.

Lemma B5_7 A B C D E F a b c d e f :
  Bet B C E -> B <> C -> Bet b c e -> b <> c ->
  EqR D C E F d c e f -> EqR A B E F a b e f ->
  EqR A B C D a b c d.
Proof.
intros HB1 HBC HB2 Hbc HE1 HE2.
assert (HD : D <> C /\ C <> E /\ d <> c /\ c <> e)
  by (apply EqR_diffs with F f; auto).
destruct HD as [HDC [HCE [Hdc Hce]]].
assert (HD : A <> B /\ B <> E /\ a <> b /\ b <> e)
  by (apply EqR_diffs with F f; auto).
destruct HD as [HAB [HBE [Hab Hbe]]].
assert (HR1 : Rectangle D C E F) by (destruct HE1 as [_ [_ [H _]]]; auto).
assert (HR2 : Rectangle A B E F) by (destruct HE2 as [_ [_ [H _]]]; auto).
assert (HR3 : Rectangle d c e f)
  by (destruct HE1 as [_ [_ [_ [_ [_ [H _]]]]]]; auto).
assert (HR4 : Rectangle a b e f)
  by (destruct HE2 as [_ [_ [_ [_ [_ [H _]]]]]]; auto).
destruct (rect_cut__rect A B C D E F) as [HDF [HEF [HAF [HB3 HR5]]]]; [assumption..|].
destruct (rect_cut__rect a b c d e f) as [Hdf [Hef [Haf [HB4 HR6]]]]; [assumption..|].
assert (HR : EqR B E F A a b e f).
  {
  apply EqR_trans with A B E F; [apply EqR_sym|auto].
  assert (HE := EqR_perm A B E F HAB HBE HR2); spliter; auto.
  }
destruct HR as [_ [_ [_ [_ [_ [_ HR]]]]]]; assert (HR' := HR).
destruct HR as [G [H [K [L [M [N [O [J [I HR]]]]]]]]].
destruct HR as [HR7 [HC1 [HC2 [HR8 [HC3 [HC4 HR]]]]]].
destruct HR as [HB5 [HB6 [HB7 [HB8 [HB9 [HB10 HB11]]]]]].
destruct (le_bet G H B C) as [P [HB12 HC5]];
[apply l5_6 with B C B E; Cong; apply bet__le1213; Between|].
assert (HHP : H <> P)
  by (intro; treat_equalities; apply HCE, between_cong with B; [Between|CongR]).
destruct (le_bet L K b c) as [R [HB14 HC6]];
[apply l5_6 with b c b e; Cong; apply bet__le1213; Between|].
assert (HKR : K <> R)
  by (intro; treat_equalities; apply Hce, between_cong with b; [Between|CongR]).
destruct (placed_rects_cut__figure G H I J K L M N O P R)
  as [Q [S [T [U [V [HR9 [HR10 [HB13 [HR11 [HR12 [HB15 [HR13 [HR14 [HR15
     [HR16 [HR17 [HB16 [HB17 [HB19 [HB20 [HB21 [HB22 HD]]]]]]]]]]]]]]]]]]]]]];
  auto; try solve [assert_diffs; auto].
destruct HD as [HPT [HST [HMS [HHS [HKO [HTU HGU]]]]]].
assert (HE3 : EqR D C E F H I Q P).
  {
  apply B5_5; auto; [apply rect_comm2; auto|..].
  - cut (Cong A B C D /\ Cong A B E F /\ Cong H I P Q);
    [intro; spliter; CongR|split; [|split]].
    + apply Rectangle_Parallelogram, plg_cong in HR5; spliter; Cong.
    + apply Rectangle_Parallelogram, plg_cong in HR2; spliter; Cong.
    + apply Rectangle_Parallelogram, plg_cong in HR9; spliter; Cong.
  - cut (Cong I Q P H /\ Cong C E P H); [intros []; CongR|split].
    + apply Rectangle_Parallelogram, plg_cong in HR9; spliter; Cong.
    + apply l4_3_1 with B G; Cong.
  }
assert (HE4 : EqR d c e f H K R S).
  {
  apply B5_5; Cong; [cut (Cong a b c d); [intro; CongR|]|].
  - apply Rectangle_Parallelogram, plg_cong in HR6; spliter; Cong.
  - cut (Cong c e R K); [Cong|apply l4_3_1 with b L; Cong].
  }
assert (HB18 : Bet T H O).
  {
  apply (EqR_placed__bet P H I Q K R S); Between.
  - assert (HPH : P <> H) by (assert_diffs; auto).
    assert (HHI : H <> I) by (assert_diffs; auto).
    assert (HR : Rectangle P H I Q)
      by (do 3 apply rect_permut; apply rect_comm2; auto).
    apply EqR_trans with H I Q P;
    [destruct (EqR_perm P H I Q HPH HHI HR); spliter; auto|].
    apply EqR_trans with D C E F; [apply EqR_sym; auto|].
    apply EqR_trans with d c e f; auto.
  - apply (between_exchange3 L); Between.
  - cut (Bet Q I O); [Between|apply (between_exchange3 J); Between].
  - apply (between_exchange3 G); Between.
  - apply (between_exchange3 M); Between.
  }
assert (HB23 : Bet N T H).
  {
  assert (HTNH : Col T N H).
    {
    assert (HHK : H <> K) by (assert_diffs; auto).
    cut (H <> O); [intro; ColR|].
    apply per_distinct with K; auto.
    apply rect_per2 with I, rect_permut; auto.
    }
  apply col_two_sides_bet with G; Col.
  assert (HNC1 : ~ Col G P T).
    {
    apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with U; auto.
    }
  assert (HNC2 : ~ Col T U G).
    {
    apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with P; do 2 apply rect_permut; auto.
    }
  apply l9_8_2 with U; [apply l9_2, l9_8_2 with P|].
  - destruct (plg_mid G P T U) as [W [HM1 HM2]];
    [apply Rectangle_Parallelogram; auto|].
    split; Col; split; Col; exists W; split; [Col|Between].
  - apply out_one_side_1 with G; Col.
    split; [|split]; [assert_diffs; auto..|Between].
  - apply out_one_side_1 with G; Col.
    split; [|split]; [assert_diffs; auto..|Between].
  }
assert (HE9 : EqR G P T U M S T V).
  {
  assert (HGP : G <> P) by (assert_diffs; auto).
  apply EqR_trans with U T P G; [|apply EqR_trans with T S M V].
  - destruct (EqR_perm G P T U HGP HPT HR15); spliter; auto.
  - split; [assert_diffs; auto|].
    split; [assert_diffs; auto|].
    split; [do 2 apply rect_permut; apply rect_comm2; auto|].
    do 2 (split; [auto|]).
    split; [apply rect_permut, rect_comm2, rect_permut, rect_permut; auto|].
    exists U, T, S, M, V, N, H, G, P.
    split; [apply rect_comm2, rect_permut, rect_permut; auto|].
    do 2 (split; Cong).
    split; [apply rect_permut, rect_comm2, rect_permut, rect_permut; auto|].
    do 8 (split; Cong; Between).
  - destruct (EqR_perm T S M V); spliter; auto.
    apply rect_permut, rect_comm2, rect_permut, rect_permut; auto.
  }
assert (HCs : Cong G P B C /\ Cong M S b c /\ Cong P T c e /\ Cong S T C E).
  {
  split; [Cong|split; [|split]].
  - cut (Cong M S L R); [intro; CongR|].
    apply Rectangle_Parallelogram, plg_cong in HR12; spliter; Cong.
  - cut (Cong P T H S /\ Cong H S K R /\ Cong R K c e); [intros [?[]]; CongR|].
    split; [|split].
    + apply Rectangle_Parallelogram, plg_cong in HR14; spliter; Cong.
    + apply Rectangle_Parallelogram, plg_cong in HR11; spliter; Cong.
    + apply l4_3_1 with L b; Between; Cong.
  - cut (Cong H P S T /\ Cong P H C E); [intros []; CongR|split].
    + apply Rectangle_Parallelogram, plg_cong in HR14; spliter; Cong.
    + apply l4_3_1 with G B; Between; Cong.
  }
keep HB1 HBC HB2 Hbc HE1 HE2 HDC HCE Hdc Hce HAB HBE Hab Hbe HR1 HR2 HR3 HR4
     HDF HEF HAF Hdf Hef Haf HB3 HB4 HR5 HR6 HR15 HR16 HE9 HCs HR'.
revert G M P S T U V HR15 HR16 HE9 HCs HR'.
intros G M P S T U V HR7 HR8 HE3 [HC1 [HC2 [HC3 HC4]]] HR.
destruct HR as [G' [H' [K' [L' [M' [N' [O' [J' [I' HR]]]]]]]]].
destruct HR as [HR9 [HC5 [HC6 [HR10 [HC7 [HC8 HR]]]]]].
destruct HR as [HB5 [HB6 [HB7 [HB8 [HB9 [HB10 HB11]]]]]].
destruct (le_bet G' H' C E) as [P' [HB12 HC9]];
[apply l5_6 with C E B E; Cong; apply bet__le2313; Between|].
assert (HH'P' : H' <> P').
  {
  intro; treat_equalities; apply HBC; cut (C = B); [auto|].
  apply between_cong with E; [Between|CongR].
  }
destruct (le_bet L' K' c e) as [R' [HB14 HC10]];
[apply l5_6 with c e b e; Cong; apply bet__le2313; Between|].
assert (HK'R' : K' <> R').
  {
  intro; treat_equalities; apply Hbc; cut (c = b); [auto|].
  apply between_cong with e; [Between|CongR].
  }
destruct (placed_rects_cut__figure G' H' I' J' K' L' M' N' O' P' R')
  as [Q' [S' [T' [U' [V' [HR11 [HR12 [HB13 [HR13 [HR14 [HB15 [_ [HR15 [HR16
     [HR17 [HR18 [HB16 [HB17 [HB20 [HB21 [HB22 [HB23 HD]]]]]]]]]]]]]]]]]]]]]];
  auto; try solve [assert_diffs; auto].
destruct HD as [HP'T' [HST [HM'S' [HH'S' [_ [HT'U' HG'U']]]]]].
assert (HE4 : EqR A B C D P' H' I' Q').
  {
  apply EqR_trans with  I' H' P' Q'; [apply B5_5; auto|].
  - cut (Cong I' H' P' Q' /\ Cong A B E F); [intros []; CongR|split].
    + apply Rectangle_Parallelogram, plg_cong in HR11; spliter; Cong.
    + apply Rectangle_Parallelogram, plg_cong in HR2; spliter; Cong.
  - cut (Cong C B P' H'); [Cong|].
    apply l4_3_1 with E G'; Between; Cong.
  - destruct (EqR_perm I' H' P' Q'); spliter; assert_diffs; auto.
  }
assert (HE5 : EqR a b c d H' K' R' S').
  {
  apply B5_5; auto.
  cut (Cong c b R' K'); [Cong|].
  apply l4_3_1 with e L'; Between; Cong.
  }
apply EqR_trans with P' H' I' Q'; [auto|clear HE4].
apply EqR_trans with H' K' R' S'; [clear HE5|apply EqR_sym; auto].
split; [auto|]; split; [assert_diffs; auto|].
split; [apply rect_permut, rect_comm2, rect_permut, rect_permut; auto|].
split; [|split; [|split]]; [assert_diffs; auto..|].
exists P', H', K', R', S', T', O', Q', I'.
split; [apply rect_permut, rect_comm2, rect_permut, rect_permut; auto|].
split; [|split; [|split; [|split; [|split]]]]; Cong; split; [|split]; Between.
split; [apply (between_exchange3 L'); Between|].
split; [apply between_symmetry, (between_exchange3 J'); Between|].
split; [apply (between_exchange3 G'); Between|].
split; [apply (between_exchange3 M'); Between|].
apply between_exchange3 with N'; [|Between].
apply (EqR_placed__bet U' T' P' G' S' M' V'); Between.
apply EqR_trans with M S T V; [|apply EqR_trans with G P T U].
- apply EqR_trans with S T V M.
  + apply B5_5; auto; [apply rect_comm2, rect_permut, rect_permut; auto|..].
    * apply rect_permut; auto.
    * cut (Cong G' P' T' U'); [intro; CongR|].
      apply Rectangle_Parallelogram, plg_cong in HR16; spliter; Cong.
    * cut (Cong P' T' H' S' /\ Cong H' S' K' R' /\
           Cong T  V  M  S  /\ Cong R' K' c  b); [intros [? [? []]]; CongR|].
      split; [|split; [|split]].
      -- apply Rectangle_Parallelogram, plg_cong in HR15; spliter; Cong.
      -- apply Rectangle_Parallelogram, plg_cong in HR13; spliter; Cong.
      -- apply Rectangle_Parallelogram, plg_cong in HR8; spliter; Cong.
      -- apply l4_3_1 with L' e; Between; Cong.
  + destruct (EqR_perm S T V M); spliter; auto; [assert_diffs; auto|..].
    * intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR8; treat_equalities; auto.
    * apply rect_permut; auto.
- apply EqR_sym; auto.
- apply B5_5; auto; [assert_diffs; auto..| | |].
  + apply rect_permut, rect_comm2, rect_permut, rect_permut; auto.
  + cut (Cong S' T' H' P' /\ Cong P' H' C B); [intros []; CongR|split].
    * apply Rectangle_Parallelogram, plg_cong in HR15; spliter; Cong.
    * apply l4_3_1 with G' E; Between; Cong.
  + cut (Cong L' R' M' S'); [intro; CongR|].
    apply Rectangle_Parallelogram, plg_cong in HR14; spliter; Cong.
Qed.

Lemma extent_rect A B C D E F :
  Bet B C E ->
  Rectangle A B C D -> Rectangle D C E F ->
  Rectangle A B E F.
Proof.
intros HB1 HR1 HR2.
assert (HBCP : B = C -> Rectangle A B E F).
  {
  apply Rectangle_Parallelogram, plg_cong in HR1.
  intro; spliter; treat_equalities; assumption.
  }
elim (eq_dec_points B C); [apply HBCP|clear HBCP; intro HBC].
assert (HCEP : C = E -> Rectangle A B E F).
  {
  apply Rectangle_Parallelogram, plg_cong in HR2.
  intro; spliter; treat_equalities; assumption.
  }
elim (eq_dec_points C E); [apply HCEP|clear HCEP; intro HCE].
assert (HB2 : Bet A D F) by (apply Bet_Rect2__Bet with B C E; assumption).
assert (HPer : Per A B C) by (apply rect_per2 with D; auto).
elim (eq_dec_points A B); [intro|intro HAB].
- apply Rectangle_Parallelogram, plg_cong in HR1.
  apply Rectangle_Parallelogram, plg_cong in HR2; spliter; treat_equalities.
  apply Rectangle_triv; assert_diffs; auto.
- assert (HCD : C <> D).
  {
  apply Rectangle_Parallelogram, plg_cong in HR1.
  intro; spliter; treat_equalities; auto.
  }
  apply plg_per_rect2; [apply pars_par_plg|apply l8_3 with C; Col; Perp].
  + apply par_not_col_strict with E; [|Col|].
    * apply Rectangle_Parallelogram, plg_par in HR1; auto.
      apply Rectangle_Parallelogram, plg_par in HR2; auto.
      spliter; apply par_trans with C D; Par.
    * apply per_not_col in HPer; auto; intro; apply HPer; ColR.
  + apply par_col4__par with A D B C; Col; [intro|assert_diffs; auto|].
    * apply Rectangle_Parallelogram, plg_cong in HR1.
      apply Rectangle_Parallelogram, plg_cong in HR2.
      spliter; treat_equalities; auto.
    * apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
Qed.

Lemma B5_8 A B C D E F a b c d e f :
  Bet B C E -> Bet b c e ->
  EqR A B C D a b c d -> EqR D C E F d c e f ->
  EqR A B E F a b e f.
Proof.
intros HB1 HB2 HE1 HE2.
assert (HB3 : Bet A D F).
  {
  destruct HE1 as [_ [_ [HR1 _]]]; destruct HE2 as [_ [_ [HR2 _]]].
  apply Bet_Rect2__Bet with B C E; Between.
  }
assert (HE3 : EqR B C D A a b c d).
  {
  apply EqR_trans with A B C D; [apply EqR_sym|auto].
  destruct HE1 as [HAB [HBC [HR _]]].
  destruct (EqR_perm A B C D); spliter; auto.
  }
assert (HE4 : EqR C E F D d c e f).
  {
  apply EqR_trans with D C E F; [apply EqR_sym|auto].
  destruct HE2 as [HCD [HCE [HR _]]].
  destruct (EqR_perm D C E F); spliter; auto.
  }
destruct HE3 as [HBC [HCD [HR1 [Hab [Hbc [HR2 HE3]]]]]].
destruct HE4 as [HCE [HEF [HR3 [Hcd [Hce [HR4 HE4]]]]]].
destruct HE3 as [G' [H' [K' [L' [M' [N' [O' [J' [I' HE3]]]]]]]]].
destruct HE3 as [HR5 [HC1 [HC2 [HR6 [HC3 [HC4 HE3]]]]]].
destruct HE3 as [HB5 [HB6 [HB7 [HB8 [HB9 [HB10 HB11]]]]]].
destruct HE4 as [P [H [K [R [S [T [O [Q [I HE4]]]]]]]]].
destruct HE4 as [HR7 [HC5 [HC6 [HR8 [HC7 [HC8 HE4]]]]]].
destruct HE4 as [HB12 [HB13 [HB14 [HB15 [HB16 [HB17 HB18]]]]]].
assert (HDF : D <> F).
  {
  intro; treat_equalities; apply rect_permut in HR3.
  apply degenerated_rect_eq in HR3; auto.
  }
assert (HAF : A <> F) by (assert_diffs; auto).
assert (HD : G' <> H' /\ H' <> I' /\ H' <> K' /\ K' <> L')
  by (assert_diffs; repeat split; auto).
destruct HD as [HG'H' [HH'I' [HH'K' HK'L']]].
destruct (placed_rects__corner_rect G' H' I' J' K' L' M' O')
  as [HH'O' [HI'O' [_ HR9]]]; auto.
assert (HI'J' : I' <> J').
  {
  intro; treat_equalities; apply rect_permut in HR5.
  apply degenerated_rect_eq in HR5; treat_equalities; auto.
  }
assert (HCA1 : CongA G' N' H' I' H' O')
  by (apply (placed_rects_diag__conga G' H' I' J' K' L' M' N' O'); auto).
assert (HD : P <> H /\ H <> I /\ H <> K /\ K <> R)
  by (assert_diffs; repeat split; auto).
destruct HD as [HPH [HHI [HHK HKR]]].
destruct (placed_rects__corner_rect P H I Q K R S O)
  as [HHO [HIO [_ HR10]]]; auto.
assert (HIQ : I <> Q).
  {
  intro; treat_equalities; apply rect_permut in HR7.
  apply degenerated_rect_eq in HR7; treat_equalities; auto.
  }
assert (HHT : H <> T).
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram P H I Q HR7).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs_pars_2, (par_not_col _ _ _ _ H) in HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with Q; auto.
  }
assert (HCA2 : CongA P T H I H O)
  by (apply (placed_rects_diag__conga P H I Q K R S T O); auto).
assert (HCA3: CongA I' H' O' I H O).
  {
  keep HB1 HE1 HB3 HBC HCD HR1 Hab Hbc HR2 HR5 HC1 HC2 HC3 HB8 HB9 HCE HEF HR3 Hcd HR7 HC5 HC6 HC7 HB15 HB16 HDF HAF HH'O' HI'O' HI'J' HR9 HIO HIQ HR10.
  destruct (l11_49 H' I' O' H I O) as [_ HCA]; [..|destruct (HCA HH'O'); CongA].
  - apply l11_16; auto.
    * apply l8_2, l8_3 with J'; Col.
      apply rect_per1 with G'; do 2 apply rect_permut; auto.
    * intro; treat_equalities.
      apply degenerated_rect_eq in HR5; treat_equalities; auto.
    * apply l8_2, l8_3 with Q; Col.
      apply rect_per1 with P; do 2 apply rect_permut; auto.
    * intro; treat_equalities.
      apply degenerated_rect_eq in HR7; treat_equalities; auto.
  - apply Rectangle_Parallelogram, plg_cong in HR1.
    apply Rectangle_Parallelogram, plg_cong in HR3; spliter; CongR.
  - keep Hab Hbc HR2 HC3 Hcd HC7 HH'O' HI'O' HR9 HIO HR10. apply Rectangle_Parallelogram, plg_cong in HR2.
    apply Rectangle_Parallelogram, plg_cong in HR9.
    apply Rectangle_Parallelogram, plg_cong in HR10; spliter; CongR.
  }
assert (HCA4 : CongA G' N' H' P T H).
  {
  apply conga_trans with I' H' O'; [auto|].
  apply conga_trans with I H O; [|apply conga_sym]; auto.
  }
destruct (placed_rects__corner_rect K H S R P Q I T) as [_ [_ [_ HR11]]];
  try solve [intro; subst; auto|Between|apply rect_comm2; assumption
            |intro; treat_equalities; apply rect_permut, rect_permut, degenerated_rect_eq in HR8;
             treat_equalities; auto
            |intro; treat_equalities; apply rect_permut, rect_permut, degenerated_rect_eq in HR7;
             treat_equalities; auto].
apply rect_permut in HR11.
destruct (segment_construction I Q B C) as [J [HB19 HC9]].
destruct (segment_construction H P B C) as [G [HB20 HC10]].
assert (HR12 : Rectangle J G P Q)
  by (apply rect_extend__rect with H I; Between; [CongR|assert_diffs; auto..]).
destruct (segment_construction K R b c) as [L [HB21 HC11]].
destruct (segment_construction H S b c) as [M [HB22 HC12]].
assert (HR13 : Rectangle M L R S).
  {
  apply rect_extend__rect with K H; Between; [CongR|assert_diffs; auto..|].
  apply rect_permut, rect_comm2, rect_permut, rect_permut; auto.
  }
destruct (segment_construction J G P T) as [U [HB23 HC13]].
assert (HR14 : Rectangle G P T U).
  {
  do 2 apply rect_permut.
  apply rect_extend__rect with J Q; Between; [CongR|..|apply rect_comm2; auto].
  - intro; treat_equalities; do 3 apply rect_permut in HR12.
    apply degenerated_rect_eq in HR12; treat_equalities.
    apply rect_permut, rect_permut, degenerated_rect_eq in HR7.
    treat_equalities; auto.
  - assert_diffs; auto.
  }
destruct (segment_construction L M S T) as [V [HB24 HC14]].
assert (HR15 : Rectangle M S T V).
  {
  do 2 apply rect_permut.
  apply rect_extend__rect with L R; Between; [CongR| |assert_diffs; auto].
  intro; treat_equalities; do 3 apply rect_permut in HR13.
  apply degenerated_rect_eq in HR13; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR8.
  treat_equalities; auto.
  }
assert (HTU : T <> U).
  {
  intro; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR14; treat_equalities; auto.
  }
destruct (plg_existence U T V) as [N HP]; [auto|].
assert (HPTV : Col P T V).
  {
  cut (Col T P V); [Col|apply par_id, par_trans with H S].
  - apply Rectangle_Parallelogram, plg_par in HR11; spliter; Par.
    apply Rectangle_Parallelogram, plg_cong in HR8.
    intro; apply plg_cong in HR11; spliter; treat_equalities; auto.
  - cut (Par S H T V); [Par|].
    apply par_col_par_2 with M; [|Col|].
    + apply Rectangle_Parallelogram, plg_cong in HR8.
      intro; spliter; treat_equalities; auto.
    + apply Rectangle_Parallelogram, plg_par in HR15; spliter; Par.
      * intro; treat_equalities; auto.
      * apply Rectangle_Parallelogram, plg_cong in HR11.
        intro; spliter; treat_equalities; auto.
  }
assert (HPT : P <> T).
  {
  apply Rectangle_Parallelogram, plg_cong in HR8.
  apply Rectangle_Parallelogram, plg_cong in HR11.
  intro; spliter; treat_equalities; auto.
  }
assert (HR16 : Rectangle N U T V).
  {
  apply plg_per_rect2; [apply parallelogram_to_plg|apply l8_2, l8_3 with G].
  - do 3 apply plg_permut; auto.
  - apply rect_per4 with P; auto.
  - apply Rectangle_Parallelogram, plg_cong in HR8.
    apply Rectangle_Parallelogram, plg_cong in HR11.
    apply plg_cong in HP; spliter; intro; treat_equalities; auto.
  - apply par_id, par_trans with P T.
    + apply Rectangle_Parallelogram, plg_par in HR14; spliter; Par;
      intro; treat_equalities; auto.
    + cut (Par T P U N); [Par|].
      apply par_col_par_2 with V; [auto|Col|].
      apply plg_par in HP; spliter; Par.
      apply Rectangle_Parallelogram, plg_cong in HR13.
      apply Rectangle_Parallelogram, plg_cong in HR15.
      intro; spliter; treat_equalities; auto.
  }
clear HP.
assert (HR17 : Rectangle A B E F)
  by (apply extent_rect with C D; Between; do 3 apply rect_permut; auto).
assert (HR18 : Rectangle a b e f) by (apply extent_rect with c d; Between).
assert (HR19 : Rectangle G H I J).
  {
  apply rect_permut, extent_rect with P Q; Between.
  do 3 apply rect_permut; auto.
  }
assert (HR20 : Rectangle H K L M).
  {
  apply extent_rect with R S; Between.
  apply rect_comm2, rect_permut, rect_permut; auto.
  }
assert (HAB : A <> B).
  {
  apply Rectangle_Parallelogram, plg_cong in HR1.
  intro; spliter; treat_equalities; auto.
  }
assert (HBE : B <> E).
  {
  apply Rectangle_Parallelogram, plg_cong in HR17.
  intro; spliter; treat_equalities; auto.
  }
apply EqR_trans with B E F A;
[destruct (EqR_perm A B E F HAB HBE HR17); spliter; auto|].
assert (Hbe : b <> e).
  {
  apply Rectangle_Parallelogram, plg_cong in HR18.
  intro; spliter; treat_equalities; auto.
  }
assert (HC15 : Cong B E G H) by (apply l2_11 with C P; Between; Cong).
assert (HC16 : Cong a b H K)
  by (apply Rectangle_Parallelogram, plg_cong in HR2; spliter; CongR).
assert (HC17 : Cong b e K L)
  by (cut (Cong b e L K); [Cong|apply l2_11 with c R; Between; Cong]).
assert (HB25 : Bet N U G).
  {
  apply Bet_Rect2__Bet with V T P; [apply Bet_Rect2__Bet with M S H|..].
  - Between.
  - apply rect_permut, rect_permut, rect_permut; auto.
  - apply rect_permut, rect_permut; auto.
  - apply rect_permut, rect_comm2; auto.
  - apply rect_comm2, rect_permut, rect_permut; auto.
  }
assert (HB26 : Bet N V M).
  {
  apply Bet_Rect2__Bet with U T S; [apply Bet_Rect2__Bet with G P H|..].
  - Between.
  - apply rect_permut, rect_permut, rect_permut; auto.
  - apply rect_permut, rect_comm2, rect_permut, rect_permut; auto.
  - auto.
  - apply rect_permut, rect_comm2; do 3 apply rect_permut; auto.
  }
assert (HGU : G <> U).
  {
  apply Rectangle_Parallelogram, plg_cong in HR8.
  apply Rectangle_Parallelogram, plg_cong in HR11.
  apply Rectangle_Parallelogram, plg_cong in HR14.
  intro; spliter; treat_equalities; auto.
  }
assert (HMV : M <> V).
  {
  apply Rectangle_Parallelogram, plg_cong in HR11.
  apply Rectangle_Parallelogram, plg_cong in HR15.
  intro; spliter; treat_equalities; auto.
  }
assert (HHS : H <> S).
  {
  apply Rectangle_Parallelogram, plg_cong in HR8.
  intro; spliter; treat_equalities; auto.
  }
apply rect_permut in HR17.
do 6 (split; [Cong|]); exists G, H, K, L, M, N, O, J, I; do 6 (split; [Cong|]).
split; [apply outer_transitivity_between2 with U; Between|].
split; [apply outer_transitivity_between2 with V; Between|].
split; [apply outer_transitivity_between2 with R; Between|].
split; [apply between_symmetry, outer_transitivity_between2 with Q; Between|].
split; [apply outer_transitivity_between2 with P; Between|].
split; [apply outer_transitivity_between2 with S; Between|].
apply outer_transitivity_between2 with T; Between.
assert (HNC : ~ Col N T V).
  {
  cut (~ Col N V T); [Col|apply per_not_col].
  - apply Rectangle_Parallelogram, plg_cong in HR12.
    apply Rectangle_Parallelogram, plg_cong in HR14.
    apply Rectangle_Parallelogram, plg_cong in HR16.
    intro; spliter; treat_equalities; auto.
  - apply Rectangle_Parallelogram, plg_cong in HR13.
    apply Rectangle_Parallelogram, plg_cong in HR15.
    intro; spliter; treat_equalities; auto.
  - apply rect_per4 with U; auto.
  }
apply CongA_OS_ParTS__Bet with U P.
- apply conga_trans with G' N' H'; [|CongA].
  assert (HNT : N <> T) by (intro; treat_equalities; Col).
  assert (HParS : Par_strict H' K' L' M').
    {
    apply par_not_col_strict with L'; [|Col|].
    - apply Rectangle_Parallelogram, plg_par in HR6; spliter; Par;
      intro; treat_equalities; auto.
    - apply per_not_col; [intro; treat_equalities; auto..|].
      apply rect_per1 with M', rect_comm2; auto.
    }
  destruct (l11_49 N U T N' G' H') as [_ HCA]; [..|destruct (HCA HNT); CongA].
  + apply l11_16; auto.
    * apply rect_per1 with V, rect_comm2; auto.
    * apply Rectangle_Parallelogram, plg_cong in HR13.
      apply Rectangle_Parallelogram, plg_cong in HR15.
      apply Rectangle_Parallelogram, plg_cong in HR16.
      intro; spliter; treat_equalities; auto.
    * apply l8_3 with J'; [..|Col].
      -- apply rect_per2 with I'; do 3 apply rect_permut; auto.
      -- apply Rectangle_Parallelogram, plg_cong in HR5.
         intro; spliter; treat_equalities; auto.
    * intro; treat_equalities; apply (par_not_col _ _ _ _ N' HParS); Col.
  + cut (Cong G' N' K' L'); [intro|].
    * apply Rectangle_Parallelogram, plg_cong in HR13.
      apply Rectangle_Parallelogram, plg_cong in HR15.
      apply Rectangle_Parallelogram, plg_cong in HR16; spliter; CongR.
    * destruct (plg_cong G' K' L' N'); [apply par_2_plg|Cong].
      -- cut (~ Col L' G' K'); [Col|].
         apply par_not_col with L' M'; Col.
         apply par_strict_col4__par_strict with L' M' H' K'; Col; Par;
         intro; treat_equalities; auto.
         assert_diffs; auto.
      -- apply par_col4__par with H' K' L' M'; Col; [assert_diffs; auto..|].
         apply Rectangle_Parallelogram, plg_par in HR6; spliter; Par;
         intro; treat_equalities; auto.
      -- apply par_trans with H' M'.
         ++ apply par_col4__par with G' J' H' I'; Col; [assert_diffs; auto..|].
            apply Rectangle_Parallelogram, plg_par in HR5; spliter; Par;
            intro; treat_equalities; auto.
         ++ apply Rectangle_Parallelogram, plg_par in HR6; spliter; Par;
            intro; treat_equalities; auto.
  + apply Rectangle_Parallelogram, plg_cong in HR14; spliter; CongR.
- apply l9_8_1 with V.
  + assert (HPara : Parallelogram_strict N U T V)
      by (apply ncol134_plg__plgs; [|apply Rectangle_Parallelogram]; Col).
    split; [apply parallelogram_strict_not_col in HPara; Col|].
    split; [intro; apply HNC; ColR|apply plgs_mid in HPara].
    destruct HPara as [MUV []]; exists MUV; split; [Col|Between].
  + split; [intro; apply HNC; ColR|].
    split; [Col|exists T; split; [Col|]].
    apply col_two_sides_bet with S; [Col|].
    assert (HMST : ~ Col M S T).
      {
      apply per_not_col; [intro; treat_equalities; auto..|].
      apply rect_per2 with V; auto.
      }
    assert (HHST : ~ Col H S T).
      {
      apply per_not_col; [intro; treat_equalities; auto..|].
      apply rect_per4 with P; auto.
      }
    apply l9_8_2 with H; [apply l9_2, l9_8_2 with M|].
    * split; [Col|split; [Col|exists S; split; [Col|Between]]].
    * apply l12_6, par_not_col_strict with M; [|Col..].
      apply Rectangle_Parallelogram, plg_par in HR15; spliter; Par;
      intro; treat_equalities; auto.
    * apply l12_6, par_not_col_strict with H; [|Col..].
      apply Rectangle_Parallelogram, plg_par in HR11; spliter; Par;
      intro; treat_equalities; auto.
- cut (Par U N T P); [Par|apply par_col_par_2 with G; [|Col|]].
  + apply Rectangle_Parallelogram, plg_cong in HR13.
    apply Rectangle_Parallelogram, plg_cong in HR15.
    apply Rectangle_Parallelogram, plg_cong in HR16.
    intro; spliter; treat_equalities; auto.
  + apply Rectangle_Parallelogram, plg_par in HR14; spliter; Par.
    intro; treat_equalities; auto.
- apply l9_8_2 with G.
  + split; [intro; apply HNC; ColR|].
    split; [intro; apply HNC; ColR|].
    exists P; split; [Col|Between].
  + apply l12_6, par_not_col_strict with N; [|Col|intro; apply HNC; ColR].
    cut (Par G N P T); [Par|].
    apply par_col_par_2 with U; [intro; treat_equalities; auto|Col|].
    apply Rectangle_Parallelogram, plg_par in HR14; spliter; Par.
    intro; treat_equalities; auto.
Qed.

Definition First_circumscribed_rectangle A B C D K :=
  Rectangle A B D K /\ Col C D K.

Lemma FCR_ABCDK_BACKD A B C D K :
  First_circumscribed_rectangle A B C D K ->
  First_circumscribed_rectangle B A C K D.
Proof. intros [HR HC]; split; [apply rect_comm2|Col]; assumption. Qed.

Lemma FCR_triv A B C : A <> B -> Col A B C -> First_circumscribed_rectangle A B C B A.
Proof. intros; split; [apply rect_permut, Rectangle_triv|]; Col. Qed.

Lemma FCR_ncol__diffs A B C D K :
  ~ Col A B C -> First_circumscribed_rectangle A B C D K ->
  B <> D /\ D <> K /\ K <> A.
Proof.
intros HNC [HR HC]; assert_diffs.
split; [|split]; intro; treat_equalities.
- assert (A = K) by (apply degenerated_rect_eq with B; auto).
  treat_equalities; Col.
- apply rect_permut, degenerated_rect_eq in HR; auto.
- do 2 apply rect_permut in HR; apply degenerated_rect_eq in HR.
  treat_equalities; Col.
Qed.

Lemma FCR_ncol__ncol A B C D K :
  ~ Col A B C -> First_circumscribed_rectangle A B C D K ->
  ~ Col A B D /\ ~ Col A B K.
Proof.
intros HNC HF; destruct (FCR_ncol__diffs A B C D K) as [HBD [HDK HKA]]; auto.
destruct HF as [HR HC].
assert (HPar : Par A B D K)
  by (apply Rectangle_Parallelogram, plg_par in HR; spliter; auto; assert_diffs; auto).
split; intro HCol; apply HNC.
- destruct (not_strict_par A B D K D) as [_ HCol']; Col; ColR.
- destruct (not_strict_par A B D K K) as [HCol' _]; Col; ColR.
Qed.

Lemma FCR_Col__eq A B P C D :
  First_circumscribed_rectangle A B P C D -> Col A B P -> A <> B ->
  A = D /\ B = C.
Proof.
intros [HR HC1] HC2 HAB.
destruct (eq_dec_points B C) as [|HNE].
- split; [treat_equalities|auto].
  apply degenerated_rect_eq in HR; auto.
- destruct (plgf_rect_id A B C D); [|assumption|tauto..].
  apply plg_col_plgf; [|apply Rectangle_Parallelogram; assumption].
  apply not_strict_par1 with D P; [|Col..].
  apply plg_par_1; [..|apply Rectangle_Parallelogram]; auto.
Qed.

Lemma FCR_Col__eq' A B P C D :
  First_circumscribed_rectangle A B P C D -> Col A B P -> C <> D ->
  A = D /\ B = C.
Proof.
intros HF HC HCD; destruct (eq_dec_points A B) as [|HAB]; [|apply (FCR_Col__eq A B P); auto].
treat_equalities; destruct HF as [HR _]; exfalso.
do 3 apply rect_permut in HR; apply degenerated_rect_eq in HR; auto.
Qed.

Lemma FCR_ncol__cop A B C D K :
  ~ Col A B C -> First_circumscribed_rectangle A B C D K ->
  Coplanar A B C D /\ Coplanar A B C K.
Proof.
intros HNC HF; destruct (FCR_ncol__diffs A B C D K) as [HBD [HDK HKA]]; auto.
destruct HF as [HR HC]; assert_diffs.
assert (HPar : Par A B D K)
  by (apply Rectangle_Parallelogram, plg_par in HR; spliter; auto).
split.
- elim (eq_dec_points C D); [intro; treat_equalities; Cop|intro HCD].
  cut (Par A B C D); [Cop|apply par_col4__par with A B D K; Col].
- elim (eq_dec_points C K); [intro; treat_equalities; Cop|intro HCK].
  cut (Par A B C K); [Cop|apply par_col4__par with A B D K; Col].
Qed.

Lemma FCR_ncol__os A B C D K :
  ~ Col A B C -> First_circumscribed_rectangle A B C D K ->
  OS A B C D /\ OS A B C K.
Proof.
intros HNC HF; destruct (FCR_ncol__diffs A B C D K) as [HBD [HDK HKA]]; auto.
destruct HF as [HR HC]; assert_diffs.
assert (HPar : Par A B D K)
  by (apply Rectangle_Parallelogram, plg_par in HR; spliter; auto).
split.
- elim (eq_dec_points C D); [intro; treat_equalities; apply one_side_reflexivity; Col|intro HCD].
  apply l12_6, par_not_col_strict with C; [|Col..].
  apply par_col4__par with A B D K; Col.
- elim (eq_dec_points C K); [intro; treat_equalities; apply one_side_reflexivity; Col|intro HCK].
  apply l12_6, par_not_col_strict with C; [|Col..].
  apply par_col4__par with A B D K; Col.
Qed.

Definition EqT A B C a b c :=
  exists D K d k,
    First_circumscribed_rectangle A B C D K /\
    First_circumscribed_rectangle a b c d k /\
    EqR A B D K a b d k.

Lemma EqT_sym A B C a b c : EqT A B C a b c -> EqT a b c A B C.
Proof.
intro HEQT; destruct HEQT as [D [K [d [k [HFCR1 [HFCR2 HEQR]]]]]].
exists d, k, D, K; do 2 (split; auto); apply EqR_sym; auto.
Qed.

Lemma Circumscribed_rectangle_exists A B C :
  A <> B \/ A <> C \/ B <> C -> exists D K, First_circumscribed_rectangle A B C D K.
Proof.
intro HNE.
assert (HDC : Col A B C -> exists D K, First_circumscribed_rectangle A B C D K).
  {
  assert (HDC : forall A B C,
                  Col A B C -> A <> C ->
                  exists D K : Tpoint, First_circumscribed_rectangle A B C D K).
    {
    clear A B C HNE; intros A B C HC HAC.
    elim (eq_dec_points A B); [intro; treat_equalities|intro HAB].
    - exists C, C; split; [|Col].
      apply Rectangle_triv; auto.
    - exists B, A; split; [|Col].
      apply rect_permut, Rectangle_triv; auto.
    }
  intro HC; destruct HNE as [HAB|[HAC|HBC]].
  - exists B, A; split; [|Col].
    apply rect_permut, Rectangle_triv; auto.
  - destruct (HDC A B C HC HAC) as [D [K [HConvex HR]]].
    exists D, K; split; assumption.
  - assert (HC' : Col B A C) by Col.
    destruct (HDC B A C HC' HBC) as [D [K [HConvex HR]]].
    exists K, D; split; [|Col].
    apply rect_comm2; auto.
  }
elim (col_dec A B C); [apply HDC|clear HNE HDC].
intro HNCol; apply not_col_distincts in HNCol.
destruct HNCol as [HNCol [HNAB [HNBC HNAC]]].
assert (HPar1 : exists L : Tpoint, Par A B C L) by (apply parallel_existence1; auto).
destruct HPar1 as [L HPar1].

assert (HPerp1 : exists X : Tpoint, Perp A B X B /\ Coplanar A B C X) by (apply ex_perp_cop; auto).
destruct HPerp1 as [X [HPerp1 HCop1]].
assert (HCop2 : Coplanar B C L X) by (apply coplanar_trans_1 with A; CopR).
assert (HPerp2 : Perp C L B X) by (apply cop_par_perp__perp with A B; Perp; Par; Cop).
assert (HD : exists D : Tpoint, Col C L D /\ Col B X D /\ Perp_at D C L B X)
  by (apply perp_inter_perp_in_n; Perp).
destruct HD as [D [HDCol1 [HDCol2 HPerp3]]].

assert (HPerp4 : exists Y : Tpoint, Perp A B Y A /\ Coplanar A B C Y) by (apply ex_perp_cop; auto).
destruct HPerp4 as [Y [HPerp4 HCop3]].
assert (HCop4 : Coplanar A C L Y) by (apply coplanar_trans_1 with B; Col; CopR).
assert (HPerp5 : Perp C L A Y) by (apply cop_par_perp__perp with A B; Perp; Par; Cop).
assert (HK : exists K : Tpoint, Col A Y K /\ Col C L K /\ Perp_at K A Y C L)
  by (apply perp_inter_perp_in_n; Perp).
destruct HK as [K [HKCol1 [HKCol2 HPerp6]]].

assert (HNBD : B <> D).
  {
  intro; treat_equalities.
  assert (HCol : Col A B C /\ Col A B L) by (apply not_strict_par with B; Par; Col).
  destruct HCol; auto.
  }
assert (HNAK : A <> K).
  {
  intro; treat_equalities.
  assert (HCol : Col A B C /\ Col A B L) by (apply not_strict_par with A; Par; Col).
  destruct HCol; auto.
  }

assert (HP1 : Perp A B B D) by (apply perp_col1 with X; Perp).
assert (HP2 : Perp B A A K) by (apply perp_col1 with Y; Perp).

assert (HCL : C <> L) by (apply par_distincts in HPar1; spliter; auto).
assert (HCol : Col C D K) by (apply col_transitivity_1 with L; Col).
assert (HNDK : D <> K).
  {
  intro; treat_equalities.
  apply perp_left_comm, perp_per_2, l8_2 in HP1.
  apply perp_left_comm, perp_per_2, l8_2 in HP2.
  apply HNAB, l8_7 with D; auto.
  }
assert (HPar2 : Par A B D K) by (apply par_col4__par with A B C L; Col).
assert (HP3 : Perp B D D K)
  by (apply perp_col4 with B X C L; Col; Perp).
exists D, K; split; [|Col].
apply par__coplanar in HPar2.
apply rect_permut, cop_perp3__rect; Cop; Perp.
Qed.

Lemma Circumscribed_rectangle_unique A B C D K d k :
  A <> B ->
  First_circumscribed_rectangle A B C D K ->
  First_circumscribed_rectangle A B C d k ->
  D = d /\ K = k.
Proof.
intros HAB HF1 HF2.
elim (col_dec A B C); [intro HC3|intro HNC].
- destruct (FCR_Col__eq A B C D K); auto.
  destruct (FCR_Col__eq A B C d k); auto.
  split; congruence.
- destruct (FCR_ncol__diffs A B C D K) as [HBD [HDK HKA]]; auto.
  destruct (FCR_ncol__diffs A B C d k) as [HBd [Hdk Hka]]; auto.
  destruct (FCR_ncol__cop A B C D K) as [HCop1 HCop2]; auto.
  destruct (FCR_ncol__cop A B C d k) as [HCop3 HCop4]; auto.
  destruct HF1 as [HR1 HC1]; destruct HF2 as [HR2 HC2].
  assert (HPar : Par D K d k).
    {
    apply Rectangle_Parallelogram, plg_par in HR1; [spliter|auto..].
    apply Rectangle_Parallelogram, plg_par in HR2; [spliter|auto..].
    apply par_trans with A B; Par.
    }
  split; [apply l6_21 with B D K D|apply l6_21 with A K D K]; Col.
  + apply per_not_col; [auto..|].
    apply rect_per3 with A; assumption.
  + cut (Col D d B); [Col|].
    apply cop_per2__col with A; [apply coplanar_pseudo_trans with A B C; Cop|auto|..].
    * apply rect_per4 with K, rect_permut, rect_permut; assumption.
    * apply rect_per4 with k, rect_permut, rect_permut; assumption.
  + apply (col2_par__col4 _ _ _ _ C) in HPar; [spliter|..]; Col.
  + apply per_not_col; [auto..|].
    apply rect_per4 with B; assumption.
  + cut (Col K k A); [Col|].
    apply cop_per2__col with B; [apply coplanar_pseudo_trans with A B C; Cop|auto|..].
    * apply rect_per2 with D; do 3 apply rect_permut; assumption.
    * apply rect_per2 with d; do 3 apply rect_permut; assumption.
  + apply (col2_par__col4 _ _ _ _ C) in HPar; [spliter|..]; Col.
Qed.

Lemma EqT_FCR__EqR A B C a b c D K d k :
  A <> B -> a <> b -> EqT A B C a b c ->
  First_circumscribed_rectangle A B C D K ->
  First_circumscribed_rectangle a b c d k ->
  EqR A B D K a b d k.
Proof.
intros HAB Hab [D' [K' [d' [k' [HF1 [HF2 HE]]]]]] HF3 HF4.
destruct (Circumscribed_rectangle_unique A B C D' K' D K); auto.
destruct (Circumscribed_rectangle_unique a b c d' k' d k); auto.
treat_equalities; assumption.
Qed.

Lemma FCR_ncol__EqR_perm A B C D K :
  ~ Col A B C -> First_circumscribed_rectangle A B C D K ->
  EqR A B D K A B D K /\ EqR A B D K B D K A /\
  EqR A B D K D K A B /\ EqR A B D K K A B D /\
  EqR A B D K A K D B /\ EqR A B D K K D B A /\
  EqR A B D K D B A K /\ EqR A B D K B A K D.
Proof.
intros HNC HF; destruct (FCR_ncol__diffs A B C D K) as [HBD _]; auto.
apply EqR_perm; [assert_diffs; auto|auto|destruct HF; auto].
Qed.

Lemma EqT_refl A B C : ~ Col A B C -> EqT A B C A B C.
Proof.
intro HNCol; apply not_col_distincts in HNCol.
destruct HNCol as [HNCol [HNAB [HNBC HNAC]]].
assert (H : exists D K, First_circumscribed_rectangle A B C D K)
  by (apply Circumscribed_rectangle_exists; auto).
destruct H as [D [K H]].
assert (HR : Rectangle A B D K) by (destruct H; auto).
assert (HC : Col C D K) by (destruct H; auto).
assert (HNBD : B <> D) by (destruct (FCR_ncol__diffs A B C D K); auto).
exists D, K, D, K.
split; auto.
split; auto.
apply EqR_refl; auto.
Qed.

Lemma EqT_trans A B C D E F G H I : EqT A B C D E F -> EqT D E F G H I -> EqT A B C G H I.
Proof.
intros HEQT1 HEQT2.
destruct HEQT1 as [J [K [j [k [HFCR1 [HFCR2 HEQR1]]]]]].
destruct HEQT2 as [L [M [l [m [HFCR3 [HFCR4 HEQR2]]]]]].
exists J, K, l, m; do 2 (split; auto).
assert (HDE : D <> E) by (apply EqR_diffs in HEQR2; spliter; auto).
destruct (Circumscribed_rectangle_unique D E F j k L M); auto; treat_equalities.
apply EqR_trans with D E j k; auto.
Qed.

Lemma EqT_not_col A B C a b c : EqT A B C a b c -> ~ Col A B C /\ ~ Col a b c.
Proof.
intros [D [K [d [k [HF1 [HF2 HEQR]]]]]].
destruct (EqR_diffs A B D K a b d k HEQR) as [HAB [HBD [Hab Hbd]]].
split; intro HC;
[destruct (FCR_Col__eq A B C D K) as [_ HE]|destruct (FCR_Col__eq a b c d k) as [_ HE]]; auto.
Qed.

Lemma B5_12 A B C D : ~ Col A B C -> Par A B C D -> EqT A B C A B D.
Proof.
intros HNCol HPar.
apply not_col_distincts in HNCol; destruct HNCol as [HNCol [HNAB [HNBC HNAC ]]]; assert_diffs.
assert (HEx : exists D K : Tpoint, First_circumscribed_rectangle A B C D K)
  by (apply Circumscribed_rectangle_exists; auto).
destruct HEx as [G [K HFCR]].
assert (HR : Rectangle A B G K) by (destruct HFCR; auto).
assert (HC : Col C G K) by (destruct HFCR; auto).
assert (HNBD : B <> G) by (destruct (FCR_ncol__diffs A B C G K); auto).
cut (Col G K D).
intro; exists G, K, G, K.
split; auto.
split; unfold First_circumscribed_rectangle; Col.
apply EqR_refl; auto.

assert (HPar2 :Par A B G K) by (apply Rectangle_Parallelogram in HR; apply plg_par_1; auto).
assert (HPar3 : Par C D G K) by (apply par_trans with A B; Par).
apply not_strict_par2 with C C; Par; Col.
Qed.

Lemma Cong_3_same_height_aux1 A B C D K a b c d k :
  Rectangle A B D K -> Rectangle a b d k -> Col c d k ->
  ~ Col A B C -> Cong_3 A B C a b c -> C = D -> c = d.
Proof.
intros HR1 HR2 HC2 HNC1 HC3 HE; subst D.
destruct (FCR_ncol__diffs A B C C K) as [HBD [HDK HKA]]; [assumption|split; Col|].
assert (HNC2 : ~ Col a b c) by (intro; apply cong_3_sym, l4_13 in HC3; Col).
destruct (FCR_ncol__diffs a b c d k) as [Hbd [Hdk Hka]]; [|split|]; auto.
assert_diffs.
assert (HPer1 : Per A B C) by (apply rect_per2 with K; auto).
assert (HPer2 : Per a b c) by (apply l8_10 with A B C; Perp).
assert (HNC3 : ~ Col b d k)
  by (apply per_not_col; auto; apply rect_per4 with a, rect_comm2; auto).
apply l6_21 with b d k d; Col.
cut (Col d c b); [Col|].
apply cop_per2__col with a; Perp.
- apply coplanar_pseudo_trans with b k d; Col; Cop.
- apply rect_per1 with k, rect_permut; auto.
Qed.

Lemma Cong_3_same_height_aux2 A B C D K a b c d k :
  Rectangle A B D K -> Rectangle a b d k -> Col c d k ->
  ~ Col A B C -> Cong_3 A B C a b c -> C = K -> c = k.
Proof.
intros HR1 HR2 HC2 HNC1 HC3 HE; subst K.
destruct (FCR_ncol__diffs A B C D C) as [HBD [HDK HKA]]; [assumption|split; Col|].
assert (HNC2 : ~ Col a b c) by (intro; apply cong_3_sym, l4_13 in HC3; Col).
destruct (FCR_ncol__diffs a b c d k) as [Hbd [Hdk Hka]]; [|split|]; auto.
assert_diffs.
assert (HPer1 : Per B A C) by (apply rect_per1 with D; auto).
assert (HPer2 : Per b a c).
  {
  apply l8_10 with B A C; Perp.
  destruct HC3 as [HC3 [HC4 HC5]]; split; [|split]; Cong.
  }
assert (HNC3 : ~ Col a k d)
  by (apply per_not_col; auto; apply rect_per4 with b; auto).
apply l6_21 with a k d k; Col.
cut (Col c k a); [Col|].
apply cop_per2__col with b; Perp.
- apply coplanar_pseudo_trans with a k d; Cop.
- apply rect_per3 with d; do 2 apply rect_permut; auto.
Qed.

Lemma Cong_3_same_height_aux3 A B C D K HC :
  Rectangle A B D K -> Col C D K -> ~ Col A B C -> C <> K -> C <> D ->
  Col A B HC -> Perp A B C HC ->
  A <> HC /\ B <> HC /\ Rectangle B HC C D.
Proof.
intros HR1 HC1 HNC1 HCK HCD HC4 HPerp1.
assert (HAB : A <> B) by (assert_diffs; auto).
assert (HAC : A <> C) by (assert_diffs; auto).
destruct (FCR_ncol__diffs A B C D K) as [HBD [HDK HKA]]; [|split|]; auto.
assert (HPar1 : Par A K C HC).
  {
  apply l12_9 with A B; Cop; Perp.
  apply coplanar_pseudo_trans with D K B; Cop.
  - cut (~ Col B D K); [Col|apply per_not_col; auto].
    apply rect_per2 with A, rect_permut; auto.
  - cut (Perp B A A K); [Perp|].
    cut (Per B A K); [apply per_perp; auto|].
    apply rect_per1 with D; auto.
  }
assert (HPar2 : Par B D C HC).
  {
  apply l12_9 with A B; Cop; Perp.
  - cut (Par A B C D); [Cop|].
    apply par_col4__par with A B D K; Col.
    apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
  - cut (Perp A B B D); [Perp|].
    cut (Per A B D); [apply per_perp; auto|].
    apply rect_per2 with K; auto.
  }
assert (HAHC : A <> HC).
  {
  intro; treat_equalities; apply HCK.
  apply l6_21 with A K D K; Col.
  apply per_not_col; auto.
  apply rect_per4 with B; auto.
  }
assert (HBHC : B <> HC).
  {
  intro; treat_equalities; apply HCD.
  apply l6_21 with B D K D; Col.
  apply per_not_col; auto.
  apply rect_per2 with A, rect_permut; auto.
  }
split; [|split]; auto.
do 2 apply rect_permut; apply cop_perp3__rect; Cop.
- apply perp_col4 with K D D B; Col; Perp.
  cut (Per K D B); [apply per_perp; auto|].
  apply rect_per4 with A; do 3 apply rect_permut; auto.
- apply perp_col4 with D B B A; Col; Perp.
  cut (Per D B A); [apply per_perp; auto|].
  apply rect_per4 with K; do 2 apply rect_permut; auto.
- apply perp_col4 with A B C HC; Col; Perp; assert_diffs; auto.
Qed.

Lemma Cong_3_same_height A B C D K a b c d k :
  Rectangle A B D K -> Col C D K ->
  Rectangle a b d k -> Col c d k ->
  ~ Col A B C -> Cong_3 A B C a b c ->
  Cong B D b d.
Proof.
intros HR1 HC1 HR2 HC2 HNC1 HC3.
assert (HAB : A <> B) by (assert_diffs; auto).
assert (HAC : A <> C) by (assert_diffs; auto).
assert (HNC2 : ~ Col a b c) by (intro; apply cong_3_sym, l4_13 in HC3; Col).
assert (Hab : a <> b) by (assert_diffs; auto).
assert (Hac : a <> c) by (assert_diffs; auto).
assert (HEP1 : C = D <-> c = d).
  {
  split; [apply (Cong_3_same_height_aux1 A B C D K a b c d k)|
          apply (Cong_3_same_height_aux1 a b c d k A B C D K)]; auto.
  apply cong_3_sym; auto.
  }
assert (HEP2 : C = K <-> c = k).
  {
  split; [apply (Cong_3_same_height_aux2 A B C D K a b c d k)|
          apply (Cong_3_same_height_aux2 a b c d k A B C D K)]; auto.
  apply cong_3_sym; auto.
  }
assert (HEC : C = K -> Cong B D b d).
  {
  intro; treat_equalities; cut (c = k); [intro HE|tauto].
  apply Rectangle_Parallelogram, plg_cong in HR1.
  apply Rectangle_Parallelogram, plg_cong in HR2.
  treat_equalities; destruct HC3; spliter; CongR.
  }
elim (eq_dec_points C K); [auto|clear HEC; intro HCK].
cut (c <> k); [clear HEP2; intro Hck|tauto].
assert (HEC : C = D -> Cong B D b d).
  {
  intro; treat_equalities. cut (c = d); [intro HE|tauto].
  apply Rectangle_Parallelogram, plg_cong in HR1.
  apply Rectangle_Parallelogram, plg_cong in HR2.
  treat_equalities; destruct HC3; spliter; CongR.
  }
elim (eq_dec_points C D); [auto|clear HEC; intro HCD].
cut (c <> d); [clear HEP1; intro Hcd|tauto].
destruct (l8_18_existence A B C) as [HC [HC4 HPerp1]]; [Col|].
destruct (Cong_3_same_height_aux3 A B C D K HC) as [HAHC [HBHC HR3]]; auto.
destruct (l8_18_existence a b c) as [Hc [HC5 HPerp2]]; [Col|].
destruct (Cong_3_same_height_aux3 a b c d k Hc) as [HaHc [HbHc HR4]]; auto.
assert (HC6 : Cong C HC c Hc).
  {
  keep HNC1 HC3 HAB HAC HNC2 Hab Hac HC4 HPerp1 HAHC HBHC HC5 HPerp2 HaHc HbHc.
  assert (HCA : CongA C A HC c a Hc).
    {
    destruct (angle_partition C A B) as [HAcute|[HPer|HObtuse]]; auto.
    - assert (HO1 : Out A HC B)
        by (apply (acute_col_perp__out C A B HC); auto).
      assert (HO2 : Out a Hc b).
        {
        apply (acute_col_perp__out c a b Hc); auto.
        apply acute_conga__acute with C A B; [auto|].
        apply cong3_conga; auto.
        destruct HC3 as [? []]; split; [|split]; Cong.
        }
      apply l11_10 with C B c b; auto; [|apply out_trivial; auto..].
      apply cong3_conga; auto.
      destruct HC3 as [? []]; split; [|split]; Cong.
    - exfalso; apply HAHC; apply (l8_18_uniqueness A B C); Col; Perp.
    - assert (HB1 : Bet B A HC).
        {
        apply (perp_obtuse_bet B A C HC); Col; Perp.
        apply obtuse_sym; auto.
        }
      assert (HB2 : Bet b a Hc).
        {
        apply (perp_obtuse_bet b a c Hc); Col; Perp.
        apply conga_obtuse__obtuse with C A B; [auto|].
        apply conga_left_comm, cong3_conga; auto.
        destruct HC3 as [? []]; split; [|split]; Cong.
        }
      apply conga_comm, l11_13 with B b; auto.
      apply cong3_conga; auto.
      destruct HC3 as [? []]; split; [|split]; Cong.
      }
    destruct (l11_50_2 C A HC c a Hc); Cong.
    - intro; apply HNC1; ColR.
    - keep HNC1 HC3 HAB HAC HNC2 Hab Hac HC4 HPerp1 HAHC HBHC HC5 HPerp2 HaHc HbHc HCA. apply l11_16; try solve [assert_diffs; auto].
      + cut (Perp A HC HC C); [Perp|].
        apply perp_col4 with A B HC C; Col; Perp; assert_diffs; auto.
      + cut (Perp a Hc Hc c); [Perp|].
        apply perp_col4 with a b Hc c; Col; Perp; assert_diffs; auto.
    - destruct HC3 as [? []]; Cong.
  }
apply Rectangle_Parallelogram, plg_cong in HR1.
apply Rectangle_Parallelogram, plg_cong in HR2.
apply Rectangle_Parallelogram, plg_cong in HR3.
apply Rectangle_Parallelogram, plg_cong in HR4; spliter; CongR.
Qed.

Theorem B6_1 A B C : ~ Col A B C -> EqT A B C B C A.
Proof.
intro HNC.
destruct (Circumscribed_rectangle_exists A B C) as [D [K HF1]]; [assert_diffs; auto|].
destruct (Circumscribed_rectangle_exists B C A) as [d [k HF2]]; [assert_diffs; auto|].
exists D, K, d, k; split; [assumption|split; [assumption|]].
(* This simplifies the paper's proof of Theorem 6.1.  The paper builds Fig. 12
   from a congruent copy A' B C' of the triangle and shows that the diagonals
   E B and B G are aligned; that last step re-proves the converse direction of
   Lemma 5.2 (B5_2_1_2).  Applying Lemma 5.2 directly, it is enough to show
   AB : BC = Cd : BD, and the copy A' B C' is no longer needed: the right
   triangles B D C and B k A play the role of the triangles C D B and A' F B
   of the paper. *)
destruct (FCR_ncol__diffs A B C D K) as [HBD [HDK HKA]]; auto.
destruct (FCR_ncol__diffs B C A d k) as [HCd [Hdk HkB]]; [Col|auto|].
destruct (FCR_ncol__os A B C D K) as [HOS1 _]; auto.
destruct (FCR_ncol__os B C A d k) as [_ HOS2]; [Col|auto|].
destruct HF1 as [HR1 HC1]; destruct HF2 as [HR2 HC2].
assert_diffs.
apply B5_2_1_2; [assumption..|].
assert (HC3 : Cong B k C d)
  by (apply Rectangle_Parallelogram, plg_cong in HR2; spliter; Cong).
assert (HP1 : Per A B D) by (apply rect_per2 with K; auto).
assert (HP2 : Per C B k) by (apply rect_per1 with d; auto).
assert (HE : C = D <-> A = k).
  {
  split; intro HE; [subst D|subst k].
  - apply l6_21 with B k d k; Col.
    + apply per_not_col; [intro; subst; auto..|apply rect_per4 with C; auto].
    + cut (Col k A B); [Col|apply cop_per2__col with C; Perp].
      assert (HCop := rectangle__coplanar B C d k HR2); CopR.
  - apply l6_21 with B D K D; Col.
    + apply per_not_col; [intro; subst; auto..|apply rect_per3 with A; auto].
    + cut (Col D C B); [Col|apply cop_per2__col with A; Perp].
      assert (HCop := rectangle__coplanar A B D K HR1); CopR.
  }
elim (eq_dec_points C D); [intro HCD|intro HCD].
- assert (A = k) by tauto; treat_equalities.
  apply EqF_cong with A B B C A B B C; Cong.
  exists B, A, C, B, A, C; do 4 (split; Cong).
  apply EqRT_BAC_BAC; auto.
- assert (HAk : A <> k) by tauto.
  assert (HP3 : Per B D C)
    by (apply per_col with K; Col; apply rect_per3 with A; auto).
  assert (HP4 : Per B k A)
    by (apply per_col with d; Col; apply rect_per4 with C; auto).
  assert (HCA : CongA D B C k B A).
    {
    apply (l11_22 D B C A k B A C); split; [right; split; Side|split].
    - apply l11_16; Perp.
    - apply conga_pseudo_refl; auto.
    }
  assert (HEQF : EqF B D B C B k B A).
    {
    apply CongA2__EqF; [|apply l11_16; Perp; auto|auto].
    apply per_not_col; auto.
    }
  apply interchange_theorem, EqF_abcd_badc, EqF_sym in HEQF.
  apply EqF_cong with B A B C B k B D; Cong.
Qed.

(* B6_2 *)
Lemma Cong_3__EqT A B C a b c :
  ~ Col A B C -> Cong_3 A B C a b c -> EqT A B C a b c.
Proof.
intros HNCol HCong3.
apply not_col_distincts in HNCol; destruct HNCol as [HNCol [HNAB [HNBC HNAC ]]]; assert_diffs.
assert (HNCol2 : ~ Col a b c)
  by (intro; assert (HC : Col A B C) by (apply l4_13 with a b c; Cong); Col).
assert (H1 : exists D K : Tpoint, First_circumscribed_rectangle A B C D K)
  by (apply Circumscribed_rectangle_exists; auto).
assert (H2 : exists D K : Tpoint, First_circumscribed_rectangle a b c D K)
  by (apply Circumscribed_rectangle_exists; assert_diffs; auto).
destruct H1 as [D [K H]]; destruct H2 as [d [k H2]].
assert (HR : Rectangle A B D K) by (destruct H; auto).
assert (HC : Col C D K) by (destruct H; auto).
assert (HNBD : B <> D) by (destruct (FCR_ncol__diffs A B C D K); auto).
assert (HR2 : Rectangle a b d k) by (destruct H2; auto).
assert (HC2 : Col c d k) by (destruct H2; auto).
assert (HNbd : b <> d) by (destruct (FCR_ncol__diffs a b c d k); auto).
exists D, K, d, k.
split; auto.
split; auto.
apply B5_5; auto.
destruct HCong3; spliter; auto.
apply Cong_3_same_height with A C K a c k; auto.
Qed.

(* B6_3_1 *)
Lemma EqT_ABC_BAC A B C : ~ Col A B C -> EqT A B C B A C.
Proof.
intro HNCol.
apply not_col_distincts in HNCol; destruct HNCol as [HNCol [HNAB [HNBC HNAC ]]]; assert_diffs.
assert (H : exists D K : Tpoint, First_circumscribed_rectangle A B C D K)
  by (apply Circumscribed_rectangle_exists; auto).
destruct H as [D [K H]].
assert (HR : Rectangle A B D K) by (destruct H; auto).
assert (HC : Col C D K) by (destruct H; auto).
assert (HNBD : B <> D) by (destruct (FCR_ncol__diffs A B C D K); auto).
exists D, K, K, D.
split; auto.
split; unfold First_circumscribed_rectangle.
apply rect_comm2 in HR; split; auto;  Col.
apply EqR_perm; auto.
Qed.

Lemma B6_3 A B C : ~ Col A B C ->
  EqT A B C B C A /\ EqT A B C B A C /\ EqT A B C C A B /\
  EqT A B C A C B /\ EqT A B C C B A .
Proof.
intro HNcol.
assert (H1 : EqT A B C B C A) by (apply B6_1; auto).
assert (H2 : EqT A B C B A C) by (apply EqT_ABC_BAC; auto).
do 2 (split; auto).
split.
apply EqT_trans with B C A; auto; apply B6_1; Col.
split.
apply EqT_trans with B A C; auto; apply B6_1; Col.
apply EqT_trans with B C A; auto; apply EqT_ABC_BAC; Col.
Qed.

Lemma B6_4 A B C D : A <> B -> B <> C -> Bet A B C -> ~ EqT C A D B A D.
Proof.
intros HNAB HNBC HBet HEQT.
unfold EqT in HEQT.
destruct HEQT as [G [K [g [k [H1 [H2 H3]]]]]].
destruct H1; destruct H2.
assert (HNP : C <> A /\ A <> G /\ B <> A /\ A <> g) by (apply EqR_diffs with K k; auto); spliter.
assert (HR1 : Rectangle A G K C) by (apply rect_permut; auto).
assert (HR2 : Rectangle A g k B) by (apply rect_permut; auto).
assert (HNGK : G <> K) by (intro; treat_equalities; apply degenerated_rect_eq in HR1; auto).
assert (HNgk : g <> k)
  by (intro; treat_equalities ;apply rect_permut in H1; apply degenerated_rect_eq in H1; auto).
assert (HEQR : EqR A G K C C A G K) by (apply EqR_perm; auto).
assert (HEQR2 : EqR B A g k A g k B) by (apply EqR_perm; auto).
assert (HEQR3 : EqR A G K C A g k B)
  by (apply EqR_trans with C A G K; auto; apply EqR_trans with B A g k; auto).
assert (HPar1 : Par B A g k) by (apply Rectangle_Parallelogram in H1; apply plg_par_1 in H1; auto).
assert (HPar2 : Par A C K G) by (apply Rectangle_Parallelogram in H; apply plg_par_1 in H; Par).
assert (HPar3 : Par A B K G) by (apply bet_col in HBet; auto; apply par_col_par_2 with C; auto; Col).
assert (HPerp1: Perp A g A B)
  by (apply rect_per2 in H1; apply perp_left_comm; apply per_perp; auto; Perp).
assert (HPerp2: Perp A G A B).
  {
  apply perp_col1 with C; auto; apply bet_col in HBet; Col.
  apply rect_per2 in H; apply perp_left_comm; apply per_perp; auto; Perp.
  }
assert (HPar4 : Par K G k g) by (apply par_trans with A B; Par).
assert (HP : Col K G g /\ Col K G k) by (apply not_strict_par with D; Par; Col).
destruct HP.
assert (HCop1 : Coplanar A B G g).
  {
  apply par__coplanar in HPar3.
  apply col_cop__cop with K; auto; Col; Cop.
  }
assert (HCol1 : Col A G g) by (apply cop_perp2__col with A B; auto).
assert(HNgK : K <> g).
  {
  intro; treat_equalities.
  assert (HPF : Parallelogram_flat C A G K).
  do 3 (apply plgf_permut); apply plg_col_plgf; auto.
  apply Rectangle_Parallelogram in H; apply plg_permut in H; auto.
  assert (HP : C = K /\ A = G \/ C = A /\ K = G) by (apply plgf_rect_id; auto).
  destruct HP as [[]|[]]; auto.
  }
assert (HCol3 : Col K g k) by (apply col_transitivity_1 with G; Col).
assert (HGg : G = g).
  {
  apply per2_col_eq with K A; auto; Col.
  apply rect_per3 in H; Perp.
  apply rect_per3 in H1.
  apply l8_2.
  apply per_col with k; Col.
  }
assert (HCong1 : Cong A G A g) by (treat_equalities; Cong).
apply B5_5 in HEQR3; auto.
apply Rectangle_Parallelogram in H; apply Rectangle_Parallelogram in H1.
apply plg_cong_1 in H.
apply plg_cong_1 in H1.
assert (HCong2 : Cong A C A B)
  by (apply cong_transitivity with G K; Cong; apply cong_transitivity with g k; Cong).
assert (HBC : B = C).
apply between_cong with A; auto; Cong.
auto.
Qed.

Lemma B6_5 A B C E F : ~ Col A B C -> E <> A -> F <> C -> Bet B E A -> Bet B F C ->
  ~ EqT A B C E B F.
Proof.
intros HNCol1 HNAE HNFC HB1 HB2 HEQT.
assert (HNCol2 : ~ Col E B F) by (destruct (EqT_not_col A B C E B F); auto).
assert (HEQT2 : EqT B C A B F E)  by (apply EqT_trans with A B C; [apply B6_3; Col|];
  apply EqT_trans with E B F; auto; apply B6_3; Col).
destruct HEQT2 as [D [K [d [k [HF1 [HF2 HEQR]]]]]].
destruct HF1; destruct HF2.
assert (HLt1 : Lt B F B C) by (apply bet__lt1213; auto).
cut (Lt F d C D).
- intro.
  apply not_col_distincts in HNCol2; spliter.
  assert (HNFd : F <> d).
    {
    intro; treat_equalities.
    assert (HBk : B = k) by (apply degenerated_rect_eq in H1; auto); treat_equalities.
    Col.
    }
  assert (HNEQT : ~ EqR B C D K B F d k).
  apply B5_6; assert_diffs; auto.
  auto.
- assert (HBF : B <> F) by (intro; subst; apply HNCol2; Col).
  assert (HCD : C <> D).
    {
    intro; treat_equalities.
    apply degenerated_rect_eq in H; treat_equalities; Col.
    }
  destruct (rect_cut_exists B C D K F) as [Q [HB3 [HR1 HR2]]]; [assert_diffs; auto|auto..|].
  assert (HFQ : F <> Q)
    by (intro; treat_equalities; apply rect_permut, rect_permut, degenerated_rect_eq in HR2; auto).
  assert (HPar1 : Par B C K D)
    by (apply Rectangle_Parallelogram, plg_par in H; [spliter; Par|assert_diffs; auto..]).
  assert (Hdk : d <> k)
    by (intro; treat_equalities; apply rect_permut, degenerated_rect_eq in H1;
        treat_equalities; Col).
  assert (HFd : F <> d)
    by (intro; treat_equalities; apply degenerated_rect_eq in H1; treat_equalities; Col).
  assert (HPar2 : Par B C d k).
    {
    apply par_col4__par with B F d k; Col; [assert_diffs; auto|].
    apply Rectangle_Parallelogram, plg_par in H1; [spliter; Par|auto..].
    }
  assert (HNP : ~ Par F Q B C).
    {
    intro HF; apply (not_strict_par _ _ _ _ F) in HF; [spliter|Col..].
    apply (per_not_col B F Q); auto; [apply rect_per2 with K; assumption|ColR].
    }
  assert (HCol : Col F Q d).
    {
    cut (Col Q d F); [Col|apply cop_per2__col with B; [|auto|..]].
    - assert (HCop1 : Coplanar B C A Q).
        {
        destruct (FCR_ncol__cop B C A D K) as [HCop1 HCop2]; [Col|split; assumption|].
        apply col_cop2__cop with K D; Col.
        intro; treat_equalities; apply rect_permut, degenerated_rect_eq in H.
        treat_equalities; apply HNCol1; Col.
        }
      assert (HCop2 : Coplanar B F E d)
        by (destruct (FCR_ncol__cop B F E d k); [Col|split; assumption|assumption]).
      apply coplanar_pseudo_trans with A B C; [Col|Cop|Cop| |Cop].
      apply coplanar_pseudo_trans with B F E; Col; Cop.
    - apply l8_2, rect_per2 with K; assumption.
    - apply l8_2, rect_per2 with k; assumption.
    }
  assert (HP1 : Proj B F F Q B C).
    {
    split; [auto|split; [assert_diffs; auto|split; [auto|split; [Col|left]]]].
    right; repeat split; Col; assert_diffs; auto.
    }
  assert (HP2 : Proj E d F Q B C).
    {
    split; [auto|split; [assert_diffs; auto|split; [auto|split; [Col|]]]].
    elim (eq_dec_points E d); [right; auto|intro HEd; left].
    apply par_col4__par with d k B C; Col; Par; assert_diffs; auto.
    }
  assert (HP3 : Proj A Q F Q B C).
    {
    split; [auto|split; [assert_diffs; auto|split; [auto|split; [Col|]]]].
    elim (eq_dec_points A Q); [right; auto|intro HAQ; left].
    apply par_col4__par with K D B C; Col; Par; assert_diffs; auto.
    }
  apply cong2_lt__lt with F d F Q.
  + apply bet__lt1213; [|apply (project_preserves_bet F Q B C B E A F d Q); auto].
    intro; subst; apply HNAE.
    assert (HPar3 : Par E A B C) by (apply (ker_par E A Q F Q B C); auto).
    apply (not_strict_par _ _ _ _ B) in HPar3; [spliter; exfalso; apply HNCol1; ColR|Col..].
  + Cong.
  + apply Rectangle_Parallelogram, plg_cong in HR2; spliter; Cong.
Qed.

Definition Convex J K L M := exists E, Bet J E L /\ Bet K E M.

Definition circumscribed_rectangle J K L M A B C D :=
  Convex J K L M /\
  (First_circumscribed_rectangle J L K A B /\
   First_circumscribed_rectangle J L M D C \/
   First_circumscribed_rectangle K M J A B /\
   First_circumscribed_rectangle K M L D C).

Lemma convex_ncol__ncol J K L M :
  Convex J K L M -> ~ Col J L K \/ ~ Col J L M -> ~ Col K M J \/ ~ Col K M L.
Proof.
intros HConvex HNCE.
assert (HNE : J <> L /\ K <> M); [|destruct HNE as [HJL HKM]].
  {
  destruct HConvex as [I []]; split; intro; treat_equalities;
  destruct HNCE as [HF|HF]; apply HF; Col.
  }
elim (col_dec K M J); [|Col]; elim (col_dec K M L); [|Col].
intros HC1 HC2; exfalso; cut (Col J L K /\ Col J L M); [|split; ColR].
intros []; destruct HNCE; Col.
Qed.

Lemma circumscribed_rectangle__bet J K L M A B C D :
  ~ Col J L K \/ ~ Col J L M ->
  Convex J K L M ->
  First_circumscribed_rectangle J L K A B ->
  First_circumscribed_rectangle J L M D C ->
  Bet A L D /\ Bet B J C.
Proof.
cut (forall J K L M A B C D,
       ~ Col J L K \/ ~ Col J L M ->
       Convex J K L M ->
       First_circumscribed_rectangle J L K A B ->
       First_circumscribed_rectangle J L M D C ->
       Bet A L D);
[intros H HNCE HC HR1 HR2; split; [apply (H J K L M A B C D); assumption|]|];
[apply (H L K J M B A D C);
 [destruct HNCE; [left|right]; Col|
  destruct HC as [I []]; exists I; split; Between|
  apply FCR_ABCDK_BACKD; assumption|
  apply FCR_ABCDK_BACKD; assumption]|].
clear J K L M A B C D; intros J K L M A B C D HNCE HC HF1 HF2.
assert (HJL : J <> L).
  {
  intro; destruct HNCE as [HF|HNC]; [treat_equalities; Col|apply HNC].
  destruct HC as [I [HB1 HB2]]; treat_equalities; Col.
  }
elim (col_dec J K L); [intro HC4|intro HNC1].
  {
  destruct (FCR_Col__eq J L K A B); [assumption|Col|assumption|].
  treat_equalities; Between.
  }
elim (col_dec J L M); [intro HC4|intro HNC2].
  {
  destruct (FCR_Col__eq J L M D C); [assumption|Col|assumption|].
  treat_equalities; Between.
  }
destruct (FCR_ncol__cop J L K A B) as [HCop1 _]; [Col|assumption|].
destruct (FCR_ncol__cop J L M D C) as [HCop2 _]; [Col|assumption|].
destruct (FCR_ncol__os J L K A B) as [HOS1 _]; [Col|assumption|].
destruct (FCR_ncol__os J L M D C) as [HOS2 _]; [Col|assumption|].
destruct HF1 as [HR1 HC1]; destruct HF2 as [HR2 HC2].
assert (HC3 : Col A D L).
  {
  apply cop_per2__col with J; [|assumption|
                               apply rect_per1 with B, rect_permut; assumption|
                               apply rect_per1 with C, rect_permut; assumption].
  assert (HCop3 : Coplanar J L K M)
    by (destruct HC as [I []]; exists I; left; split; Col).
  apply coplanar_pseudo_trans with J L K; try solve [Col|Cop].
  apply coplanar_pseudo_trans with J L M; Col; Cop.
  }
apply col_two_sides_bet with J; [Col|].
apply l9_8_2 with K; [apply l9_2, l9_8_2 with M|]; [|Side..].
split; [Col|split; [Col|]].
destruct HC as [I [HB1 HB2]]; exists I; split; [Col|Between].
Qed.

Lemma circumscribed_rectangle__rectangle J K L M A B C D :
  ~ Col J L K \/ ~ Col J L M ->
  circumscribed_rectangle J K L M A B C D ->
  A <> B /\ B <> C /\ Rectangle A B C D.
Proof.
assert (H : forall J K L M A B C D,
              ~ Col J L K \/ ~ Col J L M ->
              Convex J K L M ->
              First_circumscribed_rectangle J L K A B ->
              First_circumscribed_rectangle J L M D C ->
              A <> B /\ B <> C /\ Rectangle A B C D).
  {
  clear J K L M A B C D; intros J K L M A B C D HNCE HConvex HR1 HR2.
  assert (HJL : J <> L) by (intro; subst; destruct HNCE as [HF|HF]; apply HF; Col).
  destruct (circumscribed_rectangle__bet J K L M A B C D) as [_ HB]; auto.
  destruct HR1 as [HR1 HC1]; destruct HR2 as [HR2 HC2].
  split; [|split].
  - intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR1; treat_equalities; auto.
  - intro; treat_equalities.
    apply rect_permut, rect_permut, degenerated_rect_eq in HR1.
    apply rect_permut, rect_permut, degenerated_rect_eq in HR2.
    treat_equalities; destruct HNCE as [HF|HF]; apply HF; Col.
  - apply extent_rect with J L; [assumption| |apply rect_comm2; assumption].
    apply rect_permut, rect_permut; assumption.
  }
intros HNCE [HConvex [[HR1 HR2]|[HR1 HR2]]]; [apply (H J K L M); assumption|].
apply (H K J M L); [apply convex_ncol__ncol; assumption| |assumption..].
destruct HConvex as [I []]; exists I; split; Between.
Qed.

Lemma split_triangle__EqR J K M I A B IAB b c Iab Icd :
  ~ Col I J K -> ~ Col I J M -> Bet K I M ->
  First_circumscribed_rectangle I K J B IAB ->
  First_circumscribed_rectangle I M J A IAB ->
  First_circumscribed_rectangle I J K b Iab ->
  First_circumscribed_rectangle I J M c Icd ->
  EqR A M K B c Icd Iab b.
Proof.
intros HNC1 HNC2 HB HR1 HR2 HR3 HR4.
assert (ER1 : EqR K I IAB B I J b Iab).
  {
  apply (EqT_FCR__EqR K I J I J K); [assert_diffs; auto..|apply B6_1; Col| |assumption].
  apply FCR_ABCDK_BACKD; assumption.
  }
assert (ER2 : EqR M I IAB A I J c Icd).
  {
  apply (EqT_FCR__EqR M I J I J M); [assert_diffs; auto..|apply B6_1; Col| |assumption].
  apply FCR_ABCDK_BACKD; assumption.
  }
assert (HB2 : Bet Iab I Icd).
  {
  destruct (circumscribed_rectangle__bet I K J M b Iab Icd c);
  [left; Col|exists I; split; Between|assumption..|assumption].
  }
apply (B5_8 A M I IAB K B c Icd I J Iab b); Between.
- assert (ER3 : EqR A M I IAB M I IAB A).
    {
    destruct (FCR_ncol__EqR_perm I M J A IAB); [Col|assumption|spliter].
    apply EqR_trans with I M A IAB; [apply EqR_sym|]; assumption.
    }
  apply EqR_trans with M I IAB A; [assumption|].
  apply EqR_trans with I J c Icd; [assumption|].
  destruct (FCR_ncol__EqR_perm I J M c Icd); [Col|assumption|spliter; assumption].
- assert (ER3 : EqR IAB I K B K I IAB B).
    {
    destruct (FCR_ncol__EqR_perm I K J B IAB); [Col|assumption|spliter].
    apply EqR_trans with I K B IAB; [apply EqR_sym|]; assumption.
    }
  apply EqR_trans with K I IAB B; [assumption|].
  apply EqR_trans with I J b Iab; [assumption|].
  destruct (FCR_ncol__EqR_perm I J K b Iab); [Col|assumption|spliter; assumption].
Qed.

Lemma circumscribed_rectangle_EqR J K L M A B C D a b c d :
  ~ Col J L K \/ ~ Col J L M ->
  circumscribed_rectangle J K L M A B C D ->
  circumscribed_rectangle J K L M a b c d ->
  EqR A B C D a b c d.
Proof.
intros HNCE1 HR1 HR3.
assert (HConvex1 : Convex J K L M) by (destruct HR1 as [HC _]; assumption).
assert (HConvex2 : Convex K J M L)
  by (destruct HConvex1 as [I []]; exists I; split; Between).
assert (HNE : J <> L /\ K <> M); [|destruct HNE as [HJL HKM]].
  {
  destruct HConvex1 as [I []]; split; intro; treat_equalities;
  destruct HNCE1 as [HF|HF]; apply HF; Col.
  }
assert (HNCE2 : ~ Col K M J \/ ~ Col K M L)
  by (apply convex_ncol__ncol; assumption).
assert (HSQ : forall J K L M A B C D a b c d,
                ~ Col J L K \/ ~ Col J L M ->
                ~ Col K M J \/ ~ Col K M L ->
                First_circumscribed_rectangle J L K A B ->
                First_circumscribed_rectangle J L M D C ->
                Convex J K L M -> J <> L -> K <> M ->
                First_circumscribed_rectangle J L K a b ->
                First_circumscribed_rectangle J L M d c ->
                EqR A B C D a b c d).
  {
  clear J K L M A B C D a b c d HNCE1 HNCE2 HConvex1 HConvex2 HJL HKM HR1 HR3.
  intros J K L M A B C D a b c d HNCE1 HNCE2 HR1 HR2 HConvex HJL HKM HR3 HR4.
  destruct (Circumscribed_rectangle_unique J L K A B a b); [assumption..|].
  destruct (Circumscribed_rectangle_unique J L M D C d c); [assumption..|].
  destruct HR1 as [HR1 HC1]; destruct HR2 as [HR2 HC2].
  assert (HB : Bet A L D).
    {
    destruct (circumscribed_rectangle__bet J K L M A B C D);
    [| |split..|]; assumption.
    }
  assert (HR5 : Rectangle A B C D).
    {
    apply rect_comm2, extent_rect with L J; [auto| |assumption].
    apply rect_comm2, rect_permut, rect_permut; assumption.
    }
  assert (HAB : A <> B).
    {
    intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR1; auto.
    }
  treat_equalities; apply EqR_refl; [assumption| |assumption].
  intro; treat_equalities; apply degenerated_rect_eq in HR5; treat_equalities.
  apply degenerated_rect_eq in HR1; treat_equalities.
  destruct HNCE1 as [HF|HF]; apply HF; Col.
  }
assert (HDQ : forall J K L M A B C D a b c d,
                ~ Col J L K \/ ~ Col J L M ->
                ~ Col K M J \/ ~ Col K M L ->
                First_circumscribed_rectangle K M J A B ->
                First_circumscribed_rectangle K M L D C ->
                Convex J K L M -> J <> L -> K <> M ->
                First_circumscribed_rectangle J L K a b ->
                First_circumscribed_rectangle J L M d c ->
                EqR A B C D a b c d).
  {
  clear J K L M A B C D a b c d HNCE1 HNCE2 HConvex1 HConvex2 HJL HKM HR1 HR3.
  clear HSQ; assert (HDQOC : forall J K L M A B C D a b c d,
                               Col J L K -> ~ Col J L M ->
                               First_circumscribed_rectangle K M J A B ->
                               First_circumscribed_rectangle K M L D C ->
                               Convex J K L M -> J <> L -> K <> M ->
                               First_circumscribed_rectangle J L K a b ->
                               First_circumscribed_rectangle J L M d c ->
                               EqR A B C D a b c d).
    {
    intros J K L M A B C D a b c d HC HNC HR1 HR2 HConvex HJL HKM HR3 HR4.
    assert (a = L /\ b = J) by (destruct (FCR_Col__eq J L K a b); Col).
    spliter; treat_equalities; clear HR3; rename HR4 into HR3.
    destruct HConvex as [I [HB1 HB2]].
    assert (K = I); [solve [apply (l6_21 a b M K); Col]|].
    clear HC; treat_equalities; rename HNC into HNC1.
    assert (HSQ : forall K M A B C D a b c d,
                    First_circumscribed_rectangle K M b A B ->
                    First_circumscribed_rectangle K M a D C ->
                    ~ Col a b M -> Bet a K b -> K <> M ->
                    Col K M a -> ~ Col K M b ->
                    First_circumscribed_rectangle b a M d c ->
                    EqR A B C D a b c d).
      {
      clear K M A B C D a b c d HR1 HR2 HR3 HB1 HNC1 HJL HKM.
      intros K M A B C D a b c d HR1 HR2 HNC1 HB HKM HC HNC2 HR3.
      assert (C = K /\ D = M) by (destruct (FCR_Col__eq K M a D C); Col).
      spliter; treat_equalities; clear HR2 HKM; rename HR3 into HR2.
      elim (eq_dec_points a C); [|intro HaC; exfalso; apply HNC2; ColR].
      intro; treat_equalities.
      assert (ER : EqR D a B A a b c d).
        {
        apply (EqT_FCR__EqR D a b a b D); [assert_diffs; auto..|apply B6_1; Col| |];
        apply FCR_ABCDK_BACKD; assumption.
        }
      apply EqR_trans with D a B A; [|assumption].
      destruct ER as [HaD [HaB [HRect _]]].
      apply rect_comm2, rect_permut, rect_permut in HRect.
      destruct (EqR_perm A B a D); [|auto..|spliter; assumption].
      intro; treat_equalities; do 3 apply rect_permut in HRect.
      apply degenerated_rect_eq in HRect; apply HaD; auto.
      }
    assert (HE : Col K M a \/ Col K M b \/ ~ Col K M a /\ ~ Col K M b).
      {
      elim (col_dec K M a); [tauto|].
      elim (col_dec K M b); tauto.
      }
    assert (HNCE : ~ Col K M b \/ ~ Col K M a).
      {
      elim (col_dec K M b); [intro HC1|tauto].
      elim (col_dec K M a); [intro HC2|tauto].
      exfalso; apply HNC1; ColR.
      }
    destruct HE as [HNC2|[HNC2|[HNC2 HNC3]]]; [..|clear HSQ HNCE].
    - apply (HSQ K M A B C D a b c d); Col; Between.
      destruct HNCE as [HNC3|HF]; [Col|intro HC; apply HF; Col].
    - assert (ER1 : EqR A B C D D C B A).
        {
        destruct (circumscribed_rectangle__rectangle b K a M A B C D)
          as [HAB [HBC HRect]]; [Col|split; [exists K; split; Between|right; split; assumption]|].
        destruct (EqR_perm A B C D); spliter; auto.
        }
      assert (ER2 : EqR b a d c a b c d).
        {
        apply EqR_sym; assert (HRect : Rectangle a b c d)
          by (destruct HR3; apply rect_comm2; assumption).
        cut (b <> c); [intro; destruct (EqR_perm a b c d); spliter; auto|].
        intro; treat_equalities; apply degenerated_rect_eq in HRect.
        treat_equalities; destruct HR3 as [_ HF]; Col.
        }
      apply EqR_trans with D C B A; [assumption|].
      apply EqR_trans with b a d c; [|assumption].
      apply (HSQ K M D C B A b a d c); Col.
      + destruct HNCE as [HF|HNC3]; [intro; apply HF; Col|Col].
      + apply FCR_ABCDK_BACKD; assumption.
    - assert (HE : Bet A M D /\ Bet B K C); [|destruct HE as [HB2 HB3]].
        {
        apply circumscribed_rectangle__bet with b a;
        [left;assumption|exists K; split; Between|assumption..].
        }
      assert (ER : EqR c b a d a b c d).
        {
        assert (HRect : Rectangle a b c d)
          by (destruct HR3; apply rect_comm2; assumption).
        apply EqR_sym.
        cut (b <> c); [intro; destruct (EqR_perm a b c d); spliter; auto|].
        intro; treat_equalities; apply degenerated_rect_eq in HRect.
        treat_equalities; destruct HR3 as [_ HF]; apply HNC1; Col.
        }
      apply EqR_trans with c b a d; [clear ER|assumption].
      destruct HR3 as [HR3 HC3].
      assert (HbK : b <> K) by (intro; treat_equalities; apply HNC3; Col).
      assert (HKa : K <> a) by (intro; treat_equalities; apply HNC2; Col).
      assert (Hab : b <> a) by (intro; treat_equalities; apply HNC1; Col).
      assert (Had : a <> d)
        by (intro; treat_equalities; apply degenerated_rect_eq in HR3;
            treat_equalities; apply HNC1; Col).
      destruct (rect_cut_exists b a d c K) as [N [HB4 [HR4 HR5]]]; auto.
      assert (Hcd : c <> d)
        by (intro; treat_equalities; apply rect_permut, degenerated_rect_eq in HR3;
            treat_equalities; auto).
      assert (HF1 : First_circumscribed_rectangle K b M c N)
        by (split; [apply rect_comm2; assumption|apply col3 with c d; Col]).
      assert (HF2 : First_circumscribed_rectangle K a M d N)
        by (split; [assumption|apply col3 with c d; Col]).
      apply (B5_8 A B K M C D c b K N a d); Between.
      + apply EqR_trans with M K B A.
          {
          destruct (FCR_ncol__diffs K M b A B) as [_ [HAB' HBK]]; auto.
          destruct HR1 as [HR1 _].
          destruct (EqR_perm A B K M);
            [auto|auto|apply rect_permut, rect_permut; assumption|spliter; assumption].
          }
        apply EqR_trans with K b c N.
        * apply (EqT_FCR__EqR M K b K b M); [intro; treat_equalities; auto..|
                                              apply B6_1; Col| |assumption].
          apply FCR_ABCDK_BACKD; assumption.
        * destruct (EqR_perm K b c N);
            [intro; subst; auto| |apply rect_comm2; assumption|spliter; assumption].
          intro; treat_equalities.
          apply rect_permut, rect_permut, degenerated_rect_eq in HR4.
          treat_equalities; apply HNC3; destruct HF1; Col.
      + apply EqR_trans with K a d N.
        * apply (EqT_FCR__EqR M K a K a M); [intro; treat_equalities; auto..|
                                              apply B6_1; Col| |assumption].
          apply FCR_ABCDK_BACKD; assumption.
        * destruct (EqR_perm K a d N); [..|spliter; assumption]; auto.
    }
  intros J K L M A B C D a b c d HNCE1 HNCE2 HR1 HR2 HConvex HJL HKM HR3 HR4.
  assert (HRP : A <> B /\ B <> C /\ Rectangle A B C D /\
                a <> b /\ b <> c /\ Rectangle a b c d).
    {
    destruct (circumscribed_rectangle__rectangle J K L M A B C D) as [HAB [HBC HRect1]];
      [assumption|split; [assumption|right; split; assumption]|].
    destruct (circumscribed_rectangle__rectangle J K L M a b c d) as [Hab [Hbc HRect2]];
      [assumption|split; [assumption|left; split; assumption]|].
    repeat (split; [assumption|]); assumption.
    }
  assert (HE :   Col J L K \/   Col J L M \/   Col K M J \/   Col K M L \/
               ~ Col J L K /\ ~ Col J L M /\ ~ Col K M J /\ ~ Col K M L).
    {
    destruct (col_dec J L K) as [HC|HNC1]; [tauto|].
    destruct (col_dec J L M) as [HC|HNC2]; [tauto|].
    destruct (col_dec K M J) as [HC|HNC3]; [tauto|].
    destruct (col_dec K M L) as [HC|HNC4]; tauto.
    }
  destruct HRP as [HAB [HBC [HRect1 [Hab [Hbc HRect2]]]]].
  destruct HE as [HC|[HC|[HC|[HC|HNCs]]]]; [..|clear HNCE1 HNCE2 HDQOC].
  - assert (HNC : ~ Col J L M) by (elim HNCE1; tauto).
    apply (HDQOC J K L M); assumption.
  - assert (HNC : ~ Col J L K) by (elim HNCE1; tauto).
    apply EqR_trans with B A D C; [|apply EqR_trans with d c b a].
    + destruct (EqR_perm A B C D) as [_ [_ [_ [_ [_ [_ [_ H]]]]]]]; assumption.
    + apply (HDQOC J M L K); Col; [apply FCR_ABCDK_BACKD; assumption..|].
      destruct HConvex as [I [HB1 HB2]]; exists I; split; Between.
    + apply EqR_sym.
      destruct (EqR_perm a b c d) as [_ [_ [_ [_ [_ [H _]]]]]]; assumption.
  - assert (HNC : ~ Col K M L) by (elim HNCE2; tauto).
    apply EqR_sym, (HDQOC K J M L); Col.
    destruct HConvex as [I [HB1 HB2]]; exists I; split; Between.
  - assert (HNC : ~ Col K M J) by (elim HNCE2; tauto).
    apply (EqR_trans _ _ _ _ D C B A); [|apply EqR_trans with b a d c].
    + destruct (EqR_perm A B C D) as [_ [_ [_ [_ [_ [H _]]]]]]; assumption.
    + apply EqR_sym.
      apply (HDQOC K L M J); Col; [apply FCR_ABCDK_BACKD; assumption..|].
      destruct HConvex as [I [HB1 HB2]]; exists I; split; Between.
    + apply EqR_sym.
      destruct (EqR_perm a b c d) as [_ [_ [_ [_ [_ [_ [_ H]]]]]]]; assumption.
  - destruct HNCs as [HNC1 [HNC2 [HNC3 HNC4]]].
    inversion HConvex as [I [HB1 HB2]].
    assert (HIJ : I <> J) by (intro; treat_equalities; apply HNC3; Col).
    assert (HIK : I <> K) by (intro; treat_equalities; apply HNC1; Col).
    assert (HIL : I <> L) by (intro; treat_equalities; apply HNC4; Col).
    assert (HIM : I <> M) by (intro; treat_equalities; apply HNC2; Col).
    destruct (circumscribed_rectangle__bet J K L M a b c d) as [_ HB3];
      [left; assumption|assumption..|].
    destruct (circumscribed_rectangle__bet K J M L A B C D) as [_ HB4];
      [left; assumption|exists I; split; Between|assumption..|].
    destruct (FCR_ncol__diffs J L K a b) as [HLa _]; auto.
    destruct (FCR_ncol__diffs J L M d c) as [HLd [Hdc _]]; auto.
    destruct (FCR_ncol__diffs K M J A B) as [HMA [_ HBK]]; auto.
    destruct (FCR_ncol__diffs K M L D C) as [HMD [HDC HCK]]; auto.
    destruct HR1 as [HR1 HC1]; destruct HR2 as [HR2 HC2].
    destruct HR3 as [HR3 HC3]; destruct HR4 as [HR4 HC4].
    destruct (rect_cut_exists J L a b I) as [Iab [HB5 [HR5 HR6]]]; auto.
    destruct (rect_cut_exists J L d c I) as [Icd [HB6 [HR7 HR8]]]; auto.
    destruct (rect_cut_exists K M A B I) as [IAB [HB7 [HR9 HR10]]]; auto.
    destruct (rect_cut_exists K M D C I) as [ICD [HB8 [HR11 HR12]]]; auto.
    assert (HCol : Col b Iab a /\ Col c Icd d /\ Col B IAB A /\ Col C ICD D)
      by (repeat split; Col).
    destruct HCol as [HCol1 [HCol2 [HCol3 HCol4]]].
    assert (HNC5 : ~ Col I J K) by (intro; apply HNC1; ColR).
    assert (HNC6 : ~ Col I J M) by (intro; apply HNC2; ColR).
    assert (HNC7 : ~ Col I L K) by (intro; apply HNC1; ColR).
    assert (HNC8 : ~ Col I L M) by (intro; apply HNC2; ColR).
    assert (HJ : EqR A M K B c Icd Iab b).
      {
      apply (split_triangle__EqR J K M I A B IAB b c Iab Icd); auto.
      - split; [apply rect_comm2; assumption|apply col3 with B A; Col].
      - split; [assumption|apply col3 with B A; Col].
      - split; [apply rect_comm2; assumption|apply col3 with b a; Col].
      - split; [apply rect_comm2; assumption|apply col3 with c d; Col].
      }
    assert (HL : EqR D M K C d Icd Iab a).
      {
      apply (split_triangle__EqR L K M I D C ICD a d Iab Icd); auto.
      - split; [apply rect_comm2; assumption|apply col3 with C D; Col].
      - split; [assumption|apply col3 with C D; Col].
      - split; [assumption|apply col3 with b a; Col].
      - split; [assumption|apply col3 with c d; Col].
      }
    assert (HB9 : Bet Iab I Icd).
      {
      apply (Bet_Rect2__Bet Iab b J I c Icd); [Between| |].
      - apply rect_permut, rect_permut; assumption.
      - apply rect_comm2; assumption.
      }
    assert (ER5 : EqR c b a d a b c d)
      by (apply EqR_sym; destruct (EqR_perm a b c d); [..|spliter]; auto).
    apply EqR_trans with c b a d; [clear ER5|assumption].
    apply (B5_8 A B K M C D c b Iab Icd a d); Between.
    + assert (HR : Rectangle c Icd Iab b).
        {
        apply (extent_rect c Icd I J Iab b); Between.
        apply rect_permut, rect_permut, rect_comm2; assumption.
        }
      apply EqR_trans with A M K B.
        {
        destruct (EqR_perm A B K M); [auto|auto|apply rect_permut, rect_permut; assumption|].
        spliter; assumption.
        }
      apply EqR_trans with c Icd Iab b; [assumption|].
      destruct (EqR_perm c Icd Iab b); [..|assumption|spliter; assumption].
      * intro; treat_equalities.
        apply rect_permut, degenerated_rect_eq in HR7; auto.
      * intro; treat_equalities.
        apply degenerated_rect_eq in HR5; apply degenerated_rect_eq in HR7.
        treat_equalities; auto.
    + assert (HR : Rectangle d Icd Iab a).
        {
        apply (extent_rect d Icd I L Iab a); Between.
        - apply rect_permut, rect_permut; assumption.
        - apply rect_comm2; assumption.
        }
      apply EqR_trans with D M K C.
        {
        destruct (EqR_perm M K C D);
          [intro; subst; auto|intro; subst; auto|apply rect_comm2; assumption|].
        spliter; assumption.
        }
      apply EqR_trans with d Icd Iab a; [assumption|].
      destruct (EqR_perm d Icd Iab a); [..|assumption|spliter; assumption].
      * intro; treat_equalities.
        apply rect_permut, degenerated_rect_eq in HR8; auto.
      * intro; treat_equalities.
        apply rect_permut, rect_permut, degenerated_rect_eq in HR6; auto.
  }
destruct HR1 as [_ [[HR1 HR2]|[HR1 HR2]]];
destruct HR3 as [_ [[HR3 HR4]|[HR3 HR4]]].
- apply (HSQ J K L M); assumption.
- apply (HDQ K J M L); assumption.
- apply (HDQ J K L M); assumption.
- apply (HSQ K J M L); assumption.
Qed.

Definition EqQ J K L M j k l m :=
  exists A B C D a b c d,
    circumscribed_rectangle J K L M A B C D /\
    circumscribed_rectangle j k l m a b c d /\
    EqR A B C D a b c d.

Lemma EqQ_sym J K L M j k l m :
  EqQ J K L M j k l m <-> EqQ j k l m J K L M.
Proof.
split.
- intro HEqQ.
  destruct HEqQ as [A [B [ C [D [a [b [c [d H]]]]]]]]; spliter.
  exists a, b, c, d, A, B, C, D; do 2 (split; auto); apply EqR_sym; auto.
- intro HEqQ.
  destruct HEqQ as [A [B [ C [D [a [b [c [d H]]]]]]]]; spliter.
  exists a, b, c, d, A, B, C, D; do 2 (split; auto); apply EqR_sym; auto.
Qed.

Lemma convex_ncol2_FCR2__rect A B C D F G I H :
  Convex A B C D -> ~ Col A B C -> ~ Col A C D ->
  First_circumscribed_rectangle A C D F G ->
  First_circumscribed_rectangle A C B I H ->
  I <> H /\ H <> G /\ Rectangle I H G F.
Proof.
intros HCV HNC1 HNC2 H1 H2.
destruct HCV as [E [HB1 HB2]].
assert (HCV : Convex A B C D) by (exists E; auto).
apply not_col_distincts in HNC1; apply not_col_distincts in HNC2.
destruct HNC1 as [HNC1 [HNAC [HNBC HNAB]]]; destruct HNC2 as [HNC2 [_ [HNCD HNAD]]].
assert (HR1 : Rectangle A C F G) by (destruct H1; auto).
assert (HR2 : Rectangle A C I H) by (destruct H2; auto).
assert (HC1 : Col D F G) by (destruct H1; auto).
assert (HC2 : Col B I H) by (destruct H2; auto).
assert (HNIH :  I <> H)
  by (intro; treat_equalities; apply rect_permut in HR2; apply degenerated_rect_eq in HR2; auto).
assert (HNCF : C <> F) by (destruct (FCR_ncol__diffs A C D F G); Col).
assert (HNCI : C <> I) by (destruct (FCR_ncol__diffs A C B I H); Col).
assert (HNCol : ~ Col G A C) by (destruct (FCR_ncol__ncol A C D F G); Col).
assert (HNCol2 : ~ Col A C I) by (destruct (FCR_ncol__ncol A C B I H); Col).
assert (HPS1 : Parallelogram_strict F G A C).
  {
  do 2 (apply rect_permut in HR1); apply Rectangle_Parallelogram in HR1.
  apply ncol234_plg__plgs; auto.
  }
assert (HPS2 : Parallelogram_strict H A C I).
  {
  do 3 (apply rect_permut in HR2) ;apply Rectangle_Parallelogram in HR2.
  apply ncol234_plg__plgs; auto.
  }
apply plgs_permut in HPS2.
assert (HP : Parallelogram F G H I) by (apply plgs_pseudo_trans with A C; auto).
assert (HPerp1 : Per I C A) by (apply rect_per2 in HR2; Perp).
assert (HPerp2 : Per F C A) by (apply rect_per2 in HR1; Perp).
assert (HCop1 : Coplanar A F I C).
  {
  apply coplanar_pseudo_trans with A C D; Cop.
  - elim (eq_dec_points D F); [intro; treat_equalities; Cop|intro HDF].
    cut (Par A C D F); [Cop|destruct H1 as [_ H1]].
    apply par_col4__par with A C F G; Col.
    apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
  - keep HNC1 HNAC HNBC HNAB HNC2 HNCD HNAD HCV H2 HR2 HC2 HNIH HNCI HNCol2 HPS2 HPerp1. apply coplanar_pseudo_trans with A C B; Col; Cop.
    + destruct HCV as [M []].
      elim (eq_dec_points B M); [intro; treat_equalities; Cop|intro HBM].
      apply col_cop__cop with M; Col; Cop.
    + elim (eq_dec_points B I); [intro; treat_equalities; Cop|intro HBI].
      cut (Par A C B I); [Cop|destruct H2 as [_ H2]].
      apply par_col4__par with A C H I; Col.
      apply Rectangle_Parallelogram, plg_par in HR2; spliter; Par.
  }
assert (HC3 : Col F I C) by (apply cop_per2__col with A; auto).
assert (HPerp3 : Per G F C) by (apply rect_per3 in HR1; Perp).
assert (HPerp4 : Per G F I) by (apply per_col with C; Col).
assert (HR3 : Rectangle F G H I) by (apply parallelogram_to_plg in HP; apply plg_per_rect; Perp).
apply rect_comm2 in HR3; do 2 (apply rect_permut in HR3).
assert (HNBD : B <> D) by (intro; treat_equalities; apply bet_col in HB1; Col).
assert (HNGH :  H <> G).
  {
  intro; treat_equalities.
  apply degenerated_rect_eq in HR3; treat_equalities.
  assert (HCol : Col H B D) by (apply col_transitivity_1 with I; Col).
  assert (HCol2 : Col I B D) by (apply col_transitivity_1 with H; Col).
  assert (HPar : Par A C I H)
    by (apply Rectangle_Parallelogram in HR1; apply plg_par_1 in HR1; auto).
  assert (HPar2 : Par A C B D).
    {
    elim (eq_dec_points H B).
    +intro; apply par_col_par with I; Col; treat_equalities; Par.
    +intro.
     elim (eq_dec_points I B).
     -intro; treat_equalities; apply par_col_par with H; Col.
     -intro.
      apply par_col_par with I; Col.
      apply par_right_comm.
      apply par_col_par with H; Col.
    }
  apply bet_col in HB1; apply bet_col in HB2.
  assert (HCol3 : Col A C B) by (apply not_strict_par1 with D E; Col).
  Col.
  }
auto.
Qed.

Lemma EqQ_abcd_bcda_adcb A B C D :
  Convex A B C D -> ~ Col A B C \/ ~ Col A C D ->
  EqQ A B C D B C D A /\ EqQ A B C D A D C B.
Proof.
intros HCV HNC.
assert (HCV2 : Convex B C D A) by (destruct HCV as [E []]; exists E; Between).
assert (HCV3 : Convex A D C B) by (destruct HCV as [E []]; exists E; Between).
assert (HAC : A <> C) by (destruct HNC; assert_diffs; auto).
destruct (col_dec A B C) as [HC1|HNC1]; [|destruct (col_dec A C D) as [HC2|HNC2]].
- destruct HNC as [|HNC2]; [contradiction|].
  destruct (Circumscribed_rectangle_exists A C D) as [F [G HF]]; [assert_diffs; auto|].
  destruct (FCR_ncol__diffs A C D F G) as [HCF [HFG HGA]]; Col.
  assert (HB : First_circumscribed_rectangle A C B C A) by (apply FCR_triv; Col; assert_diffs; auto).
  assert (HR : Rectangle C A G F) by (destruct HF; apply rect_comm2; auto).
  split.
  + exists C, A, G, F, A, C, F, G; split; [split; auto|].
    split; [split; auto; right; split; apply FCR_ABCDK_BACKD; auto|].
    apply EqR_perm; auto.
  + exists C, A, G, F, F, G, A, C; split; [split; auto|].
    split; [split; auto|apply EqR_perm; auto].
- destruct (Circumscribed_rectangle_exists A C B) as [F [G HF]]; [assert_diffs; auto|].
  destruct (FCR_ncol__diffs A C B F G) as [HCF [HFG HGA]]; Col.
  assert (HD : First_circumscribed_rectangle A C D C A) by (apply FCR_triv; Col; assert_diffs; auto).
  assert (HR : Rectangle F G A C) by (destruct HF; do 2 apply rect_permut; auto).
  split.
  + exists F, G, A, C, G, F, C, A; split; [split; auto|].
    split; [split; auto; right; split; apply FCR_ABCDK_BACKD; auto|].
    apply EqR_perm; auto.
  + exists F, G, A, C, C, A, G, F; split; [split; auto|].
    split; [split; auto|apply EqR_perm; auto].
- destruct (Circumscribed_rectangle_exists A C D) as [F [G H1]]; [assert_diffs; auto|].
  destruct (Circumscribed_rectangle_exists A C B) as [I [H H2]]; [assert_diffs; auto|].
  destruct (convex_ncol2_FCR2__rect A B C D F G I H) as [HIH [HHG HR]]; auto.
  split.
  + exists I, H, G, F, H, I, F, G; split; [split; auto|].
    split; [split; auto; right; split; apply FCR_ABCDK_BACKD; auto|].
    apply EqR_perm; auto.
  + exists I, H, G, F, F, G, H, I; split; [split; auto|].
    split; [split; auto|apply EqR_perm; auto].
Qed.

Lemma EqQ_abcd_bcda A B C D :
  Convex A B C D -> ~ Col A B C \/ ~ Col A C D -> EqQ A B C D B C D A.
Proof. intros; apply EqQ_abcd_bcda_adcb; auto. Qed.

Lemma EqQ_abcd_adcb A B C D :
  Convex A B C D -> ~ Col A B C \/ ~ Col A C D -> EqQ A B C D A D C B.
Proof. intros; apply EqQ_abcd_bcda_adcb; auto. Qed.
Lemma EqQ_trans A B C D E F G H I J K L :
  EqQ A B C D E F G H ->
  EqQ E F G H I J K L ->
  EqQ A B C D I J K L.
Proof.
intros [a [b [c [d [e [f [g [h [HR1 [HR2 ER1]]]]]]]]]].
intros [m [n [o [p [i [j [k [l [HR3 [HR4 ER2]]]]]]]]]].
exists a, b, c, d, i, j, k, l; do 2 (split; [assumption|]).
apply EqR_trans with e f g h; auto; apply EqR_trans with m n o p; auto.
destruct (col_dec E F G) as [HC1|]; [destruct (col_dec E G H) as [HC2|]|].
- assert (Hd : e <> f /\ h <> g).
    {
    destruct ER1 as [_ [_ [_ [Hef [_ [HR _]]]]]]; split; [auto|].
    apply Rectangle_Parallelogram, plg_cong in HR; spliter.
    intro; treat_equalities; auto.
    }
  destruct Hd as [Hef Hhg].
  destruct HR2 as [HConvex [[HR2 HR5]|[HR2 HR5]]].
  + destruct (FCR_Col__eq' E G F e f); Col; treat_equalities.
    destruct (FCR_Col__eq' E G H h g); Col; treat_equalities.
    destruct ER1; spliter; exfalso; auto.
  + assert (HC3 : Col E F H /\ Col F G H).
      {
      destruct (eq_dec_points E G) as [|]; [treat_equalities|split; ColR].
      destruct HConvex as [M []]; treat_equalities; split; Col.
      }
    destruct HC3 as [HC3 HC4].
    destruct (FCR_Col__eq' F H E e f); Col; treat_equalities.
    destruct (FCR_Col__eq' F H G h g); Col; treat_equalities.
    destruct ER1; spliter; exfalso; auto.
- apply circumscribed_rectangle_EqR with E F G H; [Col|assumption..].
- apply circumscribed_rectangle_EqR with E F G H; [Col|assumption..].
Qed.

Lemma EqQ_perm J K L M :
  Convex J K L M -> ~ Col J K M -> ~ Col J L M ->
  EqQ J K L M K L M J /\ EqQ J K L M L M J K /\
  EqQ J K L M M J K L /\ EqQ J K L M J M L K /\
  EqQ J K L M M L K J /\ EqQ J K L M L K J M /\
  EqQ J K L M K J M L.
Proof.
intros HC1 HNC1 HNC2.
assert (HE : exists E, Bet J E L /\ Bet K E M) by auto; destruct HE as [E [HB1 HB2]].
assert (HC2 : Convex K L M J) by (exists E; split; Between).
assert (HC3 : Convex L M J K) by (exists E; split; Between).
assert (HC4 : Convex J M L K) by (exists E; split; Between).
split; [apply EqQ_abcd_bcda; auto|].
split; [apply EqQ_trans with K L M J; auto; apply EqQ_abcd_bcda; Col|].
split.
apply EqQ_trans with K L M J; auto; [apply EqQ_abcd_bcda; auto|].
apply EqQ_trans with L M J K; auto; apply EqQ_abcd_bcda; Col.
split; [apply EqQ_abcd_adcb; auto|].
split.
apply EqQ_trans with J M L K; auto; [apply EqQ_abcd_adcb; auto|]; apply EqQ_abcd_bcda; Col.
split.
apply EqQ_trans with K L M J; auto; [apply EqQ_abcd_bcda; auto|].
apply EqQ_trans with L M J K; auto; [apply EqQ_abcd_bcda; Col|]; apply EqQ_abcd_adcb; Col.
apply EqQ_trans with K L M J; auto; [apply EqQ_abcd_bcda; Col|]; apply EqQ_abcd_adcb; Col.
Qed.

(* 7.4 *)
Lemma rect_mid2__rect A B C D M N :
  A <> B -> B <> C -> Rectangle A B C D ->
  Midpoint M B C -> Midpoint N A D -> Rectangle A B M N.
Proof.
intros HAB HBC HR HM1 HM2.
assert (HC : Cong B C A D)
  by (apply Rectangle_Parallelogram, plg_cong in HR; spliter; Cong).
assert (HAD : A <> D) by (intro; treat_equalities; auto).
apply plg_per_rect1.
- apply parallelogram_to_plg; do 3 apply plg_permut.
  apply plg_out_plg with C D.
  + apply plg_permut, Rectangle_Parallelogram; auto.
  + repeat split; [intro; treat_equalities; auto..|right; Between].
  + repeat split; [intro; treat_equalities; auto..|right; Between].
  + apply cong_cong_half_1 with C D; assumption.
- cut (Per D A B); [intro; apply l8_2, per_col with D; Col; Perp|].
  apply l8_2, rect_per1 with C; assumption.
Qed.

Lemma EqF_half A B C D M N :
  A <> B -> C <> D -> Midpoint M A B -> Midpoint N C D -> EqF A B C D A M C N.
Proof.
intros HAB HCD HM1 HM2.
destruct two_distinct_points as [O [X0 HOX0]].
destruct (perp_exists O O X0 HOX0) as [Y0 HP].
assert (HOY0 : O <> Y0) by (assert_diffs; auto).
destruct (segment_construction_3 O X0 A B) as [X [HO1 HC1]]; auto.
destruct (segment_construction_3 O Y0 C D) as [Y [HO2 HC2]]; auto.
destruct (midpoint_existence O X) as [X' HM3].
destruct (midpoint_existence O Y) as [Y' HM4].
assert (HOX : O <> X) by (assert_diffs; auto).
assert (HOY : O <> Y) by (assert_diffs; auto).
exists O, X, Y, O, X', Y'; split; [Cong|split; [Cong|split]].
- apply cong_cong_half_1 with X B; Cong.
- split; [apply cong_cong_half_1 with Y D; Cong|].
  exists X', Y'; split; [Cong|split; [|split; [Cong|split; [|split]]]].
  + split; [auto|split; [intro; treat_equalities; auto|right; Between]].
  + split; [auto|split; [intro; treat_equalities; auto|right; Between]].
  + apply l8_14_2_1b_bis; Col.
    apply perp_col4 with O X0 O Y0; Col; Perp.
  + apply triangle_mid_par with O; [|Midpoint..].
    intro; treat_equalities; apply out_col in HO1; apply out_col in HO2.
    destruct (perp_not_col2 _ _ _ _ HP) as [HNC|HNC]; apply HNC; ColR.
Qed.

Lemma rectangle_cut_in_halves A B C D P Q a b c d p q:
  Midpoint P A B -> Midpoint p a d ->
  Midpoint Q C D -> Midpoint q b c ->
  EqR A B C D a b c d ->
  EqR P Q C B a b q p.
Proof.
intros HM1 HM2 HM3 HM4 HR.
destruct (EqR_diffs A B C D a b c d HR) as [HAB [HBC [Hab Hbc]]].
assert (HR1 : Rectangle A B C D) by (destruct HR as [_ [_ [HR1 _]]]; auto).
assert (HR2 : Rectangle a b c d) by (destruct HR as [_ [_ [_ [_ [_ [HR2 _]]]]]]; auto).
assert (HR3 : Rectangle P Q C B).
  {
  do 2 apply rect_permut; apply (rect_mid2__rect C B A D P Q); Midpoint.
  apply rect_comm2, rect_permut; assumption.
  }
assert (HR4 : Rectangle a b q p) by (apply (rect_mid2__rect a b c d); auto).
(* This simplifies the paper's proof of Lemma 7.4, which places the rectangles
   as in Fig. 13 and shows that the intersection of the two midlines lies on
   the diagonal.  By Lemma 5.2 (B5_2_1), it is enough to show
   PQ : ab = bq : QC, that is BC : ab = (bc/2) : (AB/2), which follows from
   AB : ab = bc : BC and x : y = (x/2) : (y/2) (EqF_half). *)
apply B5_2_1; [assumption..|].
apply B5_2_1 in HR; [|assumption..].
apply interchange_theorem, EqF_sym, EqF_abcd_badc in HR.
apply EqF_cong with B C a b b q Q C; Cong.
- apply EqF_trans with b c A B; [assumption|].
  apply EqF_cong with b c A B b q A P; [apply EqF_half; auto|Cong..].
  cut (Cong A P C Q); [Cong|].
  apply cong_cong_half_1 with B D; [assumption..|].
  apply Rectangle_Parallelogram, plg_cong in HR1; spliter; Cong.
- apply Rectangle_Parallelogram, plg_cong in HR3; spliter; Cong.
Qed.

Lemma EqT_Convex A B C D E F G H:
  Convex A C B D -> ~ Col A B C -> ~ Col A B D ->
  First_circumscribed_rectangle A B C E F ->
  First_circumscribed_rectangle A B D H G ->
  Bet G A F /\ Bet H B E.
Proof.
intros HCV HNC1 HNC2 HF1 HF2.
destruct (circumscribed_rectangle__bet A C B D E F G H); [left; Col|assumption..|].
split; Between.
Qed.

(* 7.5 but not used *)
Lemma quadrilateral_cut_in_halves A B C D P Q S T :
  Convex S P T Q ->
  First_circumscribed_rectangle P Q S A D ->
  First_circumscribed_rectangle P Q T B C ->
  EqT P Q S P Q T ->
  EqR P Q A D P Q B C.
Proof.
intros HCV HF1 HF2 HEQT.
assert (HPQ : P <> Q)
  by (destruct (EqT_not_col P Q S P Q T HEQT); assert_diffs; auto).
apply (EqT_FCR__EqR P Q S P Q T); assumption.
Qed.

(* 7.6 *)
Lemma EqR_rect2__cong A C K L N M :
  A <> C -> C <> K -> C <> N ->
  Rectangle A C K L -> Rectangle A C N M -> EqR A C K L A C N M ->
  Cong L A A M.
Proof.
intros HAC HCK HCN HR1 HR2 HEQR.
assert (HKL : K <> L).
  {
  intro; treat_equalities; apply rect_permut in HR1.
  apply degenerated_rect_eq in HR1; auto.
  }
assert (HAL : A <> L).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR1.
  apply degenerated_rect_eq in HR1; auto.
  }
cut (EqR  K L A C N M A C).
- intro HEQR4; apply B5_5 in HEQR4; Cong.
  + do 2 apply rect_permut; auto.
  + do 2 apply rect_permut; auto.
  + cut (Cong A C K L /\ Cong A C N M); [intros []; eCong|].
    apply Rectangle_Parallelogram in HR1, HR2.
    apply plg_cong in HR1, HR2; spliter; Cong.
- apply EqR_trans with A C K L; [|eapply EqR_trans; eauto];
  apply EqR_perm; auto; do 2 apply rect_permut; auto.
Qed.

Lemma halves_of_equals A B C D a b c d :
  TS A C B D -> TS a c b d ->
  EqT A C B A C D -> EqT a c b a c d ->
  EqQ A B C D a b c d ->
  EqT A C B a c b.
Proof.
intros HTS1 HTS2 HE1 HE2 HEQ.
assert (HNC1 : ~ Col A C B /\ ~ Col A C D) by (apply EqT_not_col; auto).
assert (HNC3 : ~ Col a c b /\ ~ Col a c d) by (apply EqT_not_col; auto).
destruct HNC1 as [HNC1 HNC2].
destruct HNC3 as [HNC3 HNC4].
destruct HEQ as [G [H [I [J [g [h [i [j [HCR1 [HCR2 HEQR1]]]]]]]]]].
destruct HE1 as [K [L [N [M [HF1 [HF2 HEQR2]]]]]].
destruct HE2 as [k [l [n [m [HF3 [HF4 HEQR3]]]]]].
cut (EqR M L K N l k n m).
- assert (HP : A <> C /\ C <> K /\ A <> C /\ C <> N) by (apply EqR_diffs with L M; auto); spliter.
  assert (HP : a <> c /\ c <> k /\ a <> c /\ c <> n) by (apply EqR_diffs with l m; auto); spliter.
  assert (HR1 : Rectangle A C K L) by (destruct HF1; auto).
  assert (HR2 : Rectangle A C N M) by (destruct HF2; auto).
  assert (HR3 : Rectangle a c k l) by (destruct HF3; auto).
  assert (HR4 : Rectangle a c n m) by (destruct HF4; auto).
  assert (HCV1 : Convex A B C D) by (destruct HCR1; spliter; auto).
  assert (HCV2 : Convex a b c d) by (destruct HCR2; spliter; auto).
  assert (HB : Bet M A L /\ Bet N C K) by (apply EqT_Convex with B D; auto).
  assert (HB2 : Bet m a l /\ Bet n c k) by (apply EqT_Convex with b d; auto); spliter.
  assert (HCong1 : Cong N C C K) by (apply B5_5 in HEQR2; auto; Cong).
  assert (HM1 : Midpoint C K N) by (unfold Midpoint; split; Between; Cong).
  assert (HCong2 : Cong k c c n) by (apply B5_5 in HEQR3; auto; Cong).
  assert (HM2 : Midpoint c k n) by (unfold Midpoint; Between).
  assert (HCong3 : Cong L A A M) by (apply (EqR_rect2__cong A C K L N M); auto).
  assert (HM3 : Midpoint A M L) by (unfold Midpoint; split; Between; Cong).
  assert (HCong4 : Cong l a a m) by (apply (EqR_rect2__cong a c k l n m); auto).
  assert (HM4 : Midpoint a l m) by (unfold Midpoint; split; Between; Cong).
  intro HEQR4; assert (HEQR5 : EqR A C K L l k c a)
    by (apply rectangle_cut_in_halves with M N n m; auto).
  exists K, L, k, l; do 2 (split; auto).
  assert (HNlk : l <> k)
    by (intro; treat_equalities; apply rect_permut in HR3; apply degenerated_rect_eq in HR3; auto).
  assert (HR5 : Rectangle l k c a) by (apply rect_comm2 in HR3; do 2 (apply rect_permut in HR3); auto).
  apply EqR_trans with l k c a; auto.
  apply EqR_perm; auto.
- assert (HCR3 : circumscribed_rectangle A B C D K L M N)
    by (split; [destruct HCR1|]; auto).
  apply (circumscribed_rectangle_EqR _ _ _ _ G H I J) in HCR3; auto.
  assert (HCR4 : circumscribed_rectangle a b c d k l m n)
    by (split; [destruct HCR2|]; auto).
  apply (circumscribed_rectangle_EqR _ _ _ _ g h i j) in HCR4; auto.
  cut (EqR K L M N k l m n).
  + intro HE; apply EqR_trans with K L M N; [|eapply EqR_trans; eauto].
    * destruct HE as [HKL [HLM [HR _]]]; apply EqR_perm; auto.
      do 3 apply rect_permut; apply rect_comm2; auto.
    * destruct HE as [_ [_ [_ [HKL [HLM [HR _]]]]]]; apply EqR_perm; auto.
  + apply (EqR_trans _ _ _ _ G H I J); [apply EqR_sym; auto|].
    apply (EqR_trans _ _ _ _ g h i j); auto.
Qed.

(* 7.7 *)
Lemma paste3 A B C D M a b c d m :
  EqT A B C a b c -> EqT A B D a b d ->
  Bet C M D -> Bet A M B ->
  Bet c m d -> Bet a m b ->
  EqQ A C B D a c b d.
Proof.
intros HEQT1 HEQT2 HB1 HB2 HB3 HB4.
assert (HCV1 : Convex A C B D) by (exists M; auto).
assert (HVC2 : Convex a c b d) by (exists m; auto).
assert (HNC : ~ Col A B C /\ ~ Col a b c) by (apply EqT_not_col; auto).
assert (HNC0 : ~ Col A B D /\ ~ Col a b d) by (apply EqT_not_col; auto).
destruct HNC as [HNC1 HNC2]; destruct HNC0 as [HNC3 HNC4].
destruct HEQT1 as [G [H [g [h [HF1 [HF2 HEQR1]]]]]].
destruct HEQT2 as [J [I [j [i [HF3 [HF4 HEQR2]]]]]].
assert (HP : A <> B /\ B <> G /\ a <> b /\ b <> g) by (apply EqR_diffs with H h; auto); spliter.
assert (HP : A <> B /\ B <> J /\ a <> b /\ b <> j) by (apply EqR_diffs with I i; auto); spliter.
assert (HR1 : Rectangle A B G H) by (destruct HF1; auto).
assert (HR2 : Rectangle A B J I) by (destruct HF3; auto).
assert (HR3 : Rectangle a b g h) by (destruct HF2; auto).
assert (HR4 : Rectangle a b j i) by (destruct HF4; auto).
assert (HNGH : G <> H)
  by (intro; treat_equalities; apply rect_permut in HR1; apply degenerated_rect_eq in HR1; auto).
assert (HNAH : H <> A).
intro; treat_equalities; do 2 (apply rect_permut in HR1); apply degenerated_rect_eq in HR1; auto.
assert (HNAI : A <> I).
intro; treat_equalities; do 2 (apply rect_permut in HR2); apply degenerated_rect_eq in HR2; auto.
assert (HR5 : Rectangle G H A B) by (do 2 (apply rect_permut); auto).
assert (HR6 : Rectangle B A I J) by (apply rect_comm2; auto).
assert (HEQR3 : EqR G H A B g h a b).
  {
  apply EqR_trans with A B G H; [apply EqR_perm; auto|].
  apply EqR_trans with a b g h; [auto|apply EqR_perm; auto].
  }
assert (HEQR4 : EqR B A I J b a i j).
apply EqR_trans with A B J I; [apply EqR_perm; auto|].
apply EqR_trans with a b j i; [auto|apply EqR_perm; auto].

assert (HB5 : Bet I A H /\ Bet J B G) by (apply EqT_Convex with C D; auto).
assert (HB6 : Bet i a h /\ Bet j b g) by (apply EqT_Convex with c d; auto); spliter.
assert (HEQR5 : EqR G H I J g h i j) by (apply B5_8 with A B a b; Between).
exists G, H, I, J, g, h, i, j; split; split; auto; split; auto.
Qed.

Lemma EqR__EqQ A B C D a b c d :
  EqR A B C D a b c d -> EqQ A B C D a b c d.
Proof.
intro HEQR.
assert (HP := HEQR); destruct HP as [HAB [HBC [HR1 [Hab [Hbc [HR2 _]]]]]].
assert (HT1 : EqT A B D a b d)
  by (exists C, D, c, d; split; [split; [auto|Col]|split; [split; [auto|Col]|auto]]).
assert (HT2 : EqT C D B c d b).
  {
  exists A, B, a, b; split; [split; [do 2 apply rect_permut; auto|Col]|].
  split; [split; [do 2 apply rect_permut; auto|Col]|].
  apply EqR_trans with A B C D; [apply EqR_sym, EqR_perm; auto|].
  apply EqR_trans with a b c d; [auto|apply EqR_perm; auto].
  }
destruct (EqT_not_col A B D a b d HT1) as [HNC1 HNC2].
destruct (EqT_not_col C D B c d b HT2) as [HNC3 HNC4].
assert (HT3 : EqT B D A b d a).
  {
  apply EqT_trans with A B D; [apply EqT_sym, B6_3; auto|].
  apply EqT_trans with a b d; [auto|apply B6_3; auto].
  }
assert (HT4 : EqT B D C b d c).
  {
  apply EqT_trans with C D B; [apply EqT_sym, B6_3; auto|].
  apply EqT_trans with c d b; [auto|apply B6_3; auto].
  }
destruct (plg_mid A B C D) as [M [HM1 HM2]]; [apply Rectangle_Parallelogram; auto|].
destruct (plg_mid a b c d) as [m [Hm1 Hm2]]; [apply Rectangle_Parallelogram; auto|].
assert (HQ : EqQ B A D C b a d c)
  by (apply paste3 with M m; Between).
assert (HNC5 : ~ Col B A C)
  by (intro; apply (per_not_col A B C); [auto|auto|apply rect_per2 with D; auto|Col]).
assert (HNC6 : ~ Col b a c)
  by (intro; apply (per_not_col a b c); [auto|auto|apply rect_per2 with d; auto|Col]).
apply EqQ_trans with B A D C.
  {
  apply EqQ_sym, EqQ_perm; Col.
  exists M; split; Between.
  }
apply EqQ_trans with b a d c; [auto|apply EqQ_perm; Col].
exists m; split; Between.
Qed.

Lemma B7_12 A B C D E F O :
  Bet A O C -> Bet B O D -> B <> O -> Cong B O O D ->
  Rectangle A C E F -> A <> C -> C <> E -> Col F D E ->
  EqQ A B C D A C E F.
Proof.
intros HB1 HB2 HBO HC HR HAC HCE HCol.
assert (HP : Parallelogram A C E F) by (apply Rectangle_Parallelogram; auto).
assert (HNC1 : ~ Col A C E) by (apply per_not_col; [auto|auto|apply (rect_per2 A C E F); auto]).
assert (HPS : Par_strict A C E F).
  {
  apply par_not_col_strict with E; [|Col|auto].
  destruct (plg_par A C E F) as [HPar _]; auto.
  }
assert (HEF : E <> F) by (intro; subst; destruct HPS as [_ HN]; apply HN; exists A; split; Col).
assert (HNC2 : ~ Col A C D) by (intro; destruct HPS as [_ HN]; apply HN; exists D; split; Col).
assert (HOD : O <> D) by (apply cong_diff with B O; auto).
assert (HNC3 : ~ Col A C B) by (intro; apply HNC2; ColR).
assert (HMid : Midpoint O B D) by (split; auto).
destruct (midpoint_existence A C) as [M HM].
destruct (symmetric_point_construction B M) as [B' HB'].
assert (HC3 : Cong_3 A C B C A B')
  by (repeat split; [Cong|apply l7_13 with M; Midpoint|apply l7_13 with M; Midpoint]).
assert (HNC4 : ~ Col C A B')
  by (intro; apply HNC3; apply (l4_13 C A B'); [auto|apply cong3_symmetry; auto]).
assert (HT1 : EqT A C B A C B')
  by (apply EqT_trans with C A B'; [apply Cong_3__EqT; auto|apply EqT_ABC_BAC; auto]).
assert (HT2 : EqT A C B' A C D).
  {
  destruct (eq_dec_points M O) as [|HMO].
  - subst; assert (B' = D) by (apply symmetric_point_uniqueness with B O; auto).
    subst; apply EqT_refl; auto.
  - assert (HB'D : B' <> D) by (intro; subst; apply HMO, (l7_17 D B); Midpoint).
    apply B5_12; [Col|].
    apply par_symmetry, par_col2_par with M O; [auto|apply triangle_mid_par with B; Midpoint|ColR..].
  }
assert (HT3 : EqT A C D A C E).
  {
  destruct (eq_dec_points D E); [subst; apply EqT_refl; auto|].
  apply B5_12; [auto|apply par_col2_par with E F; Col; apply par_strict_par; auto].
  }
assert (HNC5 : ~ Col E F A) by (intro; destruct HPS as [_ HN]; apply HN; exists A; split; Col).
assert (HT4 : EqT A C E A E F).
  {
  destruct (plg_cong A C E F HP) as [HC1 HC2].
  apply EqT_trans with E F A; [apply Cong_3__EqT; [auto|repeat split; Cong]|].
  destruct (B6_3 E F A) as [_ [_ [HT _]]]; auto.
  }
destruct (plg_mid A C E F HP) as [m [Hm1 Hm2]].
apply (paste3 A C B D O A E C F m).
- apply EqT_trans with A C B'; [auto|].
  apply EqT_trans with A C D; [auto|].
  apply EqT_trans with A C E; [auto|].
  destruct (B6_3 A C E) as [_ [_ [_ [HT _]]]]; auto.
- apply EqT_trans with A C E; auto.
- auto.
- auto.
- apply midpoint_bet; auto.
- apply midpoint_bet; auto.
Qed.

Lemma EqR_unit_exists U V A B C D :
  U <> V -> A <> B -> B <> C -> Rectangle A B C D ->
  exists X Y P Q R S, Cong P Q U V /\ Cong Q R X Y /\ EqR A B C D P Q R S.
Proof.
intros HUV HAB HBC HR.
destruct (Fourth_EqF_exists U V A B B C) as [X [Y HF]]; auto.
destruct (EqF_diffs U V A B B C X Y HF) as [_ [_ [_ HXY]]].
destruct (not_col_exists U V HUV) as [W HW].
destruct (ex_per_cong U V V W X Y) as [R [HPer [HCong _]]]; Col.
assert (HRV : R <> V) by (intro; treat_equalities; auto).
assert (HUR : U <> R) by (intro; treat_equalities; apply HUV, l8_8; Perp).
destruct (midpoint_existence U R) as [M HM].
destruct (symmetric_point_construction V M) as [S HS].
assert (HR2 : Rectangle U V R S)
  by (apply plg_per_rect2; [split; [left; auto|exists M; split; auto]|auto]).
exists X, Y, U, V, R, S; split; [Cong|split; [Cong|]].
apply EqR_sym, B5_2_1_2; auto.
apply EqF_cong with U V A B B C X Y; Cong.
Qed.

Lemma EqR_unit_unique U V A B C D P Q R S p q r s :
  Cong P Q U V -> Cong p q U V ->
  EqR A B C D P Q R S -> EqR A B C D p q r s ->
  Cong Q R q r.
Proof.
intros HPQ Hpq HEQR1 HEQR2.
assert (HEQR3 : EqR P Q R S p q r s) by (apply EqR_trans with A B C D; [apply EqR_sym|]; auto).
destruct HEQR3 as [HPQ' [HQR' [HR1 [_ [_ [HR2 _]]]]]].
apply (B5_5 P Q R S p q r s); [auto..|CongR|].
apply EqR_trans with A B C D; [apply EqR_sym|]; auto.
Qed.

Lemma EqR_unit_iff U V A B C D a b c d P Q R S p q r s :
  Cong P Q U V -> Cong p q U V ->
  EqR A B C D P Q R S -> EqR a b c d p q r s ->
  EqR A B C D a b c d <-> Cong Q R q r.
Proof.
intros HPQ Hpq HEQR1 HEQR2; split; intro H.
- apply EqR_unit_unique with U V A B C D P S p s; auto.
  apply EqR_trans with a b c d; auto.
- assert (HEQR3 : EqR P Q R S p q r s).
    {
    destruct HEQR1 as [_ [_ [_ [HPQ' [HQR' [HR1 _]]]]]].
    destruct HEQR2 as [_ [_ [_ [Hpq' [Hqr' [HR2 _]]]]]].
    apply (B5_5 P Q R S p q r s); auto; CongR.
    }
  apply EqR_trans with P Q R S; [auto|].
  apply EqR_trans with p q r s; [auto|apply EqR_sym; auto].
Qed.

Lemma EqR_halves A B C D a b c d M N m n :
  A <> B -> B <> C -> a <> b -> b <> c ->
  Rectangle A B C D -> Rectangle a b c d ->
  Midpoint M B C -> Midpoint N A D -> Midpoint m b c -> Midpoint n a d ->
  EqR A B C D a b c d <-> EqR A B M N a b m n.
Proof.
intros HAB HBC Hab Hbc HR Hr HM HN Hm Hn.
assert (HR1 : Rectangle A B M N) by (apply rect_mid2__rect with C D; auto).
assert (HR2 : Rectangle a b m n) by (apply rect_mid2__rect with c d; auto).
assert (HBM : B <> M) by (intro; treat_equalities; auto).
assert (Hbm : b <> m) by (intro; treat_equalities; auto).
split; intro HEQ.
- assert (HEQ' : EqR D A B C a b c d)
    by (apply EqR_trans with A B C D; [apply EqR_sym, EqR_perm|]; auto).
  assert (HEQ'' : EqR N M B A a b m n)
    by (apply (rectangle_cut_in_halves D A B C N M a b c d n m); [apply l7_2|..]; auto).
  apply EqR_trans with N M B A; [apply EqR_perm|]; auto.
- assert (HCD : C <> D /\ D <> A).
    {
    assert (Cong A B C D /\ Cong A D B C) by (apply Rectangle_Parallelogram, plg_cong in HR; spliter; split; Cong).
    spliter; split; intro; treat_equalities; auto.
    }
  assert (Hcd : c <> d /\ d <> a).
    {
    assert (Cong a b c d /\ Cong a d b c) by (apply Rectangle_Parallelogram, plg_cong in Hr; spliter; split; Cong).
    spliter; split; intro; treat_equalities; auto.
    }
  spliter.
  assert (HR3 : Rectangle N M C D).
    {
    do 2 apply rect_permut; apply rect_mid2__rect with A B; [auto|auto|do 2 apply rect_permut; auto|Midpoint|Midpoint].
    }
  assert (HR4 : Rectangle n m c d).
    {
    do 2 apply rect_permut; apply rect_mid2__rect with a b; [auto|auto|do 2 apply rect_permut; auto|Midpoint|Midpoint].
    }
  assert (HEQ1 : EqR A B M N N M C D).
    {
    apply (B5_5 A B M N N M C D); [auto..| |Cong].
    apply Rectangle_Parallelogram, plg_cong_1 in HR1; Cong.
    }
  assert (HEQ2 : EqR a b m n n m c d).
    {
    apply (B5_5 a b m n n m c d); [auto..| |Cong].
    apply Rectangle_Parallelogram, plg_cong_1 in HR2; Cong.
    }
  apply B5_8 with M N m n; Between.
  apply EqR_trans with A B M N; [apply EqR_sym; auto|].
  apply EqR_trans with a b m n; auto.
Qed.

Definition AreaT U V A B C X Y :=
  exists D K D' K' P Q R S,
    First_circumscribed_rectangle A B C D K /\
    Midpoint D' B D /\ Midpoint K' A K /\
    Cong P Q U V /\ Cong Q R X Y /\ EqR A B D' K' P Q R S.

Lemma AreaT_exists U V A B C :
  U <> V -> ~ Col A B C -> exists X Y, AreaT U V A B C X Y.
Proof.
intros HUV HNC.
destruct (Circumscribed_rectangle_exists A B C) as [D [K HF]]; [left; assert_diffs; auto|].
assert (HR : Rectangle A B D K) by (destruct HF; auto).
destruct (FCR_ncol__diffs A B C D K HNC HF) as [HBD _].
assert (HAB : A <> B) by (assert_diffs; auto).
destruct (midpoint_existence B D) as [D' HD'].
destruct (midpoint_existence A K) as [K' HK'].
assert (HR' : Rectangle A B D' K') by (apply rect_mid2__rect with D K; auto).
assert (HBD' : B <> D') by (intro; treat_equalities; auto).
destruct (EqR_unit_exists U V A B D' K') as [X [Y [P [Q [R [S HPQRS]]]]]]; auto.
exists X, Y, D, K, D', K', P, Q, R, S; auto.
Qed.

Lemma AreaT_unique U V A B C X Y X' Y' :
  AreaT U V A B C X Y -> AreaT U V A B C X' Y' -> Cong X Y X' Y'.
Proof.
intros [D [K [D' [K' [P [Q [R [S [HF [HD' [HK' [HPQ [HQR HEQR]]]]]]]]]]]]].
intros [d [k [d' [k' [p [q [r [s [Hf [Hd' [Hk' [Hpq [Hqr HEQr]]]]]]]]]]]]].
destruct (EqR_diffs A B D' K' P Q R S HEQR) as [HAB _].
destruct (Circumscribed_rectangle_unique A B C D K d k HAB HF Hf); subst d k.
assert (d' = D') by (apply l7_17 with B D; auto).
assert (k' = K') by (apply l7_17 with A K; auto); subst d' k'.
assert (HC : Cong Q R q r) by (apply EqR_unit_unique with U V A B D' K' P S p s; auto).
CongR.
Qed.

Definition AreaQ U V J K L M X Y :=
  exists A B C D M' N' P Q R S,
    circumscribed_rectangle J K L M A B C D /\
    Midpoint M' B C /\ Midpoint N' A D /\
    Cong P Q U V /\ Cong Q R X Y /\ EqR A B M' N' P Q R S.

Lemma AreaQ_exists U V J K L M :
  U <> V -> Convex J K L M -> ~ Col J L K \/ ~ Col J L M ->
  exists X Y, AreaQ U V J K L M X Y.
Proof.
intros HUV HC HNC.
assert (HJL : J <> L) by (destruct HNC; assert_diffs; auto).
destruct (Circumscribed_rectangle_exists J L K) as [A [B HF1]]; [left; auto|].
destruct (Circumscribed_rectangle_exists J L M) as [D [C HF2]]; [left; auto|].
assert (HCR : circumscribed_rectangle J K L M A B C D) by (split; [auto|left; split; auto]).
destruct (circumscribed_rectangle__rectangle J K L M A B C D) as [HAB [HBC HR]]; auto.
destruct (midpoint_existence B C) as [M' HM'].
destruct (midpoint_existence A D) as [N' HN'].
assert (HR' : Rectangle A B M' N') by (apply rect_mid2__rect with C D; auto).
assert (HBM' : B <> M') by (intro; treat_equalities; auto).
destruct (EqR_unit_exists U V A B M' N') as [X [Y [P [Q [R [S HPQRS]]]]]]; auto.
exists X, Y, A, B, C, D, M', N', P, Q; exists R, S; auto.
Qed.

Lemma AreaQ_unique U V J K L M X Y X' Y' :
  ~ Col J L K \/ ~ Col J L M ->
  AreaQ U V J K L M X Y -> AreaQ U V J K L M X' Y' -> Cong X Y X' Y'.
Proof.
intros HNC.
intros [A [B [C [D [M' [N' [P [Q [R [S [HCR [HM' [HN' [HPQ [HQR HEQR]]]]]]]]]]]]]]].
intros [a [b [c [d [m' [n' [p [q [r [s [Hcr [Hm' [Hn' [Hpq [Hqr HEQr]]]]]]]]]]]]]]].
destruct (circumscribed_rectangle__rectangle J K L M A B C D) as [HAB [HBC HR]]; auto.
destruct (circumscribed_rectangle__rectangle J K L M a b c d) as [Hab [Hbc Hr]]; auto.
assert (HEQ : EqR A B C D a b c d) by (apply circumscribed_rectangle_EqR with J K L M; auto).
assert (HEQ3 : EqR A B M' N' a b m' n')
  by (apply (EqR_halves A B C D a b c d M' N' m' n'); auto).
assert (HC : Cong Q R q r).
  {
  apply EqR_unit_unique with U V A B M' N' P S p s; auto.
  apply EqR_trans with a b m' n'; auto.
  }
CongR.
Qed.

Lemma B8_3_T U V A B C a b c X Y x y :
  AreaT U V A B C X Y -> AreaT U V a b c x y ->
  EqT A B C a b c <-> Cong X Y x y.
Proof.
intros [D [K [D' [K' [P [Q [R [S [HF [HD' [HK' [HPQ [HQR HEQR]]]]]]]]]]]]].
intros [d [k [d' [k' [p [q [r [s [Hf [Hd' [Hk' [Hpq [Hqr HEQr]]]]]]]]]]]]].
destruct (EqR_diffs A B D' K' P Q R S HEQR) as [HAB [HBD' _]].
destruct (EqR_diffs a b d' k' p q r s HEQr) as [Hab [Hbd' _]].
assert (HR : Rectangle A B D K) by (destruct HF; auto).
assert (Hr : Rectangle a b d k) by (destruct Hf; auto).
assert (HBD : B <> D) by (intro; treat_equalities; auto).
assert (Hbd : b <> d) by (intro; treat_equalities; auto).
assert (HU := EqR_unit_iff U V A B D' K' a b d' k' P Q R S p q r s HPQ Hpq HEQR HEQr).
assert (HH := EqR_halves A B D K a b d k D' K' d' k' HAB HBD Hab Hbd HR Hr HD' HK' Hd' Hk').
split.
- intros [D0 [K0 [d0 [k0 [HF0 [Hf0 HEQ]]]]]].
  destruct (Circumscribed_rectangle_unique A B C D K D0 K0 HAB HF HF0); subst D0 K0.
  destruct (Circumscribed_rectangle_unique a b c d k d0 k0 Hab Hf Hf0); subst d0 k0.
  assert (Cong Q R q r) by (apply HU, HH; auto).
  CongR.
- intro HC; exists D, K, d, k; split; [auto|split; [auto|]].
  apply HH, HU; CongR.
Qed.

Lemma B8_3_Q U V J K L M j k l m X Y x y :
  ~ Col J L K \/ ~ Col J L M -> ~ Col j l k \/ ~ Col j l m ->
  AreaQ U V J K L M X Y -> AreaQ U V j k l m x y ->
  EqQ J K L M j k l m <-> Cong X Y x y.
Proof.
intros HNC Hnc.
intros [A [B [C [D [M' [N' [P [Q [R [S [HCR [HM' [HN' [HPQ [HQR HEQR]]]]]]]]]]]]]]].
intros [a [b [c [d [m' [n' [p [q [r [s [Hcr [Hm' [Hn' [Hpq [Hqr HEQr]]]]]]]]]]]]]]].
destruct (circumscribed_rectangle__rectangle J K L M A B C D) as [HAB [HBC HR]]; auto.
destruct (circumscribed_rectangle__rectangle j k l m a b c d) as [Hab [Hbc Hr]]; auto.
assert (HU := EqR_unit_iff U V A B M' N' a b m' n' P Q R S p q r s HPQ Hpq HEQR HEQr).
assert (HH := EqR_halves A B C D a b c d M' N' m' n' HAB HBC Hab Hbc HR Hr HM' HN' Hm' Hn').
split.
- intros [A0 [B0 [C0 [D0 [a0 [b0 [c0 [d0 [HCR0 [Hcr0 HEQ]]]]]]]]]].
  assert (HEQ' : EqR A B C D a b c d).
    {
    apply EqR_trans with A0 B0 C0 D0; [apply circumscribed_rectangle_EqR with J K L M; auto|].
    apply EqR_trans with a0 b0 c0 d0; [auto|apply circumscribed_rectangle_EqR with j k l m; auto].
    }
  assert (Cong Q R q r) by (apply HU, HH; auto).
  CongR.
- intro HC; exists A, B, C, D, a, b, c, d; split; [auto|split; [auto|]].
  apply HH, HU; CongR.
Qed.

Lemma bet_mid2__mid_cong A B C P Q :
  Bet A B C -> A <> B -> B <> C -> Midpoint P B A -> Midpoint Q B C ->
  exists M, Midpoint M A C /\ Bet A P M /\ Cong P M B Q.
Proof.
intros HB HAB HBC HP HQ.
destruct (midpoint_existence P Q) as [O HO].
destruct (symmetric_point_construction B O) as [M HM].
assert (HPBQ : Bet P B Q) by (apply between_inner_transitivity with C; [apply between_exchange3 with A|]; Between).
assert (HQMP : Bet Q M P) by (apply l7_15 with P B Q O; Midpoint).
assert (HC1 : Cong P M Q B) by (apply l7_13 with O; Midpoint).
assert (HC2 : Cong Q M P B) by (apply l7_13 with O; Midpoint).
assert (HPB : P <> B) by (intro; treat_equalities; auto).
assert (HBQ : B <> Q) by (intro; treat_equalities; auto).
assert (HAPQ : Bet A P Q) by (apply outer_transitivity_between with B; Between).
assert (HAPM : Bet A P M) by (apply between_inner_transitivity with Q; Between).
assert (HPQC : Bet P Q C) by (apply outer_transitivity_between2 with B; Between).
assert (HMQC : Bet M Q C) by (apply between_exchange3 with P; Between).
assert (HMQ : M <> Q) by (intro; treat_equalities; auto).
assert (HAMQ : Bet A M Q) by (apply between_exchange2 with P; Between).
assert (HAMC : Bet A M C) by (apply outer_transitivity_between with Q; auto).
exists M; split; [|split; [auto|CongR]].
split; [auto|].
apply l2_11 with P Q; Between.
- apply cong_transitivity with P B; [Cong|CongR].
- apply cong_transitivity with B Q; Cong.
Qed.

Lemma B8_4 U V J K L M X Y Z :
  Convex J K L M -> ~ Col J L K -> ~ Col J L M ->
  AreaT U V J L K X Y -> AreaT U V J L M Y Z -> Bet X Y Z ->
  AreaQ U V J K L M X Z.
Proof.
(* This simplifies the paper's proof of Theorem 8.4: Lemma 7.13 is not needed, since the
   circumscribed rectangle of J K L M along J L is the paste of those of J L K and J L M (B5_8). *)
intros HC HNC1 HNC2.
intros [D1 [K1 [D1' [K1' [P1 [Q1 [R1 [S1 [HF1 [HD1' [HK1' [HPQ1 [HQR1 HEQ1]]]]]]]]]]]]].
intros [D2 [K2 [D2' [K2' [P2 [Q2 [R2 [S2 [HF2 [HD2' [HK2' [HPQ2 [HQR2 HEQ2]]]]]]]]]]]]].
intro HB.
assert (HCR : circumscribed_rectangle J K L M D1 K1 K2 D2) by (split; [auto|left; split; auto]).
destruct (circumscribed_rectangle__bet J K L M D1 K1 K2 D2) as [HB1 HB2]; auto.
destruct (circumscribed_rectangle__rectangle J K L M D1 K1 K2 D2) as [HD1K1 [HK1K2 HR]]; auto.
destruct (FCR_ncol__diffs J L K D1 K1) as [HLD1 [_ HK1J]]; auto.
destruct (FCR_ncol__diffs J L M D2 K2) as [HLD2 [HD2K2 HK2J]]; auto.
assert (HR1 : Rectangle J L D1 K1) by (destruct HF1; auto).
assert (HR2 : Rectangle J L D2 K2) by (destruct HF2; auto).
destruct (EqR_diffs J L D1' K1' P1 Q1 R1 S1 HEQ1) as [HJL [HLD1' [HP1Q1 HQ1R1]]].
destruct (EqR_diffs J L D2' K2' P2 Q2 R2 S2 HEQ2) as [_ [HLD2' [HP2Q2 HQ2R2]]].
assert (HXY : X <> Y) by (intro; treat_equalities; auto).
assert (HYZ : Y <> Z) by (intro; treat_equalities; auto).
destruct (bet_mid2__mid_cong K1 J K2 K1' K2') as [M' [HM' [HB3 HC3]]]; auto.
destruct (midpoint_existence D1 D2) as [N' HN'].
assert (HR3 : Rectangle D1 K1 M' N') by (apply rect_mid2__rect with K2 D2; auto).
assert (HK1M' : K1 <> M') by (intro; treat_equalities; auto).
assert (HK1K1' : K1 <> K1') by (intro; treat_equalities; auto).
assert (HK1'M' : K1' <> M') by (intro; treat_equalities; auto).
assert (HR3' : Rectangle K1 M' N' D1) by (apply rect_permut; auto).
assert (HM'N' : M' <> N') by (intro; treat_equalities; apply degenerated_rect_eq in HR3'; auto).
assert (HEx : exists Q, Bet D1 Q N' /\ Rectangle K1 K1' Q D1 /\ Rectangle K1' M' N' Q)
  by (apply rect_cut_exists; auto).
destruct HEx as [Q [_ [HR4 HR5]]].
assert (HCJL : Cong J L D1 K1)
  by (apply Rectangle_Parallelogram, plg_cong_1 in HR1; auto).
assert (HCJK1 : Cong J K1 L D1)
  by (apply Rectangle_Parallelogram, plg_cong_2 in HR1; Cong).
assert (HCJK2 : Cong J K2 L D2)
  by (apply Rectangle_Parallelogram, plg_cong_2 in HR2; Cong).
assert (HCQK1' : Cong Q K1' D1 K1)
  by (apply Rectangle_Parallelogram, plg_cong_2 in HR4; Cong).
assert (HRJ1 : Rectangle J L D1' K1') by (apply rect_mid2__rect with D1 K1; auto).
assert (HRJ2 : Rectangle J L D2' K2') by (apply rect_mid2__rect with D2 K2; auto).
assert (HR4' : Rectangle D1 K1 K1' Q) by (do 3 apply rect_permut; auto).
assert (HR5' : Rectangle Q K1' M' N') by (do 3 apply rect_permut; auto).
assert (HC4 : Cong K1 K1' L D1') by (apply cong_cong_half_1 with J D1; Midpoint; Cong).
assert (HC5 : Cong J K2' L D2') by (apply cong_cong_half_1 with K2 D2; auto).
assert (HQK1' : Q <> K1') by (intro; treat_equalities; auto).
assert (HEQ3 : EqR D1 K1 K1' Q J L D1' K1') by (apply (B5_5 D1 K1 K1' Q J L D1' K1'); auto; CongR).
assert (HEQ4 : EqR Q K1' M' N' J L D2' K2') by (apply (B5_5 Q K1' M' N' J L D2' K2'); auto; CongR).
assert (HUV : U <> V) by (intro; treat_equalities; auto).
destruct (not_col_exists U V HUV) as [W HW].
destruct (ex_per_cong U V V W X Y) as [c [HPer [HCc _]]]; Col.
assert (HcV : c <> V) by (intro; treat_equalities; auto).
assert (HUc : U <> c) by (intro; treat_equalities; apply HUV, l8_8; Perp).
destruct (segment_construction V c Y Z) as [e [HVce HCe]].
assert (Hce : c <> e) by (intro; treat_equalities; auto).
destruct (midpoint_existence U c) as [O1 HO1].
destruct (symmetric_point_construction V O1) as [d Hd].
assert (HRu : Rectangle U V c d)
  by (apply plg_per_rect2; [split; [left; auto|exists O1; split; auto]|auto]).
assert (HPer2 : Per e c d).
  {
  apply l8_2, per_col with V; [auto|apply l8_2, rect_per3 with U; auto|Col].
  }
assert (Hde : d <> e) by (intro; treat_equalities; apply Hce; symmetry; apply l8_8; auto).
destruct (midpoint_existence d e) as [O2 HO2].
destruct (symmetric_point_construction c O2) as [f Hf].
assert (HRl : Rectangle d c e f)
  by (apply plg_per_rect2; [split; [left; auto|exists O2; split; auto]|auto]).
assert (HCUV : Cong U V d c)
  by (apply Rectangle_Parallelogram, plg_cong_1 in HRu; Cong).
assert (HEQ5 : EqR P1 Q1 R1 S1 U V c d).
  {
  destruct HEQ1 as [_ [_ [_ [_ [_ [HRP1 _]]]]]].
  apply (B5_5 P1 Q1 R1 S1 U V c d); auto; CongR.
  }
assert (HEQ6 : EqR P2 Q2 R2 S2 d c e f).
  {
  destruct HEQ2 as [_ [_ [_ [_ [_ [HRP2 _]]]]]].
  assert (d <> c) by (intro; treat_equalities; auto).
  apply (B5_5 P2 Q2 R2 S2 d c e f); auto; CongR.
  }
assert (HEQ7 : EqR D1 K1 K1' Q U V c d)
  by (apply EqR_trans with J L D1' K1'; [|apply EqR_trans with P1 Q1 R1 S1]; auto).
assert (HEQ8 : EqR Q K1' M' N' d c e f)
  by (apply EqR_trans with J L D2' K2'; [|apply EqR_trans with P2 Q2 R2 S2]; auto).
assert (HEQ9 : EqR D1 K1 M' N' U V e f) by (apply B5_8 with K1' Q c d; auto).
assert (HCVe : Cong X Z V e) by (apply l2_11 with Y c; Cong).
exists D1, K1, K2, D2, M', N', U, V, e, f.
split; [auto|split; [auto|split; [auto|split; [Cong|split; [Cong|auto]]]]].
Qed.

Lemma AreaT_cong U V A B C X Y X' Y' :
  AreaT U V A B C X Y -> Cong X Y X' Y' -> AreaT U V A B C X' Y'.
Proof.
intros [D [K [D' [K' [P [Q [R [S [HF [HD' [HK' [HPQ [HQR HEQR]]]]]]]]]]]]] HC.
exists D, K, D', K', P, Q, R, S.
split; [auto|split; [auto|split; [auto|split; [auto|split; [CongR|auto]]]]].
Qed.

Lemma AreaT__AreaQ U V A B m D X Y :
  ~ Col B D A -> Bet B m D -> AreaT U V B D A X Y -> AreaQ U V A B m D X Y.
Proof.
intros HNC HBet [D0 [K0 [D0' [K0' [P [Q [R [S [HF [HD0' [HK0' [HPQ [HQR HEQR]]]]]]]]]]]]].
destruct (FCR_ncol__diffs B D A D0 K0 HNC HF) as [HDD0 [HD0K0 HK0B]].
assert (HBD : B <> D) by (assert_diffs; auto).
assert (HR : Rectangle B D D0 K0) by (destruct HF; auto).
assert (HR1 : Rectangle B D D0' K0') by (apply rect_mid2__rect with D0 K0; auto).
assert (HR2 : Rectangle D0 K0 K0' D0')
  by (apply rect_mid2__rect with B D; [auto|auto|do 2 apply rect_permut; auto|Midpoint|Midpoint]).
assert (HK0K0' : K0 <> K0') by (intro; treat_equalities; auto).
assert (HC1 : Cong D0 K0 B D) by (apply Rectangle_Parallelogram, plg_cong_1 in HR; Cong).
assert (HC2 : Cong K0 K0' D D0').
  {
  apply cong_cong_half_1 with B D0; [Midpoint|Midpoint|].
  apply Rectangle_Parallelogram, plg_cong_2 in HR; Cong.
  }
assert (HEQ : EqR D0 K0 K0' D0' B D D0' K0') by (apply (B5_5 D0 K0 K0' D0' B D D0' K0'); auto; CongR).
exists D0, K0, B, D, K0', D0', P, Q; exists R, S.
split; [split; [exists m; split; Between|right; split; [auto|apply FCR_triv; Col]]|].
split; [Midpoint|split; [Midpoint|split; [auto|split; [auto|]]]].
apply EqR_trans with B D D0' K0'; auto.
Qed.

Lemma AreaQ_AreaT U V A B m D X Y :
  ~ Col B D A -> Bet B m D ->
  AreaQ U V A B m D X Y <-> AreaT U V B D A X Y.
Proof.
intros HNC HBet; split; [|apply AreaT__AreaQ; auto].
intro HQ.
assert (HUV : U <> V).
  {
  destruct HQ as [A0 [B0 [C0 [D0 [M0 [N0 [P [Q [R [S [_ [_ [_ [HPQ [_ HEQ]]]]]]]]]]]]]]].
  destruct (EqR_diffs _ _ _ _ _ _ _ _ HEQ) as [_ [_ [HPQ' _]]].
  intro; treat_equalities; auto.
  }
destruct (AreaT_exists U V B D A) as [X' [Y' HT]]; [auto|Col|].
apply AreaT_cong with X' Y'; [auto|].
apply AreaQ_unique with U V A B m D; [|apply AreaT__AreaQ; auto|auto].
destruct (eq_dec_points m B); [subst; right; Col|left].
intro; apply HNC; ColR.
Qed.

Lemma AreaT_diffs U V A B C X Y :
  AreaT U V A B C X Y -> U <> V /\ X <> Y.
Proof.
intros [D [K [D' [K' [P [Q [R [S [_ [_ [_ [HPQ [HQR HEQR]]]]]]]]]]]]].
destruct (EqR_diffs _ _ _ _ _ _ _ _ HEQR) as [_ [_ [HPQ' HQR']]].
split; intro; treat_equalities; auto.
Qed.

Lemma AreaT_EqT U V A B C a b c X Y :
  AreaT U V A B C X Y -> EqT A B C a b c -> AreaT U V a b c X Y.
Proof.
intros HA HE.
destruct (AreaT_diffs U V A B C X Y HA) as [HUV _].
destruct (EqT_not_col _ _ _ _ _ _ HE) as [_ HNC].
destruct (AreaT_exists U V a b c HUV HNC) as [X' [Y' HA']].
apply AreaT_cong with X' Y'; [auto|].
assert (Cong X Y X' Y') by (apply (B8_3_T U V A B C a b c X Y X' Y'); auto).
Cong.
Qed.

Lemma B8_4_paste1 U V A B C D E X Y W :
  ~ Col A C E -> Bet A B C -> Bet E D C -> A <> B -> B <> C -> E <> D -> D <> C ->
  AreaT U V B C D X Y -> AreaQ U V A B D E Y W -> Bet X Y W ->
  AreaT U V A C E X W.
Proof.
intros HNC HB1 HB2 HAB HBC HED HDC HT HQ HB.
destruct (AreaT_diffs U V B C D X Y HT) as [HUV HXY].
assert (HNC1 : ~ Col B C D) by (intro; apply HNC; ColR).
assert (HNC2 : ~ Col D B A) by (intro; apply HNC; ColR).
assert (HNC3 : ~ Col A D E) by (intro; apply HNC; ColR).
assert (HNC4 : ~ Col C A D) by (intro; apply HNC; ColR).
assert (HNC5 : ~ Col C E A) by Col.
assert (HT1 : AreaT U V D B C X Y)
  by (apply AreaT_EqT with B C D; [auto|destruct (B6_3 B C D); spliter; auto]).
destruct (AreaT_exists U V D B A) as [P [Q HPQ]]; auto.
destruct (segment_construction X Y P Q) as [Z [HXYZ HYZ]].
assert (HT2 : AreaT U V D B A Y Z) by (apply AreaT_cong with P Q; Cong).
destruct (AreaT_diffs U V D B A Y Z HT2) as [_ HYZ'].
destruct (AreaT_exists U V A D E) as [R [S HRS]]; auto.
destruct (segment_construction Y Z R S) as [W' [HYZW' HZW']].
assert (HT3 : AreaT U V A D E Z W') by (apply AreaT_cong with R S; Cong).
assert (HQ1 : AreaQ U V D C B A X Z)
  by (apply B8_4 with Y; [exists B; split; Between|Col|Col|auto..]).
assert (HT4 : AreaT U V C A D X Z) by (apply (AreaQ_AreaT U V D C B A X Z); Between).
assert (HT5 : AreaT U V A D C X Z)
  by (apply AreaT_EqT with C A D; [auto|destruct (B6_3 C A D); spliter; auto]).
assert (HXZW' : Bet X Z W') by (apply outer_transitivity_between2 with Y; auto).
assert (HQ2 : AreaQ U V A C D E X W')
  by (apply B8_4 with Z; [exists D; split; Between|intro; apply HNC; ColR|auto..]).
assert (HT6 : AreaT U V C E A X W') by (apply (AreaQ_AreaT U V A C D E X W'); [Col|Between|auto]).
assert (HT7 : AreaT U V A C E X W')
  by (apply AreaT_EqT with C E A; [auto|destruct (B6_3 C E A); spliter; auto]).
assert (HT8 : AreaT U V A D B Y Z)
  by (apply AreaT_EqT with D B A; [auto|destruct (B6_3 D B A); spliter; auto]).
destruct (inner_pasch A E C B D) as [I [HI1 HI2]]; [auto|auto|].
assert (HQ3 : AreaQ U V A B D E Y W')
  by (apply B8_4 with Z; [exists I; split; Between|Col|auto..]).
assert (HC : Cong Y W Y W') by (apply AreaQ_unique with U V A B D E; [left; Col|auto..]).
apply AreaT_cong with X W'; [auto|].
apply l2_11 with Y Y; [apply outer_transitivity_between with Z; auto|auto|Cong|Cong].
Qed.

Lemma AreaQ_cong U V J K L M X Y X' Y' :
  AreaQ U V J K L M X Y -> Cong X Y X' Y' -> AreaQ U V J K L M X' Y'.
Proof.
intros [A [B [C [D [M' [N' [P [Q [R [S [HCR [HM' [HN' [HPQ [HQR HEQR]]]]]]]]]]]]]]] HC.
exists A, B, C, D, M', N', P, Q; exists R, S.
split; [auto|split; [auto|split; [auto|split; [auto|split; [CongR|auto]]]]].
Qed.

Lemma B8_4_paste2 U V A B C D E M X Y W :
  ~ Col A B D -> ~ Col C D E -> ~ Col A C E -> ~ Col A D E ->
  Bet A M D -> Bet B M E -> Bet B C D -> B <> C -> C <> D ->
  AreaQ U V A B C E X Y -> AreaT U V C D E Y W -> Bet X Y W ->
  AreaQ U V A B D E X W.
Proof.
intros HNC1 HNC2 HNC3 HNC4 HB1 HB2 HB3 HBC HCD HQ HT HB.
destruct (AreaT_diffs U V C D E Y W HT) as [HUV HYW].
assert (HNC5 : ~ Col A C B) by (intro; apply HNC1; ColR).
assert (HNC6 : ~ Col A C D) by (intro; apply HNC1; ColR).
assert (HNC7 : ~ Col B D A) by Col.
assert (HNC8 : ~ Col C E A) by Col.
destruct (AreaT_exists U V A C B) as [P1 [Q1' HT1]]; auto.
destruct (segment_construction W X P1 Q1') as [Z [_ HXZ]].
assert (HT1' : AreaT U V A C B X Z) by (apply AreaT_cong with P1 Q1'; Cong).
destruct (AreaT_exists U V A C E) as [P2 [Q2' HT2]]; auto.
destruct (segment_construction X Z P2 Q2') as [Y' [HXZY' HZY']].
assert (HT2' : AreaT U V A C E Z Y') by (apply AreaT_cong with P2 Q2'; Cong).
destruct (AreaT_exists U V A C D) as [P3 [Q3' HT3]]; auto.
destruct (segment_construction X Z P3 Q3') as [Q1 [HXZQ1 HZQ1]].
assert (HT3' : AreaT U V A C D Z Q1) by (apply AreaT_cong with P3 Q3'; Cong).
destruct (AreaT_exists U V A D E) as [P4 [Q4' HT4]]; auto.
destruct (segment_construction Z Q1 P4 Q4') as [Q2 [HZQ1Q2 HQ1Q2]].
assert (HT4' : AreaT U V A D E Q1 Q2) by (apply AreaT_cong with P4 Q4'; Cong).
destruct (segment_construction Z Y' Y W) as [W' [HZY'W' HY'W']].
destruct (AreaT_diffs U V A C B X Z HT1') as [_ HXZ'].
destruct (AreaT_diffs U V A C E Z Y' HT2') as [_ HZY''].
destruct (AreaT_diffs U V A C D Z Q1 HT3') as [_ HZQ1'].
destruct (inner_pasch B A D C M) as [I [HI1 HI2]]; [auto|auto|].
assert (HBIE : Bet B I E) by (apply between_exchange4 with M; Between).
destruct (inner_pasch E D B M C) as [J [HJ1 HJ2]]; [Between|Between|].
assert (HAJD : Bet A J D) by (apply between_exchange2 with M; auto).
assert (HQ1 : AreaQ U V A B C E X Y')
  by (apply B8_4 with Z; [exists I; split; Between|auto..]).
assert (HC1 : Cong X Y X Y') by (apply AreaQ_unique with U V A B C E; [left; auto|auto..]).
assert (HQ2 : AreaQ U V A B C D X Q1)
  by (apply B8_4 with Z; [exists C; split; Between|auto..]).
assert (HT5 : AreaT U V B D A X Q1) by (apply (AreaQ_AreaT U V A B C D X Q1); auto).
assert (HT6 : AreaT U V A D B X Q1)
  by (apply AreaT_EqT with B D A; [auto|destruct (B6_3 B D A); spliter; auto]).
assert (HT7 : AreaT U V A D C Z Q1)
  by (apply AreaT_EqT with A C D; [auto|destruct (B6_3 A C D); spliter; auto]).
assert (HQ3 : AreaQ U V A C D E Z Q2)
  by (apply B8_4 with Q1; [exists J; split; Between|Col|auto..]).
assert (HT8 : AreaT U V C E A Z Y')
  by (apply AreaT_EqT with A C E; [auto|destruct (B6_3 A C E); spliter; auto]).
assert (HT9 : AreaT U V C E D Y' W').
  {
  apply AreaT_EqT with C D E; [apply AreaT_cong with Y W; Cong|].
  destruct (B6_3 C D E); spliter; auto.
  }
assert (HQ4 : AreaQ U V C A E D Z W')
  by (apply B8_4 with Y'; [exists J; split; Between|auto|intro; apply HNC2; Col|auto..]).
assert (HC2 : Cong Z Q2 Z W').
  {
  apply (B8_3_Q U V A C D E C A E D Z Q2 Z W'); [left; Col|left; auto|auto|auto|].
  apply EqQ_perm; [exists J; split; Between|auto|auto].
  }
assert (HXQ1Q2 : Bet X Q1 Q2) by (apply outer_transitivity_between2 with Z; auto).
assert (HQ5 : AreaQ U V A B D E X Q2)
  by (apply B8_4 with Q1; [exists M; split; auto|Col|auto..]).
apply AreaQ_cong with X Q2; [auto|].
apply cong_transitivity with X W'.
- apply l2_11 with Z Z; [apply outer_transitivity_between with Q1; auto|
                         apply outer_transitivity_between with Y'; auto|Cong|auto].
- apply l2_11 with Y' Y; [apply outer_transitivity_between2 with Z; auto|auto|Cong|Cong].
Qed.

Lemma AreaQ_EqQ U V J K L M j k l m X Y :
  ~ Col J L K \/ ~ Col J L M -> ~ Col j l k \/ ~ Col j l m ->
  AreaQ U V J K L M X Y -> EqQ J K L M j k l m -> AreaQ U V j k l m X Y.
Proof.
intros HNC Hnc HA HE.
assert (HUV : U <> V).
  {
  destruct HA as [A [B [C [D [M' [N' [P [Q [R [S [_ [_ [_ [HPQ [_ HEQ]]]]]]]]]]]]]]].
  destruct (EqR_diffs _ _ _ _ _ _ _ _ HEQ) as [_ [_ [HPQ' _]]].
  intro; treat_equalities; auto.
  }
assert (HC : Convex j k l m)
  by (destruct HE as [A [B [C [D [a [b [c [d [_ [[HCv _] _]]]]]]]]]]; auto).
destruct (AreaQ_exists U V j k l m) as [X' [Y' HA']]; auto.
apply AreaQ_cong with X' Y'; [auto|].
assert (Cong X Y X' Y') by (apply (B8_3_Q U V J K L M j k l m X Y X' Y'); auto).
Cong.
Qed.

Lemma paste1 A B C D E a b c d e :
  Bet A B C -> A <> B -> B <> C -> Bet a b c -> a <> b -> b <> c ->
  Bet E D C -> E <> D -> D <> C -> Bet e d c -> e <> d -> d <> c ->
  EqT B C D b c d -> EqQ A B D E a b d e -> EqT A C E a c e.
Proof.
intros HB1 HAB HBC Hb1 Hab Hbc HB2 HED HDC Hb2 Hed Hdc HT HQ.
destruct (EqT_not_col B C D b c d HT) as [HNC1 HNC2].
assert (HNC3 : ~ Col A C E) by (intro; apply HNC1; ColR).
assert (HNC4 : ~ Col a c e) by (intro; apply HNC2; ColR).
assert (HNC5 : ~ Col A D B) by (intro; apply HNC1; ColR).
assert (HNC6 : ~ Col a d b) by (intro; apply HNC2; ColR).
destruct (AreaT_exists B C B C D) as [X [Y HT1]]; auto.
destruct (inner_pasch A E C B D) as [I [HI1 HI2]]; auto.
destruct (AreaQ_exists B C A B D E) as [P [Q HQ1]]; [auto|exists I; split; Between|left; auto|].
destruct (segment_construction X Y P Q) as [W [HXYW HYW]].
assert (HQ2 : AreaQ B C A B D E Y W) by (apply AreaQ_cong with P Q; Cong).
assert (HT2 : AreaT B C A C E X W) by (apply (B8_4_paste1 B C A B C D E X Y W); auto).
assert (HT3 : AreaT B C b c d X Y) by (apply AreaT_EqT with B C D; auto).
assert (HQ3 : AreaQ B C a b d e Y W) by (apply AreaQ_EqQ with A B D E; [left|left|..]; auto).
assert (HT4 : AreaT B C a c e X W) by (apply (B8_4_paste1 B C a b c d e X Y W); auto).
apply (B8_3_T B C A C E a c e X W X W); Cong.
Qed.

Lemma paste2_ncol A B C D E M :
  Bet B C D -> B <> C -> C <> D ->
  Bet A M D -> A <> M -> M <> D -> Bet B M E -> B <> M -> M <> E ->
  ~ Col C D E ->
  ~ Col A B D /\ ~ Col A D E /\ ~ Col A C E.
Proof.
intros HB1 HBC HCD HB2 HAM HMD HB3 HBM HME HNC.
assert (HBD : B <> D) by (intro; treat_equalities; auto).
assert (HAD : A <> D) by (intro; treat_equalities; auto).
assert (HBE : B <> E) by (intro; treat_equalities; auto).
assert (HNC1 : ~ Col B D E) by (intro; apply HNC; ColR).
assert (HNC2 : ~ Col A B D).
  {
  intro HCol; apply HBM.
  apply (l6_21 B D E B B M); Col; ColR.
  }
assert (HNC3 : ~ Col A D E) by (intro; apply HNC2; ColR).
split; [auto|split; [auto|]].
assert (HNC4 : ~ Col A E B) by (intro; apply HNC3; ColR).
assert (HOS1 : OS A E D M) by (apply out_one_side; [left; Col|apply l6_6, bet_out; Between]).
assert (HOS2 : OS E A B M) by (apply out_one_side; [left; Col|apply l6_6, bet_out; Between]).
assert (HOS3 : OS A E B D)
  by (apply one_side_transitivity with M; [apply invert_one_side; auto|apply one_side_symmetry; auto]).
assert (HOS4 : OS A E B C) by (apply l9_17 with D; auto).
intro; apply (one_side_not_col124 A E B C HOS4); Col.
Qed.

Lemma paste2 A B C D E M a b c d e m :
  Bet B C D -> B <> C -> C <> D -> Bet b c d -> b <> c -> c <> d ->
  EqT C D E c d e -> EqQ A B C E a b c e ->
  Bet A M D -> A <> M -> M <> D -> Bet B M E -> B <> M -> M <> E ->
  Bet a m d -> a <> m -> m <> d -> Bet b m e -> b <> m -> m <> e ->
  EqQ A B D E a b d e.
Proof.
intros HB1 HBC HCD Hb1 Hbc Hcd HT HQ HB2 HAM HMD HB3 HBM HME Hb2 Ham Hmd Hb3 Hbm Hme.
destruct (EqT_not_col C D E c d e HT) as [HNC1 HNC2].
destruct (paste2_ncol A B C D E M) as [HNC3 [HNC4 HNC5]]; auto.
destruct (paste2_ncol a b c d e m) as [HNC6 [HNC7 HNC8]]; auto.
assert (HNC9 : ~ Col A C B) by (intro; apply HNC3; ColR).
assert (HNC10 : ~ Col a c b) by (intro; apply HNC6; ColR).
destruct (inner_pasch B A D C M) as [I [HI1 HI2]]; auto.
assert (HBIE : Bet B I E) by (apply between_exchange4 with M; Between).
destruct (AreaQ_exists B C A B C E) as [X [Y HQ1]]; [auto|exists I; split; Between|left; auto|].
destruct (AreaT_exists B C C D E) as [P [Q HT1]]; auto.
destruct (segment_construction X Y P Q) as [W [HXYW HYW]].
assert (HT2 : AreaT B C C D E Y W) by (apply AreaT_cong with P Q; Cong).
assert (HQ2 : AreaQ B C A B D E X W) by (apply (B8_4_paste2 B C A B C D E M X Y W); auto).
assert (HQ3 : AreaQ B C a b c e X Y) by (apply AreaQ_EqQ with A B C E; [left|left|..]; auto).
assert (HT3 : AreaT B C c d e Y W) by (apply AreaT_EqT with C D E; auto).
assert (HQ4 : AreaQ B C a b d e X W) by (apply (B8_4_paste2 B C a b c d e m X Y W); auto).
apply (B8_3_Q B C A B D E a b d e X W X W); [left; Col|left; Col|auto|auto|Cong].
Qed.

Lemma cutoff1 A B C D E a b c d e :
  Bet A B C -> A <> B -> B <> C -> Bet a b c -> a <> b -> b <> c ->
  Bet E D C -> E <> D -> D <> C -> Bet e d c -> e <> d -> d <> c ->
  EqT B C D b c d -> EqT A C E a c e -> EqQ A B D E a b d e.
Proof.
intros HB1 HAB HBC Hb1 Hab Hbc HB2 HED HDC Hb2 Hed Hdc HT1 HT2.
destruct (EqT_not_col B C D b c d HT1) as [HNC1 HNC2].
assert (HNC3 : ~ Col A C E) by (intro; apply HNC1; ColR).
assert (HNC4 : ~ Col a c e) by (intro; apply HNC2; ColR).
assert (HNC5 : ~ Col A D B) by (intro; apply HNC1; ColR).
assert (HNC6 : ~ Col a d b) by (intro; apply HNC2; ColR).
destruct (AreaT_exists B C B C D) as [X [Y HA1]]; auto.
assert (HA2 : AreaT B C b c d X Y) by (apply AreaT_EqT with B C D; auto).
destruct (inner_pasch A E C B D) as [I [HI1 HI2]]; auto.
destruct (inner_pasch a e c b d) as [i [Hi1 Hi2]]; auto.
destruct (AreaQ_exists B C A B D E) as [P [Q HQ]]; [auto|exists I; split; Between|left; auto|].
destruct (AreaQ_exists B C a b d e) as [p [q Hq]]; [auto|exists i; split; Between|left; auto|].
destruct (segment_construction X Y P Q) as [W [HXYW HYW]].
destruct (segment_construction X Y p q) as [w [HXYw HYw]].
assert (HA3 : AreaQ B C A B D E Y W) by (apply AreaQ_cong with P Q; Cong).
assert (HA4 : AreaQ B C a b d e Y w) by (apply AreaQ_cong with p q; Cong).
assert (HA5 : AreaT B C A C E X W) by (apply (B8_4_paste1 B C A B C D E X Y W); auto).
assert (HA6 : AreaT B C a c e X w) by (apply (B8_4_paste1 B C a b c d e X Y w); auto).
assert (HC1 : Cong X W X w) by (apply (B8_3_T B C A C E a c e X W X w); auto).
assert (HC2 : Cong Y W Y w) by (apply l4_3_1 with X X; Cong).
apply (B8_3_Q B C A B D E a b d e Y W Y w); [left|left|..]; auto.
Qed.

Lemma AreaQ_rot U V A B C D X Y :
  Convex A B C D -> ~ Col A C B \/ ~ Col A C D -> ~ Col B D C \/ ~ Col B D A ->
  AreaQ U V A B C D X Y -> AreaQ U V B C D A X Y.
Proof.
intros HC HNC1 HNC2 HA.
apply AreaQ_EqQ with A B C D; auto.
apply EqQ_abcd_bcda; [auto|destruct HNC1; [left|right]; Col].
Qed.

Lemma cutoff2_side A B C D E M :
  Bet B C D -> B <> C -> C <> D -> ~ Col C D E -> Bet A M D -> Bet B M E ->
  Convex A B C E /\ (~ Col A C B \/ ~ Col A C E) /\ (~ Col A D B \/ ~ Col A D E) /\
  (forall U V X Y W, AreaQ U V A B C E X Y -> AreaT U V C D E Y W -> Bet X Y W ->
                     AreaQ U V A B D E X W).
Proof.
intros HB1 HBC HCD HNC HB2 HB3.
assert (HBD : B <> D) by (intro; treat_equalities; auto).
assert (HNC1 : ~ Col B D E) by (intro; apply HNC; ColR).
assert (HMD : M <> D) by (intro; subst; apply HNC1; Col).
assert (HAD : A <> D) by (intro; treat_equalities; auto).
assert (HNC3 : ~ Col E C B) by (intro; apply HNC1; ColR).
destruct (inner_pasch B A D C M) as [I [HI1 HI2]]; auto.
assert (HBIE : Bet B I E) by (apply between_exchange4 with M; Between).
assert (HCv : Convex A B C E) by (exists I; split; Between).
assert (HNC5 : ~ Col A C B \/ ~ Col A C E).
  {
  destruct (col_dec A C B) as [HCol|]; [right|left; auto].
  assert (HAC : A <> C).
    {
    intro; subst A.
    assert (M = B) by (apply (l6_21 B D E B M B); [auto|intro; subst; apply HNC1; Col|ColR|Col|Col|Col]).
    subst; apply HBC, between_equality with D; Between.
    }
  intro; apply HNC1; ColR.
  }
assert (HNC6 : ~ Col A D B \/ ~ Col A D E)
  by (destruct (col_dec A D B); [right; intro; apply HNC1; ColR|left; auto]).
split; [auto|split; [auto|split; [auto|]]].
intros U V X Y W HQ HT HXYW.
destruct (AreaT_diffs U V C D E Y W HT) as [HUV HYW].
assert (HCvEBCD : Convex E B C D) by (exists C; split; Between).
destruct (AreaT_exists U V E B C) as [P1 [Q1 HT1]]; Col.
destruct (eq_dec_points M A) as [HMA|HMA].
- subst M.
  destruct (segment_construction W X P1 Q1) as [Y' [_ HXY']].
  destruct (segment_construction X Y' Y W) as [W' [HXY'W' HY'W']].
  assert (HT2 : AreaT U V E C B X Y')
    by (apply AreaT_EqT with E B C; [apply AreaT_cong with P1 Q1; Cong|destruct (B6_3 E B C); spliter; Col]).
  assert (HT3 : AreaT U V E C D Y' W').
    {
    apply AreaT_EqT with C D E; [apply AreaT_cong with Y W; Cong|].
    destruct (B6_3 C D E); spliter; auto.
    }
  assert (HQ1 : AreaQ U V E B C D X W') by (apply B8_4 with Y'; Col).
  assert (HT4 : AreaT U V B D E X W') by (apply (AreaQ_AreaT U V E B C D X W'); auto).
  assert (HT5 : AreaT U V E B D X W')
    by (apply AreaT_EqT with B D E; [auto|destruct (B6_3 B D E); spliter; auto]).
  assert (HQ2 : AreaQ U V D E A B X W') by (apply (AreaQ_AreaT U V D E A B X W'); [Col|Between|auto]).
  assert (HNC7 : ~ Col D A E \/ ~ Col D A B)
    by (destruct (eq_dec_points A E); [subst; right; Col|left; intro; apply HNC1; ColR]).
  assert (HQ3 : AreaQ U V E A B D X W')
    by (apply AreaQ_rot; [exists A; split; Between|auto|right; Col|auto]).
  assert (HQ4 : AreaQ U V A B D E X W')
    by (apply AreaQ_rot; [exists A; split; Between|right; Col|auto|auto]).
  assert (HQ5 : AreaQ U V B C E A X Y) by (apply AreaQ_rot; [auto|auto|left; Col|auto]).
  assert (HQ6 : AreaQ U V C E A B X Y)
    by (apply AreaQ_rot; [exists I; split; Between|left; Col|destruct HNC5; [right|left]; Col|auto]).
  assert (HT6 : AreaT U V E B C X Y) by (apply (AreaQ_AreaT U V C E A B X Y); [Col|Between|auto]).
  assert (HT7 : AreaT U V E B C X Y') by (apply AreaT_cong with P1 Q1; Cong).
  assert (HC : Cong X Y X Y') by (apply AreaT_unique with U V E B C; auto).
  apply AreaQ_cong with X W'; [auto|].
  apply l2_11 with Y' Y; [auto|auto|Cong|Cong].
- assert (HNC7 : ~ Col E B A) by (intro; apply HNC1; ColR).
  destruct (AreaT_exists U V E B A) as [P0 [Q0 HT0]]; auto.
  destruct (segment_construction W X P0 Q0) as [Z [_ HXZ]].
  destruct (segment_construction X Z P1 Q1) as [Y' [HXZY' HZY']].
  destruct (segment_construction Z Y' Y W) as [W' [HZY'W' HY'W']].
  assert (HT1' : AreaT U V E B A X Z) by (apply AreaT_cong with P0 Q0; Cong).
  assert (HT2 : AreaT U V E B C Z Y') by (apply AreaT_cong with P1 Q1; Cong).
  assert (HT2' : AreaT U V E C B Z Y')
    by (apply AreaT_EqT with E B C; [auto|destruct (B6_3 E B C); spliter; Col]).
  assert (HT3 : AreaT U V E C D Y' W').
    {
    apply AreaT_EqT with C D E; [apply AreaT_cong with Y W; Cong|].
    destruct (B6_3 C D E); spliter; auto.
    }
  destruct (AreaT_diffs U V E B C Z Y' HT2) as [_ HZY''].
  assert (HQ1 : AreaQ U V E B C D Z W') by (apply B8_4 with Y'; Col).
  assert (HT4 : AreaT U V B D E Z W') by (apply (AreaQ_AreaT U V E B C D Z W'); auto).
  assert (HT5 : AreaT U V E B D Z W')
    by (apply AreaT_EqT with B D E; [auto|destruct (B6_3 B D E); spliter; auto]).
  assert (HXZW' : Bet X Z W') by (apply outer_transitivity_between with Y'; auto).
  assert (HQ2 : AreaQ U V E A B D X W')
    by (apply B8_4 with Z; [exists M; split; Between|auto|Col|auto..]).
  assert (HQ3 : AreaQ U V A B D E X W')
    by (apply AreaQ_rot; [exists M; split; Between|left; auto|auto|auto]).
  assert (HQ4 : AreaQ U V E A B C X Y')
    by (apply B8_4 with Z; [exists I; split; Between|auto|Col|auto..]).
  assert (HQ5 : AreaQ U V A B C E X Y')
    by (apply AreaQ_rot; [exists I; split; Between|left; auto|auto|auto]).
  assert (HC : Cong X Y X Y') by (apply AreaQ_unique with U V A B C E; auto).
  apply AreaQ_cong with X W'; [auto|].
  apply l2_11 with Y' Y; [apply outer_transitivity_between2 with Z; auto|auto|Cong|Cong].
Qed.

Lemma cutoff2 A B C D E a b c d e :
  Bet B C D -> B <> C -> C <> D -> Bet b c d -> b <> c -> c <> d ->
  EqT C D E c d e -> EqQ A B D E a b d e -> EqQ A B C E a b c e.
Proof.
intros HB1 HBC HCD Hb1 Hbc Hcd HT HQ.
destruct (EqT_not_col C D E c d e HT) as [HNC1 HNC2].
assert (HQ' := HQ).
destruct HQ' as [A0 [B0 [C0 [D0 [a0 [b0 [c0 [d0 [[[M [HM1 HM2]] _] [[[m [Hm1 Hm2]] _] _]]]]]]]]]].
destruct (cutoff2_side A B C D E M) as [HCv [HNC3 [HNC4 HAdd]]]; auto.
destruct (cutoff2_side a b c d e m) as [Hcv [HNC5 [HNC6 Hadd]]]; auto.
destruct (AreaQ_exists C D A B C E) as [X [Y HA1]]; auto.
destruct (AreaQ_exists C D a b c e) as [x [y HA2]]; auto.
destruct (AreaT_exists C D C D E) as [P [Q HA3]]; auto.
assert (HA4 : AreaT C D c d e P Q) by (apply AreaT_EqT with C D E; auto).
destruct (segment_construction X Y P Q) as [W [HXYW HYW]].
destruct (segment_construction x y P Q) as [w [Hxyw Hyw]].
assert (HA5 : AreaQ C D A B D E X W) by (apply HAdd with Y; [auto|apply AreaT_cong with P Q; Cong|auto]).
assert (HA6 : AreaQ C D a b d e x w) by (apply Hadd with y; [auto|apply AreaT_cong with P Q; Cong|auto]).
assert (HC1 : Cong X W x w) by (apply (B8_3_Q C D A B D E a b d e X W x w); auto).
assert (HC2 : Cong X Y x y) by (apply l4_3 with W w; [auto|auto|auto|CongR]).
apply (B8_3_Q C D A B C E a b c e X Y x y); auto.
Qed.

Lemma EqQ_ncol J K L M j k l m :
  EqQ J K L M j k l m -> ~ Col J L K \/ ~ Col J L M.
Proof.
intros [A [B [C [D [a [b [c [d [[[E [HE1 HE2]] HCR] [_ HEQR]]]]]]]]]].
destruct (EqR_diffs _ _ _ _ _ _ _ _ HEQR) as [HAB [HBC _]].
destruct (col_dec J L K) as [HC1|]; [|left; auto].
destruct (col_dec J L M) as [HC2|]; [|right; auto].
exfalso.
destruct HCR as [[HF1 HF2]|[HF1 HF2]].
- destruct (FCR_Col__eq' J L K A B) as [HJB HLA]; auto.
  destruct (FCR_Col__eq J L M D C) as [HJC HLD]; [auto|auto|intro; treat_equalities; auto|].
  subst; auto.
- assert (HC3 : Col K M J /\ Col K M L).
    {
    destruct (eq_dec_points J L); [subst; treat_equalities; split; Col|split; ColR].
    }
  destruct HC3 as [HC3 HC4].
  destruct (FCR_Col__eq' K M J A B) as [HKB HMA]; auto.
  destruct (FCR_Col__eq K M L D C) as [HKC HMD]; [auto|auto|intro; treat_equalities; auto|].
  subst; auto.
Qed.

Lemma AreaQ_diffs U V J K L M X Y :
  AreaQ U V J K L M X Y -> U <> V /\ X <> Y.
Proof.
intros [A [B [C [D [M' [N' [P [Q [R [S [_ [_ [_ [HPQ [HQR HEQR]]]]]]]]]]]]]]].
destruct (EqR_diffs _ _ _ _ _ _ _ _ HEQR) as [_ [_ [HPQ' HQR']]].
split; intro; treat_equalities; auto.
Qed.

Lemma B8_4_quad2 U V F G H J K L M X Y Z :
  Bet K H M -> K <> H -> H <> M -> Bet F G L -> F <> G -> G <> L ->
  Bet F J M -> F <> J -> J <> M -> Bet K J L -> K <> J -> J <> L ->
  ~ Col F K M -> Convex F K H G -> Convex G H M L ->
  AreaQ U V F K H G X Y -> AreaQ U V G H M L Y Z -> Bet X Y Z ->
  AreaQ U V F K M L X Z.
Proof.
intros HKHM HKH HHM HFGL HFG HGL HFJM HFJ HJM HKJL HKJ HJL HNC1 HCv1 HCv2 HQ1 HQ2 HXYZ.
destruct (AreaQ_diffs U V F K H G X Y HQ1) as [HUV _].
assert (HFM : F <> M) by (intro; treat_equalities; auto).
assert (HKL : K <> L) by (intro; treat_equalities; auto).
assert (HFL : F <> L) by (intro; treat_equalities; auto).
assert (HNC2 : ~ Col K M L) by (intro; apply HNC1; ColR).
assert (HNC3 : ~ Col F L M) by (intro; apply HNC1; ColR).
assert (HNC4 : ~ Col K M J) by (intro; apply HNC2; ColR).
assert (HNC4' : ~ Col F L J) by (intro; apply HNC3; ColR).
assert (HOS1 : OS K M J L) by (apply out_one_side; [left; auto|apply bet_out; auto]).
assert (HOS2 : OS M K J F) by (apply out_one_side; [left; Col|apply bet_out; Between]).
assert (HOS3 : OS K M F L)
  by (apply one_side_transitivity with J; [apply one_side_symmetry, invert_one_side; auto|auto]).
assert (HOS4 : OS F L J M) by (apply out_one_side; [left; auto|apply bet_out; auto]).
assert (HOS5 : OS L F J K) by (apply out_one_side; [left; Col|apply bet_out; Between]).
assert (HOS6 : OS F L K M)
  by (apply one_side_transitivity with J; [apply one_side_symmetry, invert_one_side; auto|auto]).
assert (HNC5 : ~ Col F L H) by (apply (one_side_not_col124 F L K H), l9_17 with M; auto).
assert (HNC6 : ~ Col K M G) by (apply (one_side_not_col124 K M F G), l9_17 with L; auto).
assert (HT1 : ~ Col F H K) by (intro; apply HNC1; ColR).
assert (HT2 : ~ Col F H G) by (intro; apply HNC5; ColR).
assert (HT3 : ~ Col G M H) by (intro; apply HNC6; ColR).
assert (HT4 : ~ Col G M L) by (intro; apply HNC3; ColR).
assert (HT5 : ~ Col F M H) by (intro; apply HNC1; ColR).
assert (HT6 : ~ Col F M G) by (intro; apply HNC3; ColR).
assert (HT7 : ~ Col K M F) by Col.
destruct (inner_pasch F K L G J) as [x1 [Hx1 Hx1']]; auto.
destruct (inner_pasch G M K x1 H) as [x2 [Hx2 Hx2']]; [auto|Between|].
assert (HFx1M : Bet F x1 M) by (apply between_exchange4 with J; Between).
assert (HFx2M : Bet F x2 M) by (apply between_exchange2 with x1; auto).
destruct (AreaT_exists U V F H K) as [p1 [q1 Ha]]; auto.
destruct (segment_construction Y X p1 q1) as [P1 [_ HXP1]].
assert (Ha' : AreaT U V F H K X P1) by (apply AreaT_cong with p1 q1; Cong).
destruct (AreaT_exists U V F M H) as [p2 [q2 Hu]]; auto.
destruct (segment_construction X P1 p2 q2) as [P2 [HXP1P2 HP1P2]].
assert (Hu' : AreaT U V F M H P1 P2) by (apply AreaT_cong with p2 q2; Cong).
destruct (AreaT_exists U V F M G) as [p3 [q3 Hv]]; auto.
destruct (segment_construction P1 P2 p3 q3) as [P3 [HP1P2P3 HP2P3]].
assert (Hv' : AreaT U V F M G P2 P3) by (apply AreaT_cong with p3 q3; Cong).
destruct (AreaT_exists U V G M L) as [p4 [q4 Hd]]; auto.
destruct (segment_construction P2 P3 p4 q4) as [Z' [HP2P3Z' HP3Z']].
assert (Hd' : AreaT U V G M L P3 Z') by (apply AreaT_cong with p4 q4; Cong).
destruct (AreaT_exists U V F H G) as [p5 [q5 Hb]]; auto.
destruct (segment_construction X P1 p5 q5) as [Q2 [HXP1Q2 HP1Q2]].
assert (Hb' : AreaT U V F H G P1 Q2) by (apply AreaT_cong with p5 q5; Cong).
destruct (AreaT_exists U V G M H) as [p6 [q6 Hc]]; auto.
destruct (segment_construction P1 Q2 p6 q6) as [Q3 [HP1Q2Q3 HQ2Q3]].
assert (Hc' : AreaT U V G M H Q2 Q3) by (apply AreaT_cong with p6 q6; Cong).
destruct (segment_construction Q2 Q3 p4 q4) as [W [HQ2Q3W HQ3W]].
assert (Hd'' : AreaT U V G M L Q3 W) by (apply AreaT_cong with p4 q4; Cong).
destruct (AreaT_diffs U V F M H P1 P2 Hu') as [_ HP1P2'].
destruct (AreaT_diffs U V F M G P2 P3 Hv') as [_ HP2P3'].
destruct (AreaT_diffs U V F H G P1 Q2 Hb') as [_ HP1Q2'].
destruct (AreaT_diffs U V G M H Q2 Q3 Hc') as [_ HQ2Q3'].
assert (HS1 : AreaQ U V F K H G X Q2) by (apply B8_4 with P1; auto).
assert (HS2 : AreaQ U V G H M L Q2 W) by (apply B8_4 with Q3; auto).
assert (Hb'' : AreaT U V H G F P1 Q2)
  by (apply AreaT_EqT with F H G; [auto|destruct (B6_3 F H G); spliter; auto]).
assert (Hc'' : AreaT U V H G M Q2 Q3)
  by (apply AreaT_EqT with G M H; [auto|destruct (B6_3 G M H); spliter; auto]).
assert (HS3 : AreaQ U V H F G M P1 Q3)
  by (apply B8_4 with Q2; [exists x2; split; Between|Col|Col|auto..]).
assert (HS4 : AreaQ U V F H M G P1 P3)
  by (apply B8_4 with P2; [exists x2; split; Between|auto..]).
assert (HS5 : Cong P1 P3 P1 Q3).
  {
  apply (B8_3_Q U V F H M G H F G M P1 P3 P1 Q3); [left; auto|left; Col|auto|auto|].
  apply EqQ_perm; [exists x2; split; Between|auto|auto].
  }
assert (Hu'' : AreaT U V F H M P1 P2)
  by (apply AreaT_EqT with F M H; [auto|destruct (B6_3 F M H); spliter; auto]).
assert (HS6 : AreaQ U V F K H M X P2)
  by (apply B8_4 with P1; [exists H; split; Between|auto|Col|auto..]).
assert (HS6'  : AreaT U V K M F X P2) by (apply (AreaQ_AreaT U V F K H M X P2); auto).
assert (HS6'' : AreaT U V F M K X P2)
  by (apply AreaT_EqT with K M F; [auto|destruct (B6_3 K M F); spliter; auto]).
assert (Hv''  : AreaT U V M G F P2 P3)
  by (apply AreaT_EqT with F M G; [auto|destruct (B6_3 F M G); spliter; auto]).
assert (Hd''' : AreaT U V M G L P3 Z')
  by (apply AreaT_EqT with G M L; [auto|destruct (B6_3 G M L); spliter; auto]).
assert (HS7   : AreaQ U V M F G L P2 Z')
  by (apply B8_4 with P3; [exists G; split; Between|Col|Col|auto..]).
assert (HS7'  : AreaT U V F L M P2 Z') by (apply (AreaQ_AreaT U V M F G L P2 Z'); Col).
assert (HS7'' : AreaT U V F M L P2 Z')
  by (apply AreaT_EqT with F L M; [auto|destruct (B6_3 F L M); spliter; auto]).
assert (HP1P2Z' : Bet P1 P2 Z') by (apply outer_transitivity_between with P3; auto).
assert (HXP2Z' : Bet X P2 Z') by (apply outer_transitivity_between2 with P1; auto).
assert (HS8 : AreaQ U V F K M L X Z')
  by (apply B8_4 with P2; [exists J; split; auto|Col|Col|auto..]).
assert (HS9  : Cong X Y X Q2) by (apply AreaQ_unique with U V F K H G; [left|..]; auto).
assert (HS10 : Cong Y Z Q2 W) by (apply AreaQ_unique with U V G H M L; [left|..]; auto).
assert (HXQ2Q3  : Bet X Q2 Q3) by (apply outer_transitivity_between2 with P1; auto).
assert (HXQ2W   : Bet X Q2 W) by (apply outer_transitivity_between with Q3; auto).
assert (HS11 : Cong X Z X W) by (apply l2_11 with Y Q2; auto).
assert (HP1Q3W  : Bet P1 Q3 W) by (apply outer_transitivity_between2 with Q2; auto).
assert (HP1P3Z' : Bet P1 P3 Z') by (apply outer_transitivity_between2 with P2; auto).
assert (HS12 : Cong P1 W P1 Z') by (apply l2_11 with Q3 P3; [auto|auto|Cong|CongR]).
assert (HP1Q2W : Bet P1 Q2 W) by (apply outer_transitivity_between with Q3; auto).
assert (HXP1W : Bet X P1 W) by (apply outer_transitivity_between with Q2; auto).
assert (HXP1Z' : Bet X P1 Z') by (apply outer_transitivity_between with P2; auto).
assert (HS13 : Cong X W X Z') by (apply l2_11 with P1 P1; Cong).
apply AreaQ_cong with X Z'; [auto|CongR].
Qed.

Lemma paste4 A B C D F G H J K L M P e m :
  EqQ A B m D F K H G -> EqQ D B e C G H M L ->
  Bet A P C -> A <> P -> P <> C -> Bet B P D -> B <> P -> P <> D ->
  Bet K H M -> K <> H -> H <> M -> Bet F G L -> F <> G -> G <> L ->
  Bet B m D -> B <> m -> m <> D -> Bet B e C -> B <> e -> e <> C ->
  Bet F J M -> F <> J -> J <> M -> Bet K J L -> K <> J -> J <> L ->
  EqQ A B C D F K M L.
Proof.
intros HE1 HE2 HAPC HAP HPC HBPD HBP HPD HKHM HKH HHM HFGL HFG HGL
       HBmD HBm HmD HBeC HBe HeC HFJM HFJ HJM HKJL HKJ HJL.
assert (HBD : B <> D) by (intro; treat_equalities; auto).
assert (HBC : B <> C) by (intro; treat_equalities; auto).
assert (HAC : A <> C) by (intro; treat_equalities; auto).
assert (HFM : F <> M) by (intro; treat_equalities; auto).
assert (HKL : K <> L) by (intro; treat_equalities; auto).
assert (HFL : F <> L) by (intro; treat_equalities; auto).
assert (HKM : K <> M) by (intro; treat_equalities; auto).
assert (HN1 := EqQ_ncol A B m D F K H G HE1).
assert (HN2 := EqQ_ncol D B e C G H M L HE2).
assert (HN3 := EqQ_ncol F K H G A B m D (proj1 (EqQ_sym _ _ _ _ _ _ _ _) HE1)).
assert (HN4 := EqQ_ncol G H M L D B e C (proj1 (EqQ_sym _ _ _ _ _ _ _ _) HE2)).
assert (HNC1 : ~ Col B D A) by (destruct HN1 as [HN|HN]; intro; apply HN; ColR).
assert (HNC2 : ~ Col B C D) by (destruct HN2 as [HN|HN]; intro; apply HN; ColR).
assert (HNC3 : ~ Col F K M) by (destruct HN3 as [HN|HN]; intro; apply HN; ColR).
assert (HNC4 : ~ Col A C B) by (intro; apply HNC1; ColR).
assert (HCv1 : Convex F K H G)
  by (destruct HE1 as [_ [_ [_ [_ [_ [_ [_ [_ [_ [[HCv _] _]]]]]]]]]]; auto).
assert (HCv2 : Convex G H M L)
  by (destruct HE2 as [_ [_ [_ [_ [_ [_ [_ [_ [_ [[HCv _] _]]]]]]]]]]; auto).
destruct (AreaT_exists B D B D A) as [X [Y HT1]]; auto.
destruct (AreaT_exists B D B C D) as [p [q HT2]]; auto.
destruct (segment_construction X Y p q) as [W [HXYW HYW]].
assert (HT2' : AreaT B D B C D Y W) by (apply AreaT_cong with p q; Cong).
assert (HQ1  : AreaQ B D A B m D X Y) by (apply (AreaQ_AreaT B D A B m D X Y); auto).
assert (HQ2  : AreaQ B D D B e C Y W) by (apply (AreaQ_AreaT B D D B e C Y W); auto).
assert (HQ3  : AreaQ B D F K H G X Y) by (apply AreaQ_EqQ with A B m D; auto).
assert (HQ4  : AreaQ B D G H M L Y W) by (apply AreaQ_EqQ with D B e C; auto).
assert (HQ5  : AreaQ B D F K M L X W) by (apply (B8_4_quad2 B D F G H J K L M X Y W); auto).
assert (HT3  : AreaT B D D B A X Y)
  by (apply AreaT_EqT with B D A; [auto|destruct (B6_3 B D A); spliter; auto]).
assert (HT4 : AreaT B D D B C Y W)
  by (apply AreaT_EqT with B C D; [auto|destruct (B6_3 B C D); spliter; auto]).
assert (HQ6 : AreaQ B D D A B C X W)
  by (apply B8_4 with Y; [exists P; split; Between|Col|Col|auto..]).
assert (HQ7 : AreaQ B D A B C D X W)
  by (apply AreaQ_rot; [exists P; split; Between|left; Col|left; auto|auto]).
apply (B8_3_Q B D A B C D F K M L X W X W); [left; auto|left; Col|auto|auto|Cong].
Qed.

Lemma EqQ_bet__EqT A B C D a b c d :
  ~ Col A B D -> ~ Col a b d -> Bet B C D -> Bet b c d ->
  EqQ A B C D a b c d -> EqT A B D a b d.
Proof.
intros HNC1 HNC2 HB1 HB2 HQ.
assert (HAB : A <> B) by (intro; subst; apply HNC1; Col).
assert (HNC3 : ~ Col A C B \/ ~ Col A C D).
  {
  destruct (col_dec A C B) as [HCol|]; [right; intro|left; auto].
  assert (HAC : A <> C) by (intro; subst; apply HNC1; Col).
  apply HNC1; ColR.
  }
assert (HNC4 : ~ Col a c b \/ ~ Col a c d).
  {
  destruct (col_dec a c b) as [HCol|]; [right; intro|left; auto].
  assert (Hac : a <> c) by (intro; subst; apply HNC2; Col).
  apply HNC2; ColR.
  }
destruct (AreaQ_exists A B A B C D) as [X [Y HA1]]; [auto|exists C; split; Between|auto|].
assert (HA2 : AreaQ A B a b c d X Y) by (apply AreaQ_EqQ with A B C D; auto).
apply (AreaQ_AreaT A B A B C D X Y) in HA1; [|Col|auto].
apply (AreaQ_AreaT A B a b c d X Y) in HA2; [|Col|auto].
assert (HT : EqT B D A b d a) by (apply (B8_3_T A B B D A b d a X Y X Y); Cong).
assert (HNC5 : ~ Col B D A) by Col.
assert (HNC6 : ~ Col b d a) by Col.
apply EqT_trans with B D A; [destruct (B6_3 A B D) as [HT' _]; auto|].
apply EqT_trans with b d a; [auto|destruct (B6_3 b d a) as [_ [_ [HT' _]]]; auto].
Qed.

End Beeson.