Require Import GeoCoq.Main.Tarski_dev.Ch16_coordinates.
Require Import GeoCoq.Main.Highschool.orthocenter.

Section Beeson.

Context `{TE:Tarski_euclidean}.

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
assert (HCongA1 : CongA a b c A B' C').
  {
  apply cong3_conga; [auto|assert_diffs; auto|].
  split; [Cong|split; [Cong|]].
  apply l10_12 with a A; Cong; Perp.
  cut (Perp A B' A C'); Perp.
  apply perp_col4 with A B A C; Col; Perp; assert_diffs; auto.
  }
assert (HCongA2 : CongA a b' c' A B C).
  {
  apply cong3_conga; [assert_diffs; auto| |].
  - intro; treat_equalities; apply HNC; ColR.
  - split; [Cong|split; [Cong|]].
  apply l10_12 with a A; Cong; Perp.
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
assert (HNC2 : ~ Col A2 B2 C2) by (apply perp_not_col; Perp).
assert (HOS1 : OS A1 B1 C1 C) by (apply out_one_side_1 with A1; Col).
assert (HOS2 : OS A1 C1 B1 B) by (apply out_one_side_1 with A1; Col).
assert (HCongA1 : CongA A2 B2 C2 A1 B C).
  {
  apply cong3_conga; [auto|assert_diffs; auto|].
  split; [Cong|split; [Cong|]].
  apply l10_12 with A2 A1; Cong; Perp.
  cut (Perp A1 B A1 C); Perp.
  apply perp_col4 with A1 B1 A1 C1; Col; Perp; assert_diffs; auto.
  }
assert (HCongA2 : CongA B2 C2 A2 B C A1).
  {
  apply cong3_conga; [assert_diffs; auto|auto|].
  split; [|split; Cong].
  apply l10_12 with A2 A1; Cong; Perp.
  cut (Perp A1 B A1 C); Perp.
  apply perp_col4 with A1 B1 A1 C1; Col; Perp; assert_diffs; auto.
  }
assert (HCongA3 : CongA B1 C1 A1 B C A1)
  by (apply (l12_22_a C1 B1 C B A1); Par).
assert (HCongA4 : CongA C1 B1 A1 C B A1)
  by (apply (l12_22_a B1 C1 B C A1); Par).
split; [apply conga_trans with A1 B C|]; CongA.
apply conga_trans with A1 C B; CongA.
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
assert (HCongA1 : CongA C1 B1 A1 C  B  A).
  {
  destruct (l11_49 B1 A1 C1 B A C) as [_ HCA]; [|CongR..|].
  - apply l11_16; Perp; assert_diffs; auto.
  - destruct HCA as [HCA _]; [assert_diffs; auto|CongA].
  }
assert (HCongA2 : CongA C3 B3 A1 C' B' A).
  {
  assert (HPer3 : Per B3 A1 C3)
    by (apply col_col_per_per with B1 C1; Col; Perp).
  assert (HPer4 : Per B' A C').
    {
    cut (Perp A B' A C'); Perp.
    apply perp_col4 with A B A C; Col; [assert_diffs; auto..|exists A; Perp].
    }
  destruct (l11_49 B3 A1 C3 B' A C') as [_ HCA]; [|CongR..|].
  - apply l11_16; Perp; assert_diffs; auto.
  - destruct HCA as [HCA _]; [|CongA].
    apply per_distinct with A1; Perp.
    assert_diffs; auto.
  }
apply conga_trans with C  B  A; CongA.
apply conga_trans with C' B' A; CongA.
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
assert (HNC3 : ~ Col A1 B2' C2').
  {
  apply perp_not_col.
  apply perp_col4 with A1 B1 A1 C1; Col; Perp; assert_diffs; auto.
  }
assert (HCongA1 : CongA A1 B4 C4 A2 B3' C3').
  {
  apply cong3_conga; [assert_diffs; auto| |].
  - intro; treat_equalities; apply HNC1; ColR.
  - split; [|split]; [CongR..|].
    apply l10_12 with A1 A2; [| |CongR..]; apply perp_per_1.
    + assert (HA1B4 : A1 <> B4) by (assert_diffs; auto).
      assert (HA1C4 : A1 <> C4) by (assert_diffs; auto).
      apply perp_col4 with A1 B1 A1 C1; Col; Perp.
    + assert (HA2B3' : A2 <> B3') by (assert_diffs; auto).
      assert (HA2C3' : A2 <> C3') by (assert_diffs; auto).
      apply perp_col4 with A2 B2 A2 C2; Col; Perp.
  }
assert (HCongA2 : CongA A1 B2' C2' A2 B2 C2).
  {
  apply cong3_conga; [assert_diffs; auto| |].
  - intro; treat_equalities; apply HNC3; ColR.
  - split; [|split]; [CongR..|].
    apply l10_12 with A1 A2; [| |CongR..]; apply perp_per_1; Perp.
    assert (HA1B2' : A1 <> B2') by (assert_diffs; auto).
    assert (HA1C2' : A1 <> C2') by (assert_diffs; auto).
    apply perp_col4 with A1 B1 A1 C1; Col; Perp.
  }
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
intros HEQ1 HEQ2.
assert (HD : A1 <> A2 /\ B1 <> B2 /\
             C1 <> C2 /\ D1 <> D2 /\
             E1 <> E2 /\ F1 <> F2).
  {
  apply EqF_diffs in HEQ1; apply EqF_diffs in HEQ2.
  spliter; repeat (split; auto).
  }
destruct HD as [HDA [HDB [HDC [HDD [HDE HDF]]]]].
destruct HEQ1 as [A  [B  [C  [a  [b  [c  HEQ1]]]]]].
destruct HEQ2 as [A' [B' [C' [a' [b' [c' HEQ2]]]]]].
destruct HEQ1 as [HC1 [HC2 [HC3 [HC4 HEQ1]]]].
destruct HEQ2 as [HC5 [HC6 [HC7 [HC8 HEQ2]]]].
assert (HAB : A <> B) by (intro; treat_equalities; auto).
destruct (segment_construction_3 A B E1 E2 HAB HDE) as [B'' [HO1 HC9 ]].
assert (HAC : A <> C) by (intro; treat_equalities; auto).
destruct (segment_construction_3 A C F1 F2 HAC HDF) as [C'' [HO2 HC10]].
exists A, B, C, A, B'', C''; do 4 (split; Cong).
assert (HPer1 : Perp_at A A B A C)
  by (destruct HEQ1 as [? [? HEQ1]]; spliter; auto).
exists B'', C''; do 4 (split; Cong); split; [Perp|].
destruct HEQ1 as [B''' [C''' [HC11 [HO3 [HC12 [HO4 [_ HPar1]]]]]]].
apply par_trans with B''' C'''; Par.
destruct HEQ2 as [B'''' [C'''' [HC13 [HO5 [HC14 [HO6 [HPer2 HPar2]]]]]]].
assert (HNC : ~ Col A B C) by (apply perp_not_col; Perp).
assert (HOS : OS A B''' C''' C'').
  {
  apply out_one_side_1 with A; Col; [intro; apply HNC; ColR|].
  apply l6_7 with C; [apply l6_6|]; auto.
  }
cut (CongA C''' B''' A C'' B'' A);
[apply l12_22_b; auto; apply l6_7 with B; [apply l6_6|]; auto|].
assert (HCongA1 : CongA A B'' C'' A' B'''' C'''').
  {
  apply cong3_conga; [assert_diffs; auto| |].
  - intro; treat_equalities; apply HNC; ColR.
  - split; [|split]; [CongR..|].
    apply l10_12 with A A'; [| |CongR..]; apply perp_per_1.
    + assert (HA1B4 : A <> B'') by (assert_diffs; auto).
      assert (HA1C4 : A <> C'') by (assert_diffs; auto).
      apply perp_col4 with A B A C; Col; Perp.
    + assert (HA2B3' : A' <> B'''') by (assert_diffs; auto).
      assert (HA2C3' : A' <> C'''') by (assert_diffs; auto).
      apply perp_col4 with A' B' A' C'; Col; apply l8_14_2_1a with A'; Perp.
  }
assert (HCongA2 : CongA A B''' C''' A' B' C').
  {
  apply cong3_conga; [assert_diffs; auto| |].
  - intro; treat_equalities; apply HNC; ColR.
  - split; [|split]; [CongR..|].
    apply l10_12 with A A'; [| |CongR..]; apply perp_per_1.
    + assert (HA1B4 : A <> B''') by (assert_diffs; auto).
      assert (HA1C4 : A <> C''') by (assert_diffs; auto).
      apply perp_col4 with A B A C; Col; Perp.
    + assert (HA2B3' : A' <> B') by (assert_diffs; auto).
      assert (HA2C3' : A' <> C') by (assert_diffs; auto).
      apply perp_col4 with A' B' A' C'; Col; apply l8_14_2_1a with A'; Perp.
  }
apply conga_trans with C'''' B'''' A'; [|CongA].
apply conga_trans with C' B' A'; [CongA|].
apply l12_22_a; Par.
apply out_one_side_1 with A'; Col.
apply perp_not_col.
cut (Perp A' B' A' C'); [Perp|].
apply l8_14_2_1a with A'; Perp.
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
  apply col2_os__os with B4 B5; Col; [ColR..|].
  assert (HNC3 : ~ Col C4 B4 B5) by (intro; apply HNC; ColR).
  assert (HNC4 : ~ Col C5 B4 B5)
    by (apply par_strict_not_cols in HParS; spliter; Col).
  elim (cop__one_or_two_sides B4 B5 C4 C5); Cop; intro HTS1; exfalso.
  assert (HOS1 : OS C4 C5 B4 B5).
    {
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

Definition is_orthocenter H A B C :=
  ~ Col A B C /\
  exists HA HB, Perp A HA B C /\ Col B C HA /\ Perp B HB A C /\ Col A C HB /\
                Col H A HA /\ Col H B HB.

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
  intro; treat_equalities.
  assert (HPerp3 : Perp A' B A' C)
    by (apply perp_col4 with B D A' C; Col; Perp; assert_diffs; auto).
  assert (HE : inverse_projection_postulate).
    {
    cut tarski_s_parallel_postulate; [|intro; apply euclid].
    apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
    simpl; tauto.
    }
  assert (HBet : Bet O B C \/ Bet O C B)
    by (destruct HO2 as [_ [_ [|]]]; Between).
  destruct HBet as [HBet|HBet].
  - destruct (midpoint_existence A' B) as [M HM].
    assert (HC'' := HE M B O A' C).
    assert (HAcute : Acute M B O).
      {
      apply acute_sym, acute_out2__acute with O A'.
      - apply out_trivial; auto.
      - split; [assert_diffs; auto|].
        split; [assert_diffs|]; Between.
      - apply l11_43_aux; auto.
        cut (Perp O A' O B); Perp.
        apply perp_col4 with O A' O A; Col; Perp.
      }
    assert (HO5 : Out B M A').
      {
      split; [assert_diffs; auto|].
      split; [assert_diffs|]; Between.
      }
    assert (HPer : Per B A' C) by Perp.
    assert (HCop3 : Coplanar M B O C) by Cop.
    destruct (HC'' HAcute HO5 HA'C HPer HCop3) as [C'' [HO6 HCol]].
    cut (C = C'');
    [intro; treat_equalities; apply l6_4_1 in HO6; destruct HO6; auto|].
    apply (l6_21 A' C O B); Col.
  - destruct (midpoint_existence A' C) as [M HM].
    assert (HB'' := HE M C O A' B).
    assert (HAcute : Acute M C O).
      {
      apply acute_sym, acute_out2__acute with O A'.
      - apply out_trivial; auto.
      - split; [assert_diffs; auto|].
        split; [assert_diffs|]; Between.
      - apply l11_43_aux; auto.
        cut (Perp O A' O C); Perp.
        apply perp_col4 with O A' O A; Col; Perp; ColR.
      }
    assert (HO5 : Out C M A').
      {
      split; [assert_diffs; auto|].
      split; [assert_diffs|]; Between.
      }
    assert (HA'B : A' <> B) by (assert_diffs; auto).
    assert (HPer : Per C A' B) by Perp.
    assert (HCop3 : Coplanar M C O B) by Cop.
    destruct (HB'' HAcute HO5 HA'B HPer HCop3) as [B'' [HO6 HCol]].
    cut (B = B'');
    [intro; treat_equalities; apply l6_4_1 in HO6; destruct HO6; auto|].
    apply (l6_21 A' B O C); Col; intro; apply HNC; ColR.
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
  apply cop_par_perp__perp with A' B; Par.
  apply coplanar_pseudo_trans with O C A'; Col; Cop.
  cut (Col O A C); [Cop|ColR].
  }
assert (HB'D' : B' <> D').
  {
  intro; treat_equalities.
  assert (HE : inverse_projection_postulate).
    {
    cut tarski_s_parallel_postulate; [|intro; apply euclid].
    apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
    simpl; tauto.
    }
  assert (HBet : Bet O A C \/ Bet O C A).
    {
    cut (Out O A C); [|apply l6_7 with B; auto].
    intros [_ [_ [|]]]; Between.
    }
  destruct HBet as [HBet|HBet].
  - destruct (midpoint_existence B' A) as [M HM].
    assert (HC'' := HE M A O B' C).
    assert (HAcute : Acute M A O).
      {
      apply acute_sym, acute_out2__acute with O B'.
      - apply out_trivial; auto.
      - split; [assert_diffs; auto|].
        split; [assert_diffs|]; Between.
      - apply l11_43_aux; auto.
        cut (Perp O A O B'); Perp.
        apply perp_col4 with O A O A'; Col; Perp.
      }
    assert (HO5 : Out A M B').
      {
      split; [assert_diffs; auto|].
      split; [assert_diffs|]; Between.
      }
    assert (HPer : Per A B' C) by Perp.
    assert (HCop3 : Coplanar M A O C) by Cop.
    assert (HB'C : B' <> C) by (assert_diffs; auto).
    destruct (HC'' HAcute HO5 HB'C HPer HCop3) as [C'' [HO6 HCol]].
    cut (C = C'');
    [intro; treat_equalities; apply l6_4_1 in HO6; destruct HO6; auto|].
    apply (l6_21 B' C O A); Col; intro; apply HNC; ColR.
  - destruct (midpoint_existence B' C) as [M HM].
    assert (HB'' := HE M C O B' A).
    assert (HAcute : Acute M C O).
      {
      apply acute_sym, acute_out2__acute with O B'.
      - apply out_trivial; auto.
      - split; [assert_diffs; auto|].
        split; [assert_diffs|]; Between.
      - apply l11_43_aux; auto.
        cut (Perp O B' O C); Perp.
        apply perp_col4 with O A' O A; Col; Perp; ColR.
      }
    assert (HO5 : Out C M B').
      {
      split; [assert_diffs; auto|].
      split; [assert_diffs|]; Between.
      }
    assert (HB'A : B' <> A) by (assert_diffs; auto).
    assert (HPer : Per C B' A) by Perp.
    assert (HCop3 : Coplanar M C O A) by Cop.
    destruct (HB'' HAcute HO5 HB'A HPer HCop3) as [A'' [HO6 HCol]].
    cut (A = A'');
    [intro; treat_equalities; apply l6_4_1 in HO6; destruct HO6; auto|].
    apply (l6_21 B' A O C); Col; intro; apply HNC; ColR.
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
  intro; treat_equalities.
  assert (HE : inverse_projection_postulate).
    {
    cut tarski_s_parallel_postulate; [|intro; apply euclid].
    apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
    simpl; tauto.
    }
  assert (HBet : Bet O A B \/ Bet O B A)
    by (destruct HO1 as [_ [_ [|]]]; Between).
  destruct HBet as [HBet|HBet].
  - destruct (midpoint_existence C' A) as [M HM].
    assert (HC'' := HE M A O C' B).
    assert (HAcute : Acute M A O).
      {
      apply acute_sym, acute_out2__acute with O C'.
      - apply out_trivial; auto.
      - split; [assert_diffs; auto|].
        split; [assert_diffs|]; Between.
      - apply l11_43_aux; auto.
        cut (Perp O A O C'); Perp.
        apply perp_col4 with O A O A'; Col; Perp.
      }
    assert (HO5 : Out A M C').
      {
      split; [assert_diffs; auto|].
      split; [assert_diffs|]; Between.
      }
    assert (HPer : Per A C' B) by Perp.
    assert (HCop3 : Coplanar M A O B) by Cop.
    assert (HC'B : C' <> B) by (assert_diffs; auto).
    destruct (HC'' HAcute HO5 HC'B HPer HCop3) as [B'' [HO6 HCol]].
    cut (B = B'');
    [intro; treat_equalities; apply l6_4_1 in HO6; destruct HO6; auto|].
    apply (l6_21 B C' O A); Col; intro; apply HNC; ColR.
  - destruct (midpoint_existence C' B) as [M HM].
    assert (HB'' := HE M B O C' A).
    assert (HAcute : Acute M B O).
      {
      apply acute_sym, acute_out2__acute with O C'.
      - apply out_trivial; auto.
      - split; [assert_diffs; auto|].
        split; [assert_diffs|]; Between.
      - apply l11_43_aux; auto.
        cut (Perp O B O C'); Perp.
        apply perp_col4 with O A O A'; Col; Perp; ColR.
      }
    assert (HO5 : Out B M C').
      {
      split; [assert_diffs; auto|].
      split; [assert_diffs|]; Between.
      }
    assert (HB'A : C' <> A) by (assert_diffs; auto).
    assert (HPer : Per B C' A) by Perp.
    assert (HCop3 : Coplanar M B O A) by Cop.
    destruct (HB'' HAcute HO5 HB'A HPer HCop3) as [A'' [HO6 HCol]].
    cut (A = A'');
    [intro; treat_equalities; apply l6_4_1 in HO6; destruct HO6; auto|].
    apply (l6_21 C' A O B); Col; intro; apply HNC; ColR.
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
- apply coplanar_pseudo_trans with O C A'; Col; Cop.
  cut (Col O A C); [Cop|ColR].
- apply coplanar_pseudo_trans with O C A'; Col; Cop.
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

Theorem fundamental_thoerem_of_proportion A B C b c :
  ~ Col A B C -> Out A B b -> Out A C c -> Par B C b c -> EqF A B A b A C A c.
Proof.
intros HNC1 HO1 HO2 HPar; apply interchange_theorem.
assert (HD : A <> B /\ A <> b /\ A <> C /\ A <> c) by (assert_diffs; auto).
destruct HD as [HAB [HAb [HAC HAc]]].
destruct (ex_perp_cop A B A C HAB) as [E [HPerp HCop1]].
assert (HAE : A <> E) by (assert_diffs; auto).
destruct (segment_construction_3 A E A C HAE HAC) as [D [HO3 HC1]].
destruct (segment_construction_3 A E A c HAE HAc) as [d [HO4 HC2]].
assert (HAD : A <> D) by (assert_diffs; auto).
assert (HO5 : Out A D d) by (apply l6_7 with E; [apply l6_6|]; auto).
exists A, B, D, A, b, d; do 4 (split; Cong); exists b, d; do 4 (split; Cong).
split; [cut (Perp A B A D); Perp; apply perp_col4 with A B A E; Col; Perp|].
assert (HNC2 : ~ Col A B E)
  by (apply perp_not_col2 in HPerp; destruct HPerp; Col).
assert (HCop : Coplanar A B C D) by CopR.
assert (HBD : B <> D).
  {
  assert (HF : Perp A B A D) by (apply perp_col4 with A B A E; Col; Perp).
  apply perp_not_col2 in HF; destruct HF; [Col|assert_diffs; auto].
  }
assert (HAd : A <> d)  by (assert_diffs; auto).
assert (Hbd : b <> d).
  {
  assert (HF : Perp A b A d) by (apply perp_col4 with A B A E; Col; Perp).
  apply perp_not_col2 in HF; destruct HF; [Col|assert_diffs; auto].
  }
assert (HSL : b <> c -> Col B b c -> Col C b c -> Par B D b d).
  {
  intros Hbc HCol1 HCol2.
  elim (eq_dec_points B b).
  - intro; treat_equalities; right; do 3 (split; Col).
    assert (HCc : C = c) by (apply (l6_21 A C B C); Col; assert_diffs; auto).
    treat_equalities; cut (D = d); [intro; treat_equalities; Col|].
    apply (l6_11_uniqueness A A C D); [apply out_trivial| |apply l6_6|]; Cong.
  - intro; exfalso; apply Hbc.
    assert (HBC : B <> C) by (assert_diffs; auto).
    apply (l6_21 A B C B); Col; ColR.
  }
destruct HPar as [HParS1|[? [? []]]]; [clear HSL|apply HSL; Col].
assert (HSL : Col A C D -> Par B D b d).
  {
  intro HCol; assert (HE : C = D /\ c = d \/ Midpoint A C D /\ Midpoint A c d).
    {
    destruct (l7_20 A C D) as [|HMid]; Col; Cong; treat_equalities.
    - left; split; auto.
      apply (l6_11_uniqueness A A c c); Cong; [apply out_trivial; auto|].
      apply l6_7 with C; [apply l6_6|]; auto.
    - right; split; auto; split; Cong; destruct HMid as [HBet HC3].
      apply (bet_out__bet C); auto.
      apply between_symmetry, (bet_out__bet D); Between.
    }
  destruct HE as [[]|[HMid1 HMid2]]; treat_equalities; Par.
  assert (HOS : OS A B D d)
    by (apply (out_one_side_1 _ _ _ _ A); Col; intro; apply HNC2; ColR).
  apply (l12_22_b B D b d A); auto.
  assert (HCongA1 : CongA D A B C A B).
    {
    apply conga_left_comm, conga_right_comm.
    apply l11_18_1; Between; cut (Perp A B A D); Perp.
    apply perp_col4 with A B A E; Col; Perp.
    }
  assert (HCongA2 : CongA D B A C B A).
    {
    apply l11_49 in HCongA1; Cong.
    destruct HCongA1 as [_ HCongA1].
    assert (HDB : D <> B) by auto.
    destruct (HCongA1 HDB); CongA.
    }
  apply conga_trans with C B A; CongA.
  assert (HCongA3 : CongA d A b c A b).
    {
    apply conga_left_comm, conga_right_comm.
    apply l11_18_1; Between; cut (Perp A b A d); Perp.
    apply perp_col4 with A B A E; Col; Perp.
    }
  assert (HCongA4 : CongA d b A c b A).
    {
    apply l11_49 in HCongA3; Cong.
    destruct HCongA3 as [_ HCongA3].
    assert (Hdb : d <> b) by auto.
    destruct (HCongA3 Hdb); CongA.
    }
  apply conga_trans with c b A; CongA.
  apply l12_22_a; Par; apply (out_one_side_1 _ _ _ _ A); Col.
  }
elim (col_dec A C D); [auto|clear HSL; intro HNC3].
assert (HParS2 : Par_strict C D c d).
  {
  assert (HPar : Par C D c d) by (apply (out2_cong2_par A); Cong).
  apply par_not_col_strict with c; Col; intro HF.
  assert (HNC4 : ~ Col B C c) by (apply (par_strict_not_col_3 _ b); Par).
  assert (HCc : C <> c) by (assert_diffs; auto).
  apply HCc; apply (l6_21 A C D C); Col; assert_diffs; auto.
  }
assert (HSL : Col B C D -> Par B D b d).
  {
  intro HCol1; assert (HD : B <> C /\ c <> d) by (assert_diffs; auto).
  destruct HD as [HBC Hcd].
  assert (HPar : Par B C c d) by (apply par_col4__par with C D c d; Col; Par).
  destruct (parallel_uniqueness B C b c c d c) as [HCol2 HCol3]; Col; Par.
  apply par_col4__par with B C c d; Col.
  }
elim (col_dec B C D); [auto|clear HSL; intro HNC4].
apply (l13_15 C B D c b d A); Col; Par.
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
apply interchange_theorem, fundamental_thoerem_of_proportion; auto.
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
  apply fundamental_thoerem_of_proportion; Col.
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

Lemma B5_2_1_1 A B C D a b c d :
  Rectangle A B C D -> Rectangle a b c d ->
  EqR A B C D a b c d -> EqF A B a b b c B C.
Proof.
intros RABCD Rabcd HR.
assert (HD : A <> B /\ a <> b /\ B <> C /\ b <> c)
  by (apply EqR_diffs in HR; spliter; auto).
destruct HD as [HNbc [HNBC [HNab HNAB]]].
destruct HR as [_ [_ [HR1 [_ [_ [HR2 HR]]]]]].
destruct HR as [I [J [E [F [G [H [K [L [M HR]]]]]]]]]; spliter.
assert_diffs.
assert (HPlg1 : Parallelogram I J M L) by (apply Rectangle_Parallelogram; auto).
assert (HPlg2 : Parallelogram J E F G) by (apply Rectangle_Parallelogram; auto).
assert (HR3 : Rectangle I J M L) by auto.
apply rect_per in HR3; spliter.
assert (HR4 : Rectangle J E F G) by auto.
apply rect_per in HR4; spliter.
assert_diffs.
assert (HNJG : J <> G).
  intro; treat_equalities; apply rect_comm2 in H3; apply degenerated_rect_eq in H3; auto.

assert (HNIL : I <> L).
  intro; treat_equalities.
  apply rect_permut in H0; apply rect_permut in H0; apply degenerated_rect_eq in H0; auto.

assert (HNLM : L <> M).
  intro; treat_equalities; apply rect_permut in H0; apply degenerated_rect_eq in H0; auto.

assert (HNFG : F <> G).
  intro; treat_equalities; apply rect_permut in H3; apply degenerated_rect_eq in H3; auto.

assert (HPar : Par G F J E) by (apply plg_par_2; auto ; apply plg_permut; apply plg_sym; auto).
assert (HPar2 : Par J M I L) by (apply plg_par_2; auto; apply plg_comm2; auto).
assert (HPar3 : Par J G E F) by (apply plg_par_2; auto).
assert (HPar4 : Par J I M L)
  by (apply plg_par_2; auto; apply plg_permut; apply plg_comm2; apply plg_comm2; auto).


assert (HNIH : I <> H).
  {
  intro; treat_equalities.
  assert (HBet1 : Col I G F) by (apply bet_col; auto).
  assert (HBet2 : Col I J E) by (apply bet_col; auto).
  destruct (col2_par__col4 G F E J I) as [HC1 [HC2 [HC3 HC4]]]; Col.
  apply par_right_comm; auto.
  cut (~ Col E F G); Col.
  apply per_not_col; [assert_diffs; auto..|]; auto.
  }
assert (HNHG : G <> H).
  {
  intro; treat_equalities.
  assert (HBet1 : Col G J M) by (apply bet_col; auto).
  assert (HBet2 : Col G I L) by (apply bet_col; auto).
  destruct (col2_par__col4 J M I L G) as [HC1 [HC2 [HC3 HC4]]]; Col.
  cut (~ Col I L M); Col.
  apply per_not_col; [assert_diffs; auto..|]; auto.
  }

assert (HNMK : M <> K).
  {
  intro; treat_equalities.
  assert (HBet1 : Col M J G) by (apply bet_col; apply between_symmetry; auto).
  assert (HBet2 : Col M E F) by (apply bet_col; apply between_symmetry; auto).
  destruct (col2_par__col4 J G E F M) as [HC1 [HC2 [HC3 HC4]]]; Col.
  cut (~ Col G F E); Col.
  apply per_not_col; [assert_diffs; auto..|]; Perp.
  }

assert (HNEK : E <> K).
  {
  intro; treat_equalities.
  assert (HBet1 : Col E J I) by (apply bet_col; apply between_symmetry; auto).
  assert (HBet2 : Col E M L) by (apply bet_col; auto).
  destruct (col2_par__col4 J I M L E) as [HC1 [HC2 [HC3 HC4]]]; Col.
  cut (~ Col L M J); Col.
  apply per_not_col; [assert_diffs; auto..|]; Perp.
  }

assert (HNHJ : J <> H).
  {
  intro; treat_equalities.
  assert (HBet1 : Col J G F) by (apply bet_col; auto).
  cut (~ Col J G F); Col.
  apply per_not_col; [assert_diffs; auto..|].
  auto.
  }

assert (HNJK : J <> K).
  {
  intro; treat_equalities.
  assert (HBet1 : Col F E J) by (apply bet_col; auto).
  cut (~ Col F E J); Col.
  apply per_not_col; [assert_diffs; auto..|]; Perp.
  }

assert (HP1 : Per I J G).
  {
  apply per_suppa__per with M J I.
  apply l8_2; auto.
  apply bet__suppa; auto.
  apply between_symmetry; auto.
  }

assert (HP2 : Per J I H).
  {
  apply per_suppa__per with L I J.
  apply l8_2; auto.
  apply bet__suppa; auto.
  apply between_symmetry; auto.
  }

assert (HP3 : Per J G H).
  {
  apply per_suppa__per with F G J.
  apply l8_2; auto.
  apply bet__suppa; auto.
  apply between_symmetry; auto.
  }

assert (HP4 : Per J M K).
  {
  apply per_suppa__per with L M J.
  apply l8_2; auto.
  apply bet__suppa; auto.
  apply between_symmetry; auto.
  }

assert (HP5 : Per E J M).
  {
  apply per_suppa__per with G J E.
  apply l8_2; auto.
  apply bet__suppa; auto.
  }

assert (HP6 : Per J E K).
  {
  apply per_suppa__per with F E J.
  apply l8_2; auto.
  apply bet__suppa; auto.
  }

assert (HPP1 : Perp I J J G) by (apply per_perp; auto).
assert (HPP2 : Perp J G G H) by (apply per_perp; auto).
assert (HPP3 : Perp H I I J) by (apply per_perp; auto; Perp).
assert (HPP4 : Perp K E E J) by (apply per_perp; auto; Perp).
assert (HPP5 : Perp E J J M) by (apply per_perp; auto).
assert (HPP6 : Perp J M M K) by (apply per_perp; auto).

assert (HPar5 : Par G H I J).
  {
  assert (HCol1 : Col H G F) by (apply bet_col; auto).
  apply par_col_par_2 with F; auto; Col.
  apply par_right_comm.
  apply par_col_par with E; auto; Col.
  }

assert (HPar6 : Par J E M K).
  {
  apply par_col_par_2 with I; auto; Col.
  apply par_col_par with L; auto; Col.
  }

assert (Cop1 : Coplanar H I J G) by Cop.
assert (Cop2 : Coplanar J M K E) by Cop.

assert (HR3 : Rectangle H I J G) by (apply cop_perp3__rect; auto).
assert (HPlg3 : Plg H I J G) by (apply Rectangle_Plg in HR3; auto).

assert (HR4 : Rectangle K E J M) by (apply cop_perp3__rect; auto; Cop).
assert (HPlg4 : Plg K E J M) by (apply Rectangle_Plg in HR4; auto).

assert (HCA1: CongA I H J G J H) by (apply plg_conga1; auto).
assert (HCA2 : CongA G J H M J K) by (apply l11_14; auto).
assert (HCA3 : CongA H J I K J E) by (apply l11_14; auto).
assert (HCA4 : CongA M K J E J K).
  {
  apply plg_conga1; auto.
  apply parallelogram_to_plg.
  apply plg_comm2; apply plg_permut; apply plg_sym.
  apply plg_to_parallelogram; auto.
  }
assert (HCA5: CongA H I J J M K) by (apply l11_16 ;auto; Perp).
assert (HCA6 : CongA I H J M J K) by (apply conga_trans with G J H; auto).
assert (HCA7 : CongA H J I J K M).
  {
  apply conga_trans with E J K; auto.
  apply conga_right_comm; auto.
  apply conga_sym; apply conga_left_comm; auto.
  }

assert (HEQF1 : EqF M K M J I J I H).
  {
  apply CongA2__EqF; auto.
  - destruct (perp_not_col2 _ _ _ _ HPP6) as [|]; Col.
  - apply conga_sym; apply conga_right_comm; apply conga_left_comm; auto.
  - apply conga_sym; apply conga_right_comm; apply conga_left_comm; auto.
  }
apply interchange_theorem in HEQF1.

destruct HEQF1 as [N [O [P [n [o [p HI]]]]]]; spliter.

apply EqF_abcd_badc.
unfold EqF.

assert (HPlg5 : Parallelogram H I J G) by (apply Rectangle_Parallelogram; auto).
assert (HPlg6 : Parallelogram K E J M) by (apply Rectangle_Parallelogram; auto).

assert (HCong1 : Cong I H b c).
  {
  apply plg_cong in HPlg2; spliter.
  apply plg_cong in HPlg5; spliter.
  apply cong_transitivity with J G; Cong.
  apply cong_transitivity with E F; Cong.
  }

assert (HCong2 :  Cong M K a b).
  {
  apply cong_transitivity with J E; Cong.
  apply plg_cong in HPlg6; spliter; Cong.
  }

exists N, O, P, n, o, p.
split.
apply cong_inner_transitivity with M K; Cong.
split.
apply cong_inner_transitivity with I J; Cong.
split.
apply cong_inner_transitivity with M J; Cong.
split.
apply cong_inner_transitivity with I H; Cong.
auto.
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
assert (HAE : A <> E) by (assert_diffs; auto).
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
assert (HPer2 : Per E B G).
  {
  apply per_suppa__per with C B E; auto.
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
assert (HDK : D <> K) by (assert_diffs; auto).
assert (HEF : E <> F) by (assert_diffs; auto).
assert (HEK : E <> K)
  by (intro; treat_equalities; apply per_not_col in HPer1; Col).
assert (HC6 : Cong B E K C) by (apply cong_inner_transitivity with a b; Cong).
assert (HR1 : Rectangle B E K C).
  {
  cut (Parallelogram B E K C).
  - intro HPara; apply plg_per_rect1; Perp.
    apply parallelogram_to_plg; auto.
  - apply sac_plg; split; Perp; split; Perp; split; Cong.
    assert (HNC1 : ~ Col B C E) by (apply per_not_col in HPer1; Col).
    assert (HNC2 : ~ Col B K C) by (apply per_not_col in HPer3; Col).
    assert (HNC3 : ~ Col A B C) by (intro; apply HNC1; ColR).
    assert (HNC4 : ~ Col B C D) by (intro; apply HNC2; ColR).
    assert (HTS1 : TS B C E A).
      {
      split; Col; split; Col.
      exists B; split; Between; Col.
      }
    apply l9_8_1 with A; [Side|].
    assert (HTS2 : TS B C D K).
      {
      split; Col; split; Col.
      exists C; split; Between; Col.
      }
    apply l9_2, l9_8_2 with D; [Side|].
    apply l12_6, par_not_col_strict with A; Col; Par.
  }
assert (HPer4 : Per F E B).
  {
  apply rect_per in HR1; spliter.
  apply per_suppa__per with B E K; Perp.
  apply suppa_sym, bet__suppa; Between.
  }
assert (HR2 : Rectangle B E F G).
  {
  cut (Parallelogram B E F G).
  - intro HPara; apply plg_per_rect1; Perp.
    apply parallelogram_to_plg; auto.
  - do 3 apply plg_permut; apply sac_plg.
    split; Perp; split; Perp; split; [CongR|].
    assert (HNC1 : ~ Col B C E) by (apply per_not_col in HPer1; Col).
    assert (HNC2 : ~ Col B E G) by (apply per_not_col in HPer2; Col).
    assert (HNC3 : ~ Col B E F) by (apply per_not_col in HPer4; Col).
    assert (HNC4 : ~ Col B E K) by (intro; apply HNC3; ColR).
    assert (HTS1 : TS E B C G).
      {
      split; Col; split; Col.
      exists B; split; Between; Col.
      }
    apply l9_8_1 with C; [|Side].
    assert (HTS2 : TS E B F K).
      {
      split; Col; split; Col.
      exists E; split; Between; Col.
      }
    apply l9_2, l9_8_2 with K; [Side|].
    apply l12_6, par_not_col_strict with C; Col.
    apply Rectangle_Parallelogram, plg_par_1 in HR1; Par.
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
  cut (Parallelogram A B G H).
  - intro HPara; apply plg_per_rect1; Perp.
    apply parallelogram_to_plg; auto.

  - do 3 apply plg_permut; apply sac_plg.
    split; Perp; split; Perp; split; [CongR|].
    assert (HAH : A <> H) by (assert_diffs; auto).
    assert (HNC1 : ~ Col B C E) by (apply per_not_col in HPer1; Col).
    assert (HNC2 : ~ Col A B C) by (intro; apply HNC1; ColR).
    assert (HNC3 : ~ Col A B G) by (apply per_not_col in HPer6; Col).
    assert (HNC4 : ~ Col A B H) by (apply per_not_col in HPer5; Col).
    assert (HNC5 : ~ Col A B D) by (intro; apply HNC4; ColR).
    assert (HTS1 : TS A B C G).
      {
      split; Col; split; Col.
      exists B; split; Between; Col.
      }
    apply l9_8_1 with C; [Side|].
    assert (HTS2 : TS A B D H).
      {
      split; Col; split; Col.
      exists A; split; Between; Col.
      }
    apply l9_2, l9_8_2 with D; [Side|].
    apply l12_6, par_not_col_strict with C; Col.
    apply Rectangle_Parallelogram, plg_par_1 in HR1; Par.
  }
assert (HHGF : Bet H G F).
  {
  assert (HHGF : Col H G F).
    {
    apply col_par_par_col with A B E; Col.
    - apply Rectangle_Parallelogram, plg_par_1 in HR3; Par.
    - apply Rectangle_Parallelogram, plg_par_1 in HR2; Par.
    }
  apply col_two_sides_bet with B; Col.
  assert (HOS1 : OS G B A H).
    {
    assert (HGH : G <> H).
      {
      intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR3; auto.
      }
    apply rect_permut, Rectangle_Parallelogram, plg_par_1 in HR3; auto.
    apply pars__os3412, par_not_col_strict with B; Col; Par.
    assert (HAD : A <> D).
      {
      intro; treat_equalities.
      apply rect_permut, rect_permut, degenerated_rect_eq in RABCD; auto.
      }
    apply rect_per1 in RABCD.
    apply per_not_col in RABCD; auto.
    intro; apply RABCD; ColR.
    }
  apply l9_8_2 with A; [|Side].
  assert (HOS2 : OS G B E F).
    {
    assert (HGH : F <> G).
      {
      intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR2; auto.
      }
    apply rect_permut, Rectangle_Parallelogram, plg_par_1 in HR2; auto.
    apply pars__os3412, par_not_col_strict with B; Col; Par.
    apply per_not_col in HPer4; Col.
    }
  apply l9_2, l9_8_2 with E; [|Side].
  assert (HNC1 : ~ Col B E G) by (apply per_not_col in HPer2; Col).
  assert (HNC2 : ~ Col B C E) by (apply per_not_col in HPer1; Col).
  assert (HNC3 : ~ Col A B G) by (intro; apply HNC2; ColR).
  split; Col; split; Col.
  exists B; split; Between; Col.
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
    apply per_not_col; [assert_diffs; auto..|].
    apply rect_per3 with A; auto.
    }
  assert (HNC4 : ~ Col K B C) by (intro; apply HNC3; ColR).
  split; [Col|]; split; [Col|].
  exists C; split; [Col|Between].
  }
cut (Col H B K); [intro HC; apply col_two_sides_bet with C; Col|].
apply interchange_theorem in HE.
clear H1 H2 H3 H4 H5 N O P n o p.
destruct HE as [N [O [P [n [o [p HE]]]]]].
destruct HE as [HC7 [HC8 [HC9 [HC10 HE']]]].
assert (HE : EqF A B A H C K C B)
  by (exists N, O, P, n, o, p; do 4 (split; [CongR|]); auto).
assert (HCongA1 : CongA A H B C B K)
  by (destruct (Per2_EqF__CongA A B H C K B); CongA; Perp).
destruct (point_construction_different H B) as [K' [HK' HBK']].
assert (HCongA2 : CongA A H B C B K').
  {
  apply conga_trans with A H K'.
  - apply out2__conga; [apply out_trivial; assert_diffs; auto|].
    assert_diffs; repeat (split; Between).
  - apply l12_22_a; [assert_diffs; repeat (split; Between)|..].
    + apply l9_8_1 with G.
      * apply invert_two_sides, col_two_sides with B; [|assert_diffs|]; Col.
        assert (HNC : ~ Col A B G)
          by (apply per_not_col; Perp; assert_diffs; auto).
        assert (HPar4 : Par A B G H).
          {
          apply par_col4__par with B E F G; Col.
          - intro; treat_equalities; apply rect_permut in HR3.
            apply degenerated_rect_eq in HR3; auto.
          - apply plg_par_1; [assert_diffs; auto..|].
            apply Rectangle_Parallelogram; auto.
          }
        destruct (l12_19 A B G H) as [_ [_ [HTS' _]]]; Col; Side.
        apply rect_permut in HR3.
        apply plg_par_1; [assert_diffs; auto..|].
        apply Rectangle_Parallelogram; auto.
      * assert (HNC : ~ Col B G H).
          {
          cut (Perp B G G H).
          - intro HP; destruct (perp_not_col2 _ _ _ _ HP); Col.
          - apply perp_col4 with B G G F; Col.
            + intro; treat_equalities.
              apply rect_permut, degenerated_rect_eq in HR3; auto.
            + cut (Per B G F); [apply per_perp; Perp|].
              * intro; treat_equalities.
                apply rect_permut, degenerated_rect_eq in HR2; auto.
              * apply rect_per3 with E; apply rect_comm2; auto.
          }
        split; [intro; apply HNC; ColR|].
        split; [intro; apply HNC; ColR|].
        exists B; split; [Col|Between].
    + apply par_col4__par with A D B C; Col; assert_diffs; auto.
  }
assert (HCongA3 : CongA C B K C B K') by (apply conga_trans with A H B; CongA).
apply conga_os__out in HCongA3; [ColR|].
apply l9_8_1 with H; [Side|].
assert (HNC : ~ Col B C H) by (apply two_sides_not_col with K; Side).
split; [intro; apply HNC; ColR|].
split; [intro; apply HNC; ColR|].
exists B; split; [Col|Between].
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
apply B5_2_1 in HEQR; auto.
apply interchange_theorem in HEQR.
destruct HEQR as [I [J [K [i [j [k HEQR]]]]]]; spliter.
assert (HC2 : Cong I J E F) by (apply cong_inner_transitivity with A B; Cong).
assert (HC3 : Cong I J i j) by (apply cong_inner_transitivity with E F; Cong).
assert (HEQT : EqRT I J K i j k) by auto.
unfold EqRT in H4.
destruct H4 as [M [N [H4]]]; spliter.
assert (HC4 : Cong I J I M) by (apply cong_inner_transitivity with i j; Cong).
apply cong_inner_transitivity with i k; auto.
apply cong_inner_transitivity with I K; auto.
apply cong_inner_transitivity with I N; Cong.
assert (H10 : J = M).
apply l6_11_uniqueness with I I J M; auto; Cong.
apply out_trivial.
intro; treat_equalities; auto.
treat_equalities.
assert (HCol1 : ~ Col I J K) by (apply perp_not_col;apply l8_14_2_1a in H8;Perp).
assert (HKN : K = N).
apply l6_21 with I K J K; Col.
intro; treat_equalities; apply out_col in H5; auto.
CongR.

apply B5_2_1; auto.
apply interchange_theorem.
unfold EqF.
exists B, A, C, B, A, C.
do 4 (split; Cong).
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

Lemma rect2_bet__bet A B C D E F :
  Rectangle A B E D -> Rectangle B C F E ->
  A <> B -> B <> C -> B <> E ->
  Bet A B C -> Bet D E F.
Proof.
intros HR1 HR2 HAB HBC HBE HB.
assert (HCF : C <> F).
  {
  intro; treat_equalities.
  apply degenerated_rect_eq in HR2; auto.
  }
assert (HDE : D <> E).
  {
  intro; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR1; auto.
  }
assert (HEF : E <> F).
  {
  intro; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR2; auto.
  }
apply col_two_sides_bet with B.
- cut (Par E D E F); [apply par_id|].
  apply par_trans with A C.
  + apply par_col4__par with D E A B; Col; [assert_diffs; auto|].
    apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
  + apply par_col4__par with B C E F; Col; [assert_diffs; auto|].
    apply Rectangle_Parallelogram, plg_par in HR2; spliter; Par.
- assert (HNC : ~ Col A B E)
    by (apply per_not_col; auto; apply rect_per2 with D; auto).
  apply l9_8_2 with A; [apply l9_2, l9_8_2 with C|].
  + split; [intro; apply HNC; ColR|].
    split; [intro; apply HNC; ColR|].
    exists B; split; [Col|Between].
  + apply l12_6, par_not_col_strict with C; Col; [|intro; apply HNC; ColR].
    apply Rectangle_Parallelogram, plg_par in HR2; spliter; Par.
  + apply l12_6, par_not_col_strict with A; Col.
    apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
Qed.

Lemma B5_7 A B C D E F a b c d e f :
  Bet B C E -> B <> C -> Bet b c e -> b <> c ->
  EqR D C E F d c e f -> EqR A B E F a b e f ->
  EqR A B C D a b c d.
Proof.
assert (HCut : forall B C E G H I J P Q,
                 B <> C -> C <> E -> G <> H -> H <> I -> H <> P ->
                 Cong G P B C -> Cong G H B E -> Bet B C E -> Bet G P H ->
                 Rectangle G H I J -> Rectangle I H P Q ->
                 Bet J Q I /\ Rectangle J G P Q).
  {
  clear A B C D E F a b c d e f; intros B C E G H I J P Q.
  intros HBC HCE HGH HHI HHP.
  intros HC1 HC2 HB1 HB2 HR1 HR2.
  assert (HGP : G <> P) by (assert_diffs; auto).
  assert (HJQ : J <> Q).
    {
    intro; treat_equalities; apply HGP.
    cut (P = G); [auto|apply between_cong with H; [Between|]].
    cut (Cong G H I J /\ Cong I J H P); [intros []; CongR|split].
    - apply Rectangle_Parallelogram, plg_cong in HR1; spliter; Cong.
    - apply Rectangle_Parallelogram, plg_cong in HR2; spliter; Cong.
    }
  assert (HIQ : I <> Q).
    {
    intro; treat_equalities.
    apply rect_permut, rect_permut, degenerated_rect_eq in HR2; auto.
    }
  assert (HPQ : P <> Q).
    {
    intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR2; auto.
    }
  cut (Bet J Q I); [intro B3; split; [auto|]|].
  - apply plg_per_rect1; [apply parallelogram_to_plg|].
    + do 3 apply plg_permut; apply plg_out_plg with H I.
      * apply Rectangle_Parallelogram; auto.
      * split; [assert_diffs|split]; Between.
      * split; [|split]; Between.
        intro; treat_equalities; auto.
      * cut (Cong P G Q J); [Cong|].
        apply Rectangle_Parallelogram, plg_cong in HR1.
        apply Rectangle_Parallelogram, plg_cong in HR2.
        apply l4_3_1 with H I; Between; spliter; Cong.
    + cut (Perp Q J J G); Perp.
      assert (HGJ : G <> J).
        {
        intro; treat_equalities.
        apply rect_permut, rect_permut, degenerated_rect_eq in HR1; auto.
        }
      apply perp_col4 with I J J G; Col.
      cut (Per I J G); [apply per_perp; assert_diffs; auto|].
      apply rect_per4 with H; do 3 apply rect_permut; apply rect_comm2; auto.
  - assert (HCol : Col I Q J).
      {
      cut (Par I Q I J); [apply par_id|].
      apply par_trans with H G.
      - apply par_col4__par with I Q P H; Col.
        apply plg_par_1; [auto..|].
        apply Rectangle_Parallelogram, rect_permut, rect_comm2; auto.
      - cut (Par G H I J); [Par|apply plg_par_1; auto].
        apply Rectangle_Parallelogram; auto.
      }
    apply col_two_sides_bet with P; [Col|].
    assert (HNC : ~ Col H P Q)
      by (apply per_not_col; auto; apply (rect_per3 I); auto).
    assert (HGJ : G <> J).
      {
      intro; treat_equalities.
      apply rect_permut, rect_permut, degenerated_rect_eq in HR1; auto.
      }
    apply l9_8_2 with G; [apply l9_2, l9_8_2 with H|].
    + split; [intro; apply HNC; ColR|].
      split; [intro; apply HNC; ColR|].
      exists P; split; [Col|Between].
    + apply l12_6, par_not_col_strict with H; [|Col|intro; apply HNC; ColR].
      apply Rectangle_Parallelogram, plg_par in HR2; spliter; Par.
    + apply l12_6, par_not_col_strict with G; [|Col|intro; apply HNC; ColR].
      apply par_trans with H I.
      * apply Rectangle_Parallelogram, plg_par in HR2; spliter; Par.
      * apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
  }
assert (EqRP : forall G H I J K L M N O,
                 EqR G H I J H K L M ->
                 Bet N G J -> Bet N M L -> Bet L K O ->
                 Bet O I J -> Bet G H K -> Bet M H I ->
                 Bet N H O).
  {
  clear A B C D E F a b c d e f; intros G H I J K L M N O.
  intros HE HB1 HB2 HB3 HB4 HB5 HB6.
  destruct HE as [HGH [HHI [HR1 [HHK [HKL [HR2 HE]]]]]].
  destruct HE as [G' [H' [K' [L' [M' [N' [O' [J' [I' HE]]]]]]]]].
  destruct HE as [HR3 [HC1 [HC2 [HR4 [HC3 [HC4 HE]]]]]].
  destruct HE as [HB7 [HB8 [HB9 [HB10 [HB11 [HB12 HB13]]]]]].
  assert (HC5 : Cong O I O' I').
    {
    cut (Cong O I M L /\ Cong O' I' M' L'); [intros [HC5 HC6]|split].
    - apply Rectangle_Parallelogram, plg_cong in HR2.
      apply Rectangle_Parallelogram, plg_cong in HR4; spliter; CongR.
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
    - apply t22_8__cong with K' H'; Between; [|assert_diffs; auto|..].
      + split; [|split; [|split]].
        * apply rect_per2 with K', rect_permut, rect_permut; auto.
        * apply rect_per2 with L'; do 3 apply rect_permut; auto.
        * apply Rectangle_Parallelogram, plg_cong in HR4; spliter; Cong.
        * apply l12_6, ncol234_plg__pars1423.
          -- cut (~ Col H' K' L'); [Col|].
             apply per_not_col; [assert_diffs; auto..|].
             apply rect_per2 with M'; auto.
          -- apply plg_comm2, plg_permut, plg_permut.
             apply Rectangle_Parallelogram; auto.
      + apply l8_3 with H'; Col; [|assert_diffs; auto].
        apply l8_2, l8_3 with J'; Col; [|assert_diffs; auto].
        * apply rect_per1 with G', rect_permut, rect_permut; auto.
        * intro; treat_equalities; apply rect_permut in HR3.
          apply degenerated_rect_eq in HR3; auto.
      + apply rect_per1 with H', rect_permut, rect_permut; auto.
    }
  assert (HC6 : Cong N G N' G').
    {
    assert (HGN   : G  <> J ).
      {
      intro; treat_equalities.
      apply rect_permut, rect_permut, degenerated_rect_eq in HR1; auto.
      }
    assert (HG'N' : G' <> J').
      {
      intro; treat_equalities.
      apply rect_permut, rect_permut, degenerated_rect_eq in HR3.
      treat_equalities; auto.
      }
    assert (HHM   : H  <> M ).
      {
      intro; treat_equalities.
      apply rect_permut, rect_permut, degenerated_rect_eq in HR2; auto.
      }
    assert (HH'M' : H' <> M').
      {
      intro; treat_equalities.
      apply rect_permut, rect_permut, degenerated_rect_eq in HR4.
      treat_equalities; auto.
      }
    assert (HLM   : L  <> M ).
      {
      intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR2; auto.
      }
    assert (HL'M' : L' <> M').
      {
      intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR4.
      treat_equalities; auto.
      }
    cut (Cong N G K L /\ Cong N' G' K' L'); [intros [HC6 HC7]|split].
    - apply Rectangle_Parallelogram, plg_cong in HR2.
      apply Rectangle_Parallelogram, plg_cong in HR4; spliter; CongR.
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
    - apply t22_8__cong with M' H'; Between; [|assert_diffs; auto|..].
      + split; [|split; [|split]].
        * apply rect_per1 with M', rect_permut; auto.
        * apply rect_per4 with L', rect_permut; auto.
        * apply Rectangle_Parallelogram, plg_cong in HR4; spliter; Cong.
        * apply l12_6, ncol234_plg__pars1423.
          -- apply per_not_col; auto.
             apply rect_per2 with K', rect_permut, rect_permut; auto.
          -- apply plg_permut, Rectangle_Parallelogram; auto.
      + apply l8_3 with H'; Col; [|assert_diffs; auto].
        apply l8_2, l8_3 with J'; Col.
        apply rect_per2 with I'; do 3 apply rect_permut; auto.
      + apply rect_per2 with H', rect_permut; auto.
    }
  apply (l4_6 N' H' O'); Between; split; [|split].
  - apply l10_12 with G' G; Cong.
    + elim (eq_dec_points G' N'); [intro; treat_equalities; Perp|intro HG'N'].
      cut (Perp N' G' G' H'); [Perp|].
      apply perp_col4 with J' G' G' H'; Col; [assert_diffs; auto|].
      cut (Per J' G' H'); [apply per_perp; [|assert_diffs; auto]|].
      * intro; treat_equalities; apply rect_permut, rect_permut in HR3.
        apply degenerated_rect_eq in HR3; treat_equalities; auto.
      * apply rect_per2 with I'; do 3 apply rect_permut; auto.
    + elim (eq_dec_points G N); [intro; treat_equalities; Perp|intro HGN].
      cut (Perp N G G H); [Perp|].
      apply perp_col4 with J G G H; Col.
      cut (Per J G H); [apply per_perp; [|assert_diffs; auto]|].
      * intro; treat_equalities; apply rect_permut, rect_permut in HR1.
        apply degenerated_rect_eq in HR1; treat_equalities; auto.
      * apply rect_per2 with I; do 3 apply rect_permut; auto.
  - apply l10_12 with J' J; Cong.
    + elim (eq_dec_points J' N'); [intro; treat_equalities; Perp|intro HJ'N'].
      elim (eq_dec_points J' O'); [intro; treat_equalities; Perp|intro HJ'O'].
      cut (Perp N' J' J' O'); [Perp|].
      apply perp_col4 with G' J' J' I'; Col.
      cut (Per G' J' I'); [apply per_perp|].
      * intro; treat_equalities; apply rect_permut, rect_permut in HR3.
        apply degenerated_rect_eq in HR3; treat_equalities; auto.
      * intro; treat_equalities; apply rect_permut in HR3.
        apply degenerated_rect_eq in HR3; treat_equalities; auto.
      * apply rect_per1 with H'; do 3 apply rect_permut; auto.
    + elim (eq_dec_points J N); [intro; treat_equalities; Perp|intro HJN].
      elim (eq_dec_points J O); [intro; treat_equalities; Perp|intro HJO].
      cut (Perp N J J O); [Perp|].
      apply perp_col4 with G J J I; Col.
      cut (Per G J I); [apply per_perp|].
      * intro; treat_equalities; apply rect_permut, rect_permut in HR1.
        apply degenerated_rect_eq in HR1; treat_equalities; auto.
      * intro; treat_equalities; apply rect_permut in HR1.
        apply degenerated_rect_eq in HR1; treat_equalities; auto.
      * apply rect_per1 with H; do 3 apply rect_permut; auto.
    + apply l2_11 with G' G; Between; Cong.
      apply Rectangle_Parallelogram, plg_cong in HR1.
      apply Rectangle_Parallelogram, plg_cong in HR3; spliter; CongR.
    + apply l2_11 with I' I; Between; Cong.
      apply Rectangle_Parallelogram, plg_cong in HR1.
      apply Rectangle_Parallelogram, plg_cong in HR3; spliter; CongR.
  - apply l10_12 with I' I; Cong.
    + elim (eq_dec_points H' I'); [intro; treat_equalities; Perp|intro HH'I'].
      elim (eq_dec_points I' O'); [intro; treat_equalities; Perp|intro HI'O'].
      cut (Perp H' I' I' O'); [Perp|].
      apply perp_col4 with H' I' I' J'; Col.
      cut (Per H' I' J'); [apply per_perp|].
      * intro; treat_equalities.
        apply degenerated_rect_eq in HR3; treat_equalities; auto.
      * intro; treat_equalities; apply rect_permut in HR3.
        apply degenerated_rect_eq in HR3; treat_equalities; auto.
      * apply rect_per2 with G', rect_permut; auto.
    + elim (eq_dec_points I O); [intro; treat_equalities; Perp|intro HIO].
      cut (Perp H I I O); [Perp|].
      apply perp_col4 with H I I J; Col.
      cut (Per H I J); [apply per_perp; auto|].
      * intro; treat_equalities; apply rect_permut in HR1.
        apply degenerated_rect_eq in HR1; treat_equalities; auto.
      * apply rect_per2 with G, rect_permut; auto.
  }
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
assert (Hdf : d <> f).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR3.
  apply degenerated_rect_eq in HR3; auto.
  }
assert (Hef : e <> f).
  {
  intro; treat_equalities; apply rect_permut in HR3.
  apply degenerated_rect_eq in HR3; auto.
  }
assert (Haf : a <> f).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR4.
  apply degenerated_rect_eq in HR4; auto.
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
assert (HB4 : Bet a d f).
  {
  assert (HCol : Col a d f).
    {
    cut (Col f a d); Col.
    cut (Par f a f d); [apply par_id|].
    apply par_trans with b e.
    - apply plg_par_1; auto.
      do 3 apply plg_permut; apply Rectangle_Parallelogram; auto.
    - apply par_col4__par with c e f d; Col.
      apply plg_par_1; auto.
      apply plg_permut; apply Rectangle_Parallelogram; auto.
    }
  apply col_two_sides_bet with c; [Col|].
  assert (HNC : ~ Col d c e)
    by (apply per_not_col; [..|apply rect_per2 with f]; auto).
  apply l9_8_2 with b; [apply l9_2, l9_8_2 with e|].
  - split; [intro; apply HNC; ColR|].
    split; [intro; apply HNC; ColR|].
    exists c; split; [Col|Between].
  - apply l12_6, ncol123_plg__pars1234; [Col|].
    apply Rectangle_Parallelogram; auto.
  - apply l12_6, par_not_col_strict with b; [|Col|].
    + apply par_trans with e f.
      * apply plg_par_1; [..|apply Rectangle_Parallelogram]; auto.
      * cut (Par a b e f); [Par|].
        apply plg_par_1; [..|apply Rectangle_Parallelogram]; auto.
    + intro HF; apply Hbc; apply l6_21 with d c e c; Col.
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
assert (HR6 : Rectangle a b c d).
  {
  apply plg_per_rect2.
  - apply parallelogram_to_plg; do 3 apply plg_permut.
    assert (HC : Cong b c a d).
      {
      apply l4_3 with e f; Between;
      apply plg_cong_2, plg_comm2, Rectangle_Parallelogram; auto.
      }
    apply plg_out_plg with e f; Cong.
    + apply plg_permut, Rectangle_Parallelogram; auto.
    + split; [|split]; Between.
    + split; [auto|split]; assert_diffs; Between.
  - cut (Perp a b b c); Perp.
    apply perp_col4 with a b b e; Col.
    cut (Per a b e); [apply per_perp; assert_diffs; auto|].
    apply rect_per2 with f; auto.
  }
assert (HR : EqR B E F A a b e f).
  {
  apply EqR_trans with A B E F; [apply EqR_sym|auto].
  assert (HE := EqR_perm A B E F HAB HBE HR2); spliter; auto.
  }
destruct HR as [_ [_ [_ [_ [_ [_ HR]]]]]]; assert (HR' := HR).
destruct HR as [G [H [K [L [M [N [O [J [I HR]]]]]]]]].
destruct HR as [HR7 [HC1 [HC2 [HR8 [HC3 [HC4 HR]]]]]].
destruct HR as [HB5 [HB6 [HB7 [HB8 [HB9 [HB10 HB11]]]]]].
assert (HGJ : G <> J).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR7.
  apply degenerated_rect_eq in HR7; treat_equalities; auto.
  }
destruct (le_bet G H B C) as [P [HB12 HC5]];
[apply l5_6 with B C B E; Cong; apply bet__le1213; Between|].
destruct (plg_existence I H P) as [Q HP]; [assert_diffs; auto|].
assert (HHP : H <> P)
  by (intro; treat_equalities; apply HCE, between_cong with B; [Between|CongR]).
assert (HR9 : Rectangle I H P Q).
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  cut (Perp P H H I); Perp.
  apply perp_col4 with G H H I; Col; [assert_diffs; auto..|].
  cut (Per G H I); [apply per_perp; assert_diffs; auto|].
  apply l8_2, rect_per2 with J; do 3 apply rect_permut; apply rect_comm2; auto.
  }
assert (HBR : Bet J Q I /\ Rectangle J G P Q)
  by (apply (HCut B C E G H); Cong; assert_diffs; auto).
clear HP; destruct HBR as [HB13 HR10].
destruct (le_bet L K b c) as [R [HB14 HC6]];
[apply l5_6 with b c b e; Cong; apply bet__le1213; Between|].
destruct (plg_existence H K R) as [S HP]; [assert_diffs; auto|].
assert (HKR : K <> R)
  by (intro; treat_equalities; apply Hce, between_cong with b; [Between|CongR]).
assert (HR11 : Rectangle H K R S).
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  cut (Perp R K K H); Perp.
  apply perp_col4 with L K K H; Col; [assert_diffs; auto..|].
  cut (Per L K H); [apply per_perp; assert_diffs; auto|].
  apply l8_2, rect_per2 with M; auto.
  }
assert (HLM : L <> M).
  {
  intro; treat_equalities; apply rect_permut in HR8.
  apply degenerated_rect_eq in HR8; treat_equalities; auto.
  }
assert (HLR : L <> R) by (assert_diffs; auto).
assert (HBR : Bet M S H /\ Rectangle M L R S).
  {
  apply (HCut b c e L K); Cong; [assert_diffs; auto..|].
  apply rect_permut, rect_comm2, rect_permut, rect_permut; auto.
  }
clear HP; destruct HBR as [HB15 HR12].
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
assert (HD : H <> K /\ I <> O).
  {
  assert (HParS : Par_strict S H K R).
    {
    apply ncol123_plg__pars1234.
    - cut (~ Col S H K); [Col|].
      apply per_not_col; [|assert_diffs; auto|apply rect_per3 with R].
      + intro; treat_equalities.
         apply rect_permut, rect_permut, degenerated_rect_eq in HR11; auto.
      + do 2 apply rect_permut; auto.
    - do 3 apply plg_permut; apply Rectangle_Parallelogram; auto.
    }
  assert (HH := par_not_col _ _ _ _ H HParS).
  assert (HI := par_not_col _ _ _ _ I HParS).
  split; intro; treat_equalities; [apply HH|apply HI]; Col; ColR.
  }
destruct HD as [HHK HIO].
assert (HKO : K <> O).
  {
  assert (HParS : Par_strict H P I Q).
    {
    cut (Par_strict H P Q I); [Par|apply ncol123_plg__pars1234].
    - apply per_not_col; [assert_diffs; auto| |apply rect_per3 with I; auto].
      intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR10; auto.
    - apply plg_permut, Rectangle_Parallelogram; auto.
    }
  apply (par_not_col _ _ _ _ K) in HParS; [|ColR].
  intro; treat_equalities; apply HParS; ColR.
  }
assert (HR13 : Rectangle I H K O).
  {
  apply rect_permut, cop_perp3__rect.
  - cut (Par O I K H); [Cop|].
    apply par_col4__par with I J G H; Col.
    apply Rectangle_Parallelogram, plg_par in HR7; spliter; Par.
    + intro; treat_equalities; apply degenerated_rect_eq in HR10; auto.
    + intro; treat_equalities; do 3 apply rect_permut in HR9.
      apply degenerated_rect_eq in HR9; auto.
  - apply perp_col4 with J I I H; Col; [assert_diffs; auto|].
    cut (Per J I H); [apply per_perp; assert_diffs; auto|].
    + intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR7; auto.
    + apply rect_per3 with G; apply rect_comm2; do 3 apply rect_permut; auto.
  - apply perp_col4 with I H H P; Col; [assert_diffs; auto|ColR|].
    cut (Per I H P); [apply per_perp; assert_diffs; auto|].
    apply rect_per3 with Q; do 3 apply rect_permut; auto.
  - apply perp_col4 with H K K R; Col; [ColR|].
    cut (Per H K R); [apply per_perp; assert_diffs; auto|].
    apply rect_per3 with S; do 3 apply rect_permut; auto.
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
      assert (HHI : H <> I).
        {
        intro; treat_equalities; do 3 apply rect_permut in HR9.
        apply degenerated_rect_eq in HR9; treat_equalities; auto.
        }
      apply Rectangle_Parallelogram, plg_par in HR9; spliter; Par.
    + apply par_col4__par with H S P T; Col; [..|ColR].
      apply Rectangle_Parallelogram, plg_par in HR14; spliter; Par.
  - cut (Per Q P G); [apply per_perp; assert_diffs; auto|].
    apply rect_per1 with J, rect_permut, rect_permut; auto.
  }
clear HP.
assert (HMS : M <> S).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR12.
  apply degenerated_rect_eq in HR12; auto.
  }
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
  apply (rect2_bet__bet S H I); Between.
  - do 3 apply rect_permut; auto.
  - apply rect_comm2; auto.
  - intro; treat_equalities; do 3 apply rect_permut in HR13.
    apply degenerated_rect_eq in HR13; auto.
  - apply (between_exchange3 M); Between.
  }
assert (HB17 : Bet T S R).
  {
  apply (rect2_bet__bet P H K); Between; [apply rect_comm2; auto|].
  apply (between_exchange3 G); Between.
  }
assert (HB18 : Bet T H O).
  {
  apply (EqRP P H I Q K R S); Between.
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
  apply (rect2_bet__bet G P H); Between; [|assert_diffs; auto].
  apply rect_comm2; auto.
  }
assert (HB20 : Bet V T P).
  {
  apply (rect2_bet__bet M S H); Between.
  do 3 apply rect_permut; auto.
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
    assert (HGP : G <> P).
      {
      intro; treat_equalities; do 3 apply rect_permut in HR15.
      apply degenerated_rect_eq in HR15; auto.
      }
    cut (Col G U J); [Col|cut (Par G U G J); [apply par_id|]].
    apply par_trans with P Q.
    - apply par_col4__par with G U P T; Col.
      apply Rectangle_Parallelogram, plg_par in HR15; spliter; Par.
    - apply Rectangle_Parallelogram, plg_par in HR10; spliter; Par.
    }
  assert (HP1 : Par L M R S)
    by (apply Rectangle_Parallelogram, plg_par in HR12; spliter; Par).
  assert (HGP : G <> P) by (assert_diffs; auto).
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
  apply (rect2_bet__bet V T P); Between.
  - apply rect_comm2, rect_permut, rect_permut; auto.
  - apply rect_comm2, rect_permut; auto.
  - intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR17; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR16; auto.
  }
assert (HB22 : Bet N V M).
  {
  apply (rect2_bet__bet U T S); Between.
  - apply rect_permut; auto.
  - do 3 apply rect_permut; apply rect_comm2; auto.
  - intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR16; auto.
  }
assert (HB23 : Bet N T H).
  {
  assert (HTNH : Col T N H).
    {
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
clear HR7 HC1 HC2 HR8 HC3 HC4 HB5 HB6 HB7 HB8 HB9 HB10 HB11.
clear HGJ HB12 HC5 HHP HR9 HB13 HR10 HB14 HC6 HKR HR11 HLM HLR HB15 HR12.
clear HE3 HE4 HHK HIO HKO HR13 HHS HR14 HIS HPQ HPT HMS HST HB16 HB17 HB18.
clear HTU HGU HB19 HB20 HR17 HB21 HB22 HB23 H K L N O J I Q R.
revert G M P S T U V HR15 HR16 HE9 HCs HR'.
intros G M P S T U V HR7 HR8 HE3 [HC1 [HC2 [HC3 HC4]]] HR.
destruct HR as [G' [H' [K' [L' [M' [N' [O' [J' [I' HR]]]]]]]]].
destruct HR as [HR9 [HC5 [HC6 [HR10 [HC7 [HC8 HR]]]]]].
destruct HR as [HB5 [HB6 [HB7 [HB8 [HB9 [HB10 HB11]]]]]].
assert (HG'J' : G' <> J').
  {
  intro; treat_equalities; do 2 apply rect_permut in HR9.
  apply degenerated_rect_eq in HR9; treat_equalities; auto.
  }
destruct (le_bet G' H' C E) as [P' [HB12 HC9]];
[apply l5_6 with C E B E; Cong; apply bet__le2313; Between|].
destruct (plg_existence I' H' P') as [Q' HP]; [assert_diffs; auto|].
assert (HH'P' : H' <> P').
  {
  intro; treat_equalities; apply HBC; cut (C = B); [auto|].
  apply between_cong with E; [Between|CongR].
  }
assert (HR11 : Rectangle I' H' P' Q').
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  cut (Perp P' H' H' I'); Perp.
  apply perp_col4 with G' H' H' I'; Col; [assert_diffs; auto..|].
  cut (Per G' H' I'); [apply per_perp; assert_diffs; auto|].
  apply l8_2, rect_per2 with J'; do 3 apply rect_permut; apply rect_comm2; auto.
  }
assert (HBR : Bet J' Q' I' /\ Rectangle J' G' P' Q')
  by (apply (HCut E C B G' H'); Cong; Between; assert_diffs; auto).
clear HP; destruct HBR as [HB13 HR12].
destruct (le_bet L' K' c e) as [R' [HB14 HC10]];
[apply l5_6 with c e b e; Cong; apply bet__le2313; Between|].
destruct (plg_existence H' K' R') as [S' HP]; [assert_diffs; auto|].
assert (HK'R' : K' <> R').
  {
  intro; treat_equalities; apply Hbc; cut (c = b); [auto|].
  apply between_cong with e; [Between|CongR].
  }
assert (HR13 : Rectangle H' K' R' S').
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  cut (Perp R' K' K' H'); Perp.
  apply perp_col4 with L' K' K' H'; Col; [assert_diffs; auto..|].
  cut (Per L' K' H'); [apply per_perp; assert_diffs; auto|].
  apply l8_2, rect_per2 with M'; auto.
  }
assert (HL'M' : L' <> M').
  {
  intro; treat_equalities; apply rect_permut in HR10.
  apply degenerated_rect_eq in HR10; treat_equalities; auto.
  }
assert (HL'R' : L' <> R') by (assert_diffs; auto).
assert (HBR : Bet M' S' H' /\ Rectangle M' L' R' S').
  {
  apply (HCut e c b L' K'); Cong; Between; [assert_diffs; auto..|].
  apply rect_permut, rect_comm2, rect_permut, rect_permut; auto.
  }
clear HP; destruct HBR as [HB15 HR14].
assert (HD : H' <> K' /\ I' <> O').
  {
  assert (HParS : Par_strict S' H' K' R').
    {
    apply ncol123_plg__pars1234.
    - cut (~ Col S' H' K'); [Col|].
      apply per_not_col; [|assert_diffs; auto|apply rect_per3 with R'].
      + intro; treat_equalities.
         apply rect_permut, rect_permut, degenerated_rect_eq in HR13; auto.
      + do 2 apply rect_permut; auto.
    - do 3 apply plg_permut; apply Rectangle_Parallelogram; auto.
    }
  assert (HH' := par_not_col _ _ _ _ H' HParS).
  assert (HI' := par_not_col _ _ _ _ I' HParS).
  split; intro; treat_equalities; [apply HH'|apply HI']; Col; ColR.
  }
destruct HD as [HH'K' HI'O'].
assert (HK'O' : K' <> O').
  {
  assert (HParS : Par_strict H' P' I' Q').
    {
    cut (Par_strict H' P' Q' I'); [Par|apply ncol123_plg__pars1234].
    - apply per_not_col; [assert_diffs; auto| |apply rect_per3 with I'; auto].
      intro; treat_equalities.
      apply rect_permut, degenerated_rect_eq in HR12; auto.
    - apply plg_permut, Rectangle_Parallelogram; auto.
    }
  apply (par_not_col _ _ _ _ K') in HParS; [|ColR].
  intro; treat_equalities; apply HParS; ColR.
  }
assert (HH'S' : H' <> S').
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR13; auto.
  }
destruct (plg_existence S' H' P') as [T' HP]; auto.
assert (HR15 : Rectangle H' P' T' S').
  {
  apply plg_per_rect1; [apply parallelogram_to_plg, plg_permut; auto|].
  cut (Perp S' H' H' P'); [Perp|].
  apply perp_col4 with I' H' H' P'; Col; [ColR|].
  cut (Per I' H' P'); [apply per_perp; assert_diffs; auto|].
  apply rect_per2 with Q'; auto.
  }
clear HP.
assert (HB16 : Bet T' P' Q').
  {
  apply (rect2_bet__bet S' H' I'); Between.
  - do 3 apply rect_permut; auto.
  - apply rect_comm2; auto.
  - intro; treat_equalities; do 3 apply rect_permut in HR11.
    apply degenerated_rect_eq in HR11; auto.
  - apply (between_exchange3 M'); Between.
  }
assert (HB17 : Bet T' S' R').
  {
  apply (rect2_bet__bet P' H' K'); Between; [apply rect_comm2; auto|].
  apply (between_exchange3 G'); Between.
  }
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
destruct (plg_existence G' P' T') as [U' HP]; [assert_diffs; auto|].
assert (HI'S' : I' <> S').
  {
  intro; treat_equalities; do 3 apply rect_permut in HR11.
  apply degenerated_rect_eq in HR11; treat_equalities; auto.
  }
assert (HP'Q' : P' <> Q').
  {
  intro; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR11; treat_equalities; auto.
  }
assert (HP'T' : P' <> T')
  by (intro; treat_equalities; apply degenerated_rect_eq in HR15; auto).
assert (HR16 : Rectangle G' P' T' U').
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  cut (Perp T' P' P' G'); [Perp|].
  apply perp_col4 with Q' P' P' G'; Col; [assert_diffs; auto|..].
  cut (Per Q' P' G'); [apply per_perp; assert_diffs; auto|].
  apply rect_per1 with J', rect_permut, rect_permut; auto.
  }
clear HP.
assert (HM'S' : M' <> S').
  {
  intro; treat_equalities; do 2 apply rect_permut in HR14.
  apply degenerated_rect_eq in HR14; auto.
  }
destruct (plg_existence M' S' T') as [V' HP]; auto.
assert (HST : S' <> T').
  {
  intro; treat_equalities; apply rect_permut in HR15.
  apply degenerated_rect_eq in HR15; auto.
  }
assert (HR17 : Rectangle M' S' T' V').
  {
  apply plg_per_rect2; [apply parallelogram_to_plg; auto|].
  cut (Perp T' S' S' M'); [Perp|].
  apply perp_col4 with T' S' S' H'; Col.
  cut (Per T' S' H'); [apply per_perp; assert_diffs; auto|].
  apply rect_per2 with P', rect_permut, rect_permut; auto.
  }
clear HP.
assert (HB18 : Bet T' P' Q').
  {
  apply (rect2_bet__bet S' H' I'); Between.
  - do 3 apply rect_permut; auto.
  - apply rect_comm2; auto.
  - intro; treat_equalities; do 3 apply rect_permut in HR11.
    apply degenerated_rect_eq in HR11; auto.
  - apply (between_exchange3 M'); Between.
  }
assert (HB19 : Bet T' S' R').
  {
  apply (rect2_bet__bet P' H' K'); Between; [apply rect_comm2; auto|].
  apply (between_exchange3 G'); Between.
  }
assert (HT'U' : T' <> U').
  {
  intro; treat_equalities.
  apply rect_permut, degenerated_rect_eq in HR16; treat_equalities.
  apply degenerated_rect_eq in HR12; auto.
  }
assert (HG'U' : G' <> U').
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR16; auto.
  }
assert (HB20 : Bet U' T' S').
  {
  apply (rect2_bet__bet G' P' H'); Between; [|assert_diffs; auto].
  apply rect_comm2; auto.
  }
assert (HB21 : Bet V' T' P').
  {
  apply (rect2_bet__bet M' S' H'); Between.
  do 3 apply rect_permut; auto.
  }
assert (HR18 : Rectangle N' U' T' V').
  {
  assert (HCol1 : Col N' G' J') by Col.
  assert (HCol2 : Col V' P' Q') by ColR.
  assert (HCol3 : Col N' M' L') by Col.
  assert (HCol4 : Col U' S' R') by ColR.
  assert (HCol5 : Col L' M' V').
    {
    cut (Col M' L' V'); [Col|cut (Par M' L' M' V'); [apply par_id|]].
    apply par_trans with R' S'.
    - apply Rectangle_Parallelogram, plg_par in HR14; spliter; Par.
    - apply par_col4__par with S' T' M' V'; Col.
      + intro; treat_equalities.
        apply rect_permut, degenerated_rect_eq in HR14; auto.
      + intro; treat_equalities.
        apply rect_permut, rect_permut, degenerated_rect_eq in HR17; auto.
      + apply Rectangle_Parallelogram, plg_par in HR17; spliter; Par.
    }
  assert (HCol6 : Col U' G' J').
    {
    assert (HG'P' : G' <> P').
      {
      intro; treat_equalities; do 3 apply rect_permut in HR16.
      apply degenerated_rect_eq in HR16; auto.
      }
    cut (Col G' U' J'); [Col|cut (Par G' U' G' J'); [apply par_id|]].
    apply par_trans with P' Q'.
    - apply par_col4__par with G' U' P' T'; Col.
      apply Rectangle_Parallelogram, plg_par in HR16; spliter; Par.
    - apply Rectangle_Parallelogram, plg_par in HR12; spliter; Par.
    }
  assert (HP1 : Par L' M' R' S')
    by (apply Rectangle_Parallelogram, plg_par in HR14; spliter; Par).
  assert (HG'P' : G' <> P') by (assert_diffs; auto).
  assert (HP2 : Par P' Q' G' J')
    by (apply Rectangle_Parallelogram, plg_par in HR12; spliter; Par).
  assert (HPer : Per U' N' V').
    {
    elim (eq_dec_points N' U'); [intro; treat_equalities; Perp|intro HN'U'].
    elim (eq_dec_points N' V'); [intro; treat_equalities; Perp|intro HN'V'].
    cut (Perp U' N' N' V'); [Perp|].
    apply cop_par_perp__perp with P' T'; Cop.
    - apply par_col4__par with P' Q' G' J'; Col.
    - cut (Perp N' V' P' T'); [Perp|].
      apply cop_par_perp__perp with S' T'; Cop.
      + apply par_col4__par with R' S' L' M'; Col; Par.
      + cut (Perp P' T' T' S'); [Perp|].
        cut (Per P' T' S'); [apply per_perp; assert_diffs; auto|].
        apply rect_per2 with H', rect_permut; auto.
    }
  assert (HN'U' : N' <> U').
    {
    apply (par_not_col_strict _ _ _ _ R') in HP1; Col.
    - intro; treat_equalities; apply (par_not_col L' M' R' S' N' HP1); Col.
    - cut (~ Col M' L' R'); [Col|apply per_not_col; [assert_diffs; auto..|]].
      apply rect_per2 with S'; auto.
    }
  assert (HN'V' : N' <> V').
    {
    apply (par_not_col_strict _ _ _ _ G') in HP2; Col.
    - intro; treat_equalities; apply (par_not_col P' Q' G' J' N' HP2); Col.
    - cut (~ Col Q' P' G'); [Col|apply per_not_col; [assert_diffs; auto..|]].
      apply rect_per1 with J', rect_permut, rect_permut; auto.
    }
  assert (HT'V' : T' <> V').
    {
    apply (par_not_col_strict _ _ _ _ R') in HP1; Col.
    - intro; treat_equalities; apply (par_not_col L' M' R' S' T' HP1); Col.
    - cut (~ Col M' L' R'); [Col|apply per_not_col; [assert_diffs; auto..|]].
      apply rect_per2 with S'; auto.
    }
  apply plg_per_rect1; [apply parallelogram_to_plg|Perp].
  apply plg_permut, par_2_plg.
  - apply per_not_col; Perp.
  - apply par_col4__par with L' M' R' S'; Col.
  - apply par_col4__par with P' Q' G' J'; Col.
  }
assert (HB22 : Bet N' U' G').
  {
  apply (rect2_bet__bet V' T' P'); Between.
  - apply rect_comm2, rect_permut, rect_permut; auto.
  - apply rect_comm2, rect_permut; auto.
  - intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR18; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR17; auto.
  }
assert (HB23 : Bet N' V' M').
  {
  apply (rect2_bet__bet U' T' S'); Between.
  - apply rect_permut; auto.
  - do 3 apply rect_permut; apply rect_comm2; auto.
  - intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR17; auto.
  }
apply (EqRP U' T' P' G' S' M' V'); Between.
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
assert (HExtend : forall G H I J P Q,
                    Bet G P H -> Bet J Q I -> Cong G P J Q ->
                    P <> H -> H <> I -> Rectangle P H I Q ->
                    Rectangle J G P Q).
  {
  clear A B C D E F a b c d e f; intros G H I J P Q HB1 HB2 HC HPH HHI HR.
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
  }
intros HB1 HB2 HE1 HE2.
assert (HB3 : Bet A D F).
  {
  destruct HE1 as [_ [_ [HR1 _]]]; destruct HE2 as [_ [_ [HR2 _]]].
  apply Bet_Rect2__Bet with B C E; Between.
  }
assert (HB4 : Bet a d f).
  {
  destruct HE1 as [_ [_ [_ [_ [_ [HR1 _]]]]]].
  destruct HE2 as [_ [_ [_ [_ [_ [HR2 _]]]]]].
  apply Bet_Rect2__Bet with b c e; Between.
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
assert (Hdf : d <> f).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR4.
  apply degenerated_rect_eq in HR4; auto.
  }
assert (Hef : e <> f).
  {
  intro; treat_equalities; apply rect_permut in HR4.
  apply degenerated_rect_eq in HR4; auto.
  }
assert (Haf : a <> f) by (assert_diffs; auto).
assert (HH'O' : H' <> O').
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram G' H' I' J' HR5).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs__pars, (par_not_col _ _ _ _ H') in HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with J'; auto.
  }
assert (HI'O' : I' <> O').
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram H' K' L' M' HR6).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs_pars_2, (par_not_col _ _ _ _ I') in HPlg; Col.
    apply HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with M'; auto.
  }
assert (HI'J' : I' <> J').
  {
  intro; treat_equalities; apply rect_permut in HR5.
  apply degenerated_rect_eq in HR5; treat_equalities; auto.
  }
assert (HCA1 : CongA G' N' H' I' H' O').
  {
  assert (HG'N' : G' <> N').
    {
    intro; treat_equalities.
    assert (HPlg := Rectangle_Parallelogram H' K' L' M' HR6).
    apply ncol123_plg__plgs in HPlg.
    - apply plgs__pars, (par_not_col _ _ _ _ G') in HPlg; Col.
      apply HPlg; Col.
    - apply per_not_col; [assert_diffs; auto..|].
      apply rect_per2 with M'; auto.
    }
  assert (HH'N' : H' <> N').
    {
    intro; treat_equalities.
    assert (HPlg := Rectangle_Parallelogram G' H' I' J' HR5).
    apply ncol123_plg__plgs in HPlg.
    - apply plgs_pars_2, (par_not_col _ _ _ _ H') in HPlg; Col.
    - apply per_not_col; [assert_diffs; auto..|].
      apply rect_per2 with J'; auto.
    }
  assert (HG'J' : G' <> J').
    {
    intro; treat_equalities; do 2 apply rect_permut in HR5.
    apply degenerated_rect_eq in HR5; treat_equalities; auto.
    }
  assert (HNC : ~ Col G' J' I')
    by (apply per_not_col; auto; apply rect_per4 with H'; auto).
  apply conga_trans with G' N' O'.
  - apply out2__conga; [apply out_trivial; auto|].
    split; [|split]; Between; assert_diffs; auto.
  - apply l12_22_a; [split; [|split]; Between; assert_diffs; auto|..].
    + apply one_side_transitivity with J'.
      * apply out_one_side_1 with N'; [intro; apply HNC; ColR|Col|].
        split; [|split]; Between; assert_diffs; auto.
      * apply out_one_side_1 with O'; [intro; apply HNC; ColR|Col|].
        split; [|split]; Between; assert_diffs; auto.
    + apply Rectangle_Parallelogram, plg_par in HR5; [|assert_diffs; auto..].
      apply par_col4__par with G' J' H' I'; Col; [assert_diffs|spliter]; Par.
  }
assert (HR9 : Rectangle I' H' K' O').
  {
  assert (HH'I' : H' <> I')
    by (intro; treat_equalities; apply degenerated_rect_eq in HR5; auto).
  assert (HH'K' : H' <> K').
    {
    intro; treat_equalities; do 3 apply rect_permut in HR6.
    apply degenerated_rect_eq in HR6; auto.
    }
  assert (HH'G' : H' <> G').
    {
    intro; treat_equalities; do 3 apply rect_permut in HR5.
    apply degenerated_rect_eq in HR5; auto.
    }
  assert (HK'O' : K' <> O').
    {
    intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram G' H' I' J' HR5).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs__pars, (par_not_col _ _ _ _ K') in HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with J'; auto.
    }
  apply rect_permut, cop_perp3__rect.
  - cut (Par O' I' K' H'); [Cop|].
    apply par_col4__par with I' J' G' H'; Col.
    apply Rectangle_Parallelogram, plg_par in HR5; spliter; Par.
  - apply perp_col4 with J' I' I' H'; Col.
    cut (Per J' I' H'); [apply per_perp; assert_diffs; auto|].
    apply rect_per3 with G'; apply rect_comm2; do 3 apply rect_permut; auto.
  - apply perp_col4 with I' H' H' G'; Col.
    cut (Per I' H' G'); [apply per_perp; assert_diffs; auto|].
    apply rect_per4 with J'; do 2 apply rect_permut; auto.
  - apply perp_col4 with H' K' K' L'; Col.
    cut (Per H' K' L'); [apply per_perp; assert_diffs; auto|].
    apply rect_per3 with M'; do 3 apply rect_permut; auto.
  }
assert (HIO : I <> O).
  {
  intro; treat_equalities.
  assert (HPlg := Rectangle_Parallelogram H K R S HR8).
  apply ncol123_plg__plgs in HPlg.
  - apply plgs_pars_2, (par_not_col _ _ _ _ I) in HPlg; Col.
    apply HPlg; Col.
  - apply per_not_col; [assert_diffs; auto..|].
    apply rect_per2 with S; auto.
  }
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
assert (HCA2: CongA P T H I H O).
  {
  assert (HPT : P <> T).
    {
    intro; treat_equalities.
    assert (HPlg := Rectangle_Parallelogram H K R S HR8).
    apply ncol123_plg__plgs in HPlg.
    - apply plgs__pars, (par_not_col _ _ _ _ P) in HPlg; Col.
      apply HPlg; Col.
    - apply per_not_col; [assert_diffs; auto..|].
      apply rect_per2 with S; auto.
    }
  assert (HHO : H <> O).
    {
    intro; treat_equalities.
    assert (HPlg := Rectangle_Parallelogram P H I Q HR7).
    apply ncol123_plg__plgs in HPlg.
    - apply plgs__pars, (par_not_col _ _ _ _ H) in HPlg; Col.
    - apply per_not_col; [assert_diffs; auto..|].
      apply rect_per2 with Q; auto.
    }
  assert (HPQ : P <> Q).
    {
    intro; treat_equalities; do 2 apply rect_permut in HR7.
    apply degenerated_rect_eq in HR7; treat_equalities; auto.
    }
  assert (HNC : ~ Col P Q I)
    by (apply per_not_col; auto; apply rect_per4 with H; auto).
  apply conga_trans with P T O.
  - apply out2__conga; [apply out_trivial; auto|].
    split; [|split]; Between; assert_diffs; auto.
  - apply l12_22_a; [split; [|split]; Between; assert_diffs; auto|..].
    + apply one_side_transitivity with Q.
      * apply out_one_side_1 with T; [intro; apply HNC; ColR|Col|].
        split; [|split]; Between; assert_diffs; auto.
      * apply out_one_side_1 with O; [intro; apply HNC; ColR|Col|].
        split; [|split]; Between; assert_diffs; auto.
    + apply Rectangle_Parallelogram, plg_par in HR7; [|assert_diffs; auto..].
      apply par_col4__par with P Q H I; Col; [assert_diffs|spliter]; Par.
  }
assert (HR10 : Rectangle I H K O).
  {
  assert (HHI : H <> I)
    by (intro; treat_equalities; apply degenerated_rect_eq in HR7; auto).
  assert (HHK : H <> K).
    {
    intro; treat_equalities; do 3 apply rect_permut in HR8.
    apply degenerated_rect_eq in HR8; auto.
    }
  assert (HHP : H <> P).
    {
    intro; treat_equalities; do 3 apply rect_permut in HR7.
    apply degenerated_rect_eq in HR7; auto.
    }
  assert (HKO : K <> O).
    {
    intro; treat_equalities.
    assert (HPlg := Rectangle_Parallelogram P H I Q HR7).
    apply ncol123_plg__plgs in HPlg.
    - apply plgs__pars, (par_not_col _ _ _ _ K) in HPlg; Col.
    - apply per_not_col; [assert_diffs; auto..|].
      apply rect_per2 with Q; auto.
    }
  apply rect_permut, cop_perp3__rect.
  - cut (Par O I K H); [Cop|].
    apply par_col4__par with I Q P H; Col.
    apply Rectangle_Parallelogram, plg_par in HR7; spliter; Par.
  - apply perp_col4 with Q I I H; Col.
    cut (Per Q I H); [apply per_perp; assert_diffs; auto|].
    apply rect_per3 with P; apply rect_comm2; do 3 apply rect_permut; auto.
  - apply perp_col4 with I H H P; Col.
    cut (Per I H P); [apply per_perp; assert_diffs; auto|].
    apply rect_per4 with Q; do 2 apply rect_permut; auto.
  - apply perp_col4 with H K K R; Col.
    cut (Per H K R); [apply per_perp; assert_diffs; auto|].
    apply rect_per3 with S; do 3 apply rect_permut; auto.
  }
assert (HCA3: CongA I' H' O' I H O).
  {
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
  - apply Rectangle_Parallelogram, plg_cong in HR2.
    apply Rectangle_Parallelogram, plg_cong in HR9.
    apply Rectangle_Parallelogram, plg_cong in HR10; spliter; CongR.
  }
assert (HCA4 : CongA G' N' H' P T H).
  {
  apply conga_trans with I' H' O'; [auto|].
  apply conga_trans with I H O; [|apply conga_sym]; auto.
  }
assert (HR11 : Rectangle H P T S).
  {
  apply plg_per_rect; [apply pars_par_plg|left].
  - apply par_not_col_strict with T; [|Col|].
    + apply par_col4__par with H K R S; Col; [assert_diffs; auto|..].
      * intro; treat_equalities.
        assert (HPlg := Rectangle_Parallelogram P H I Q HR7).
        apply ncol123_plg__plgs in HPlg.
        -- apply plgs_pars_2, (par_not_col _ _ _ _ T) in HPlg; Col.
        -- apply per_not_col; [assert_diffs; auto..|].
           apply rect_per2 with Q; auto.
      * apply Rectangle_Parallelogram, plg_par in HR8; [|assert_diffs; auto..].
        spliter; Par.
    + cut (~ Col H P Q); [intros HNC HF; apply HNC; ColR|].
      apply per_not_col; [assert_diffs; auto| |apply rect_per1 with I; auto].
      apply Rectangle_Parallelogram, plg_cong in HR7.
      spliter; intro; treat_equalities; auto.
  - apply par_col4__par with H I P Q; Col; [|assert_diffs; auto|].
    + apply Rectangle_Parallelogram, plg_cong in HR8.
      spliter; intro; treat_equalities; auto.
    + apply Rectangle_Parallelogram, plg_par in HR7; spliter; Par;
      intro; treat_equalities; auto.
  - apply l8_3 with I; [|intro; treat_equalities; auto|Col].
    apply rect_per4 with Q, rect_permut, rect_permut; auto.
  }
destruct (segment_construction I Q B C) as [J [HB19 HC9]].
destruct (segment_construction H P B C) as [G [HB20 HC10]].
assert (HR12 : Rectangle J G P Q)
  by (apply HExtend with H I; Between; [CongR|assert_diffs; auto..]).
destruct (segment_construction K R b c) as [L [HB21 HC11]].
destruct (segment_construction H S b c) as [M [HB22 HC12]].
assert (HR13 : Rectangle M L R S).
  {
  apply HExtend with K H; Between; [CongR|assert_diffs; auto..|].
  apply rect_permut, rect_comm2, rect_permut, rect_permut; auto.
  }
destruct (segment_construction J G P T) as [U [HB23 HC13]].
assert (HR14 : Rectangle G P T U).
  {
  do 2 apply rect_permut.
  apply HExtend with J Q; Between; [CongR|..|apply rect_comm2; auto].
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
  apply HExtend with L R; Between; [CongR| |assert_diffs; auto].
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
assert (HHMS : Col S H M).
  {
  apply par_id, par_trans with R K.
  - apply Rectangle_Parallelogram, plg_par in HR8; spliter; Par;
    intro; treat_equalities; auto.
  - apply par_col_par_2 with L; [intro; treat_equalities; auto|Col|].
    assert (HLM : L <> M).
      {
      apply Rectangle_Parallelogram, plg_cong in HR8.
      apply Rectangle_Parallelogram, plg_cong in HR13.
      intro; spliter; treat_equalities; auto.
      }
    apply Rectangle_Parallelogram, plg_par in HR13; spliter; Par.
      intro; treat_equalities; auto.
  }
assert (HPTV : Col P T V).
  {
  cut (Col T P V); [Col|apply par_id, par_trans with H S].
  - apply Rectangle_Parallelogram, plg_par in HR11; spliter; Par.
    intro; treat_equalities; auto.
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
assert (HKR : K <> R) by (intro; treat_equalities; auto).
assert (HHP : H <> P) by (intro; treat_equalities; auto).
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
  + apply l11_16; auto; [..|intro; treat_equalities; auto].
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

elim (eq_dec_points C D).
-intro; elim (eq_dec_points C K).
+ intro; treat_equalities.
  assert (HPerp7 : Perp A B B C) by (apply perp_col1 with X; auto; Perp; Col).
  assert (HPerp8 : Perp A B A C) by (apply perp_col1 with Y; auto; Perp; Col).
  assert (HCol : Col C A B) by (apply cop_perp2__col with A B; Cop; Perp).
  exfalso; Col.
+ intro; treat_equalities.
  assert (HPar2 : Par A B C K) by (apply par_col_par with L; auto).
  apply par__coplanar in HPar2.

  assert (HP3 : Perp C K K A)
    by (apply perp_in_per_1 in HPerp6; apply per_perp in HPerp6; auto; Perp).
  assert (HR : Rectangle A B C K) by (do 2 (apply rect_permut); apply cop_perp3__rect; Cop; Perp).
  exists C, K; split; auto; Col.

-intro.
 assert (HPar2 : Par A B C D) by (apply par_col_par with L; auto).
 elim (eq_dec_points C K).
  + intro; treat_equalities.
  apply par__coplanar in HPar2.
  assert (HP3 : Perp C D D B) by (apply perp_in_per_1 in HPerp3; apply per_perp in HPerp3; auto).
  assert (HR : Rectangle A B D C) by (apply rect_permut; apply cop_perp3__rect; Cop; Perp).
  exists D, C; split; auto; Col.

  + intro; assert_diffs.
  assert (HCol : Col C D K) by (apply col_transitivity_1 with L; auto).

  assert (HNDK : D <> K).
    {
    intro; treat_equalities.
    apply perp_left_comm in HP1; apply perp_left_comm in HP2.
    apply perp_per_2 in HP1; apply perp_per_2 in HP2.
    apply l8_2 in HP1; apply l8_2 in HP2.
    assert (HAB : A = B).
    apply l8_7 with D; auto.
    auto.
    }
  assert (HPar3 : Par A B D K) by (apply par_col_par with C; Col; Par).
  apply par__coplanar in HPar3.

  assert (HP3 : Perp B D D K).
    {
    apply perp_sym; apply perp_right_comm.
    apply perp_in_per_1 in HPerp3.
    apply per_perp in HPerp3; auto.
    apply perp_col with C; auto; Col; Perp.
    }
  assert (HR : Rectangle A B D K) by (apply rect_permut; apply cop_perp3__rect; Cop; Perp).
exists D, K; split; auto; Col.
Qed.

Lemma Circumscribed_rectangle_unique A B C D K d k :
  A <> B ->
  First_circumscribed_rectangle A B C D K ->
  First_circumscribed_rectangle A B C d k ->
  D = d /\ K = k.
Proof.
intros HNE [HR1 HC1] [HR2 HC2].
assert (HDK : D <> K).
  {
  apply Rectangle_Parallelogram, plg_cong in HR1.
  intro; spliter; treat_equalities; auto.
  }
assert (Hdk : d <> k).
  {
  apply Rectangle_Parallelogram, plg_cong in HR2.
  intro; spliter; treat_equalities; auto.
  }
elim (col_dec A B C); [intro HC3|clear HNE; intro HNC].
- assert (HBD : B = D).
    {
    assert (HPer : Per A B D) by (apply rect_per2 with K; assumption).
    elim (eq_dec_points B D); [auto|intro HBD; exfalso].
    apply Rectangle_Parallelogram, plg_par in HR1; [|auto..].
    apply per_not_col in HPer; [destruct HR1 as [HPar _]|auto..].
    apply (col2_par__col4 _ _ _ _ C) in HPar; [spliter|..]; Col.
    }
  treat_equalities; apply degenerated_rect_eq in HR1; treat_equalities.
    assert (HBd : B = d).
    {
    assert (HPer : Per A B d) by (apply rect_per2 with k; assumption).
    elim (eq_dec_points B d); [auto|intro HBd; exfalso].
    apply Rectangle_Parallelogram, plg_par in HR2; [|auto..].
    apply per_not_col in HPer; [destruct HR2 as [HPar _]|auto..].
    apply (col2_par__col4 _ _ _ _ C) in HPar; [spliter|..]; Col.
    }
  treat_equalities; apply degenerated_rect_eq in HR2; treat_equalities; auto.
- assert (HAB : A <> B) by (assert_diffs; auto).
  assert (HAK : A <> K).
    {
    apply Rectangle_Parallelogram, plg_cong in HR1.
    intro; spliter; treat_equalities; Col.
    }
  assert (HBD : B <> D).
    {
    apply Rectangle_Parallelogram, plg_cong in HR1.
    intro; spliter; treat_equalities; Col.
    }
  assert (HBd : B <> d).
    {
    apply Rectangle_Parallelogram, plg_cong in HR2.
    intro; spliter; treat_equalities; Col.
    }
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
    apply cop_per2__col with A; [|auto|..].
    * apply coplanar_pseudo_trans with A B C; Cop.
      -- elim (eq_dec_points C D); [intro; treat_equalities; Cop|intro HCD].
         cut (Par A B C D); [Cop|].
         apply Rectangle_Parallelogram, plg_par in HR1; [spliter|auto..].
         apply par_col4__par with A B D K; Col.
      -- elim (eq_dec_points C d); [intro; treat_equalities; Cop|intro HCd].
         cut (Par A B C d); [Cop|].
         apply Rectangle_Parallelogram, plg_par in HR2; [spliter|auto..].
         apply par_col4__par with A B d k; Col.
    * apply rect_per4 with K, rect_permut, rect_permut; assumption.
    * apply rect_per4 with k, rect_permut, rect_permut; assumption.
  + apply (col2_par__col4 _ _ _ _ C) in HPar; [spliter|..]; Col.
  + apply per_not_col; [auto..|].
    apply rect_per4 with B; assumption.
  + cut (Col K k A); [Col|].
    apply cop_per2__col with B; [|auto|..].
    * apply coplanar_pseudo_trans with A B C; Cop.
      -- elim (eq_dec_points C K); [intro; treat_equalities; Cop|intro HCK].
         cut (Par A B C K); [Cop|].
         apply Rectangle_Parallelogram, plg_par in HR1; [spliter|auto..].
         apply par_col4__par with A B D K; Col.
      -- elim (eq_dec_points C k); [intro; treat_equalities; Cop|intro HCk].
         cut (Par A B C k); [Cop|].
         apply Rectangle_Parallelogram, plg_par in HR2; [spliter|auto..].
         apply par_col4__par with A B d k; Col.
    * apply rect_per2 with D; do 3 apply rect_permut; assumption.
    * apply rect_per2 with d; do 3 apply rect_permut; assumption.
  + apply (col2_par__col4 _ _ _ _ C) in HPar; [spliter|..]; Col.
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
assert (HNBD : B <> D).
  {
  intro; treat_equalities.
  assert (HAK : A = K) by (apply degenerated_rect_eq with B; auto).
  treat_equalities; Col.
  }
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
unfold EqT.
exists J, K, l, m; do 2 (split; auto).

cut (EqR D E j k D E L M).
intro; apply EqR_trans with D E L M; auto.
apply EqR_trans with D E j k; auto.

destruct HFCR1, HFCR2, HFCR3, HFCR4.
assert (HN1 : A <> B /\ B <> J /\ D <> E /\ E <> j) by (apply EqR_diffs with K k; auto).
assert (HN2 : D <> E /\ E <> L /\ G <> H /\ H <> l) by (apply EqR_diffs with M m; auto); spliter.
apply B5_5; auto; Cong.

assert (HPar1 : Par D E j k) by (apply Rectangle_Parallelogram in H2; apply plg_par_1 in H2; auto).
assert (HPar2 : Par D E L M) by (apply Rectangle_Parallelogram in H4; apply plg_par_1 in H4; auto).
assert (HPar3 : Par j k L M) by (apply par_trans with D E; Par).
assert (HCol1 : Col j k L) by (apply not_strict_par2 with M F; Par; Col).
assert (HCol2 : Col j k M) by (apply not_strict_par2 with L F; Par; Col).
assert (HNjM : j <> M).
  {
  intro; treat_equalities.
  apply rect_per1 in H4; apply rect_per2 in H2.
  apply l8_2 in H4; apply l8_2 in H2.
  assert (D = E) by (apply l8_7 with j; auto).
  auto.
  }
assert (HPar4 : Par D E j M).
apply par_col_par with k; Par; Col.
assert (HPer1 : Per D E L) by (apply rect_per2 in H4; auto).
assert (HPer2 : Per D E j) by (apply rect_per2 in H2; auto).

assert (HNCol1 : ~ Col M D E).
  {
  intro.
  assert (HP : Parallelogram D E L M) by (apply Rectangle_Parallelogram in H4; auto).
  do 3 (apply plg_permut in HP).
  assert (HPF : Parallelogram_flat M D E L) by (apply plg_col_plgf; auto).
  do 3 (apply rect_permut in H4).
  assert_diffs.
  assert (H23 : M = L /\ D = E \/ M = D /\ L = E) by (apply plgf_rect_id; auto).
  destruct H23.
  destruct H18; auto.
  destruct H18; auto.
  }
assert (HNCol2 : ~ Col D E j).
  {
  intro.
  assert (HP : Parallelogram D E j k) by (apply Rectangle_Parallelogram in H2; auto).
  assert (HPF : Parallelogram_flat D E j k) by (apply plg_col_plgf; auto).
  assert (HPoints : D = k /\ E = j \/ D = E /\ k = j) by (apply plgf_rect_id; auto).
  destruct HPoints.
  destruct H17; auto.
  destruct H17; auto.
  }
assert (HCop1:  Coplanar D E j L) by (apply coplanar_trans_1 with M; Cop).
assert (HC : Col j L E) by (apply cop_per2__col with D; auto; Perp; Cop).
assert (HPar5: Par D M E j).
  {
  apply Rectangle_Parallelogram in H4; apply plg_par in H4; spliter; auto.
  apply par_col_par with L; auto; Col.
  }
assert (HP : Parallelogram D E j M) by (apply par_2_plg; Par).
apply plg_cong_2 in HP.
apply Rectangle_Parallelogram in H4; apply plg_cong_2 in H4.
apply cong_inner_transitivity with D M; Cong.
Qed.

Lemma B5_12 A B C D : ~ Col A B C -> Par A B C D -> EqT A B C A B D.
Proof.
intros HNCol HPar.
apply not_col_distincts in HNCol; destruct HNCol as [HNCol [HNAB [HNBC HNAC ]]]; assert_diffs.
assert (H : exists D K : Tpoint, First_circumscribed_rectangle A B C D K)
  by (apply Circumscribed_rectangle_exists; auto).
destruct H as [G [K H]].
assert (HR : Rectangle A B G K) by (destruct H; auto).
assert (HC : Col C G K) by (destruct H; auto).
assert (HNBD : B <> G).
  {
  intro; treat_equalities.
  assert (HAK : A = K) by (apply degenerated_rect_eq with B; auto).
  treat_equalities; Col.
  }
cut (Col G K D).
intro; exists G, K, G, K.
split; auto.
split; unfold First_circumscribed_rectangle; Col.
apply EqR_refl; auto.

assert (HPar2 :Par A B G K) by (apply Rectangle_Parallelogram in HR; apply plg_par_1; auto).
assert (HPar3 : Par C D G K) by (apply par_trans with A B; Par).
apply not_strict_par2 with C C; Par; Col.
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
assert (HAK : A <> K).
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR1.
  treat_equalities; Col.
  }
assert (HBD : B <> D).
  {
  intro; treat_equalities; apply degenerated_rect_eq in HR1.
  treat_equalities; Col.
  }
assert (HDK : D <> K).
  {
  intro; treat_equalities; apply rect_permut, degenerated_rect_eq in HR1.
  treat_equalities; Col.
  }
assert (HNC2 : ~ Col a b c) by (intro; apply cong_3_sym, l4_13 in HC3; Col).
assert (Hab : a <> b) by (assert_diffs; auto).
assert (Hac : a <> c) by (assert_diffs; auto).
assert (Hak : a <> k).
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR2.
  treat_equalities; Col.
  }
assert (Hbd : b <> d).
  {
  intro; treat_equalities; apply degenerated_rect_eq in HR2.
  treat_equalities; Col.
  }
assert (Hdk : d <> k).
  {
  intro; treat_equalities; apply rect_permut, degenerated_rect_eq in HR2.
  treat_equalities; Col.
  }
assert (HEP1 : C = D <-> c = d).
  {
  split; intro; treat_equalities.
  - assert (HPer1 : Per A B C) by (apply rect_per2 with K; auto).
    assert (HPer2 : Per a b c) by (apply l8_10 with A B C; Perp).
    assert (HNC3 : ~ Col b d k)
      by (apply per_not_col; auto; apply rect_per4 with a, rect_comm2; auto).
    apply l6_21 with b d k d; Col.
    cut (Col d c b); [Col|].
    apply cop_per2__col with a; Perp.
    + apply coplanar_pseudo_trans with b k d; Col; Cop.
    + apply rect_per1 with k, rect_permut; auto.
  - assert (HPer1 : Per a b c) by (apply rect_per2 with k; auto).
    assert (HPer2 : Per A B C)
      by (apply l8_10 with a b c; Perp; apply cong_3_sym; auto).
    assert (HNC3 : ~ Col B D K)
      by (apply per_not_col; auto; apply rect_per4 with A, rect_comm2; auto).
    apply l6_21 with B D K D; Col.
    cut (Col D C B); [Col|].
    apply cop_per2__col with A; Perp.
    + apply coplanar_pseudo_trans with B K D; Col; Cop.
    + apply rect_per1 with K, rect_permut; auto.
  }
assert (HEP2 : C = K <-> c = k).
  {
  split; intro; treat_equalities.
  - assert (HPer1 : Per B A C) by (apply rect_per1 with D; auto).
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
    + apply coplanar_pseudo_trans with a k d; Cop.
    + apply rect_per3 with d; do 2 apply rect_permut; auto.
  - assert (HPer1 : Per b a c) by (apply rect_per1 with d; auto).
    assert (HPer2 : Per B A C).
      {
      apply l8_10 with b a c; Perp.
      destruct HC3 as [HC3 [HC4 HC5]]; split; [|split]; Cong.
      }
    assert (HNC3 : ~ Col A K D)
      by (apply per_not_col; auto; apply rect_per4 with B; auto).
    apply l6_21 with A K D K; Col.
    cut (Col C K A); [Col|].
    apply cop_per2__col with B; Perp.
    + apply coplanar_pseudo_trans with A K D; Cop.
    + apply rect_per3 with D; do 2 apply rect_permut; auto.
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
assert (HR3 : Rectangle B HC C D).
  {
  do 2 apply rect_permut; apply cop_perp3__rect; Cop.
  - apply perp_col4 with K D D B; Col; Perp.
    cut (Per K D B); [apply per_perp; auto|].
    apply rect_per4 with A; do 3 apply rect_permut; auto.
  - apply perp_col4 with D B B A; Col; Perp.
    cut (Per D B A); [apply per_perp; auto|].
    apply rect_per4 with K; do 2 apply rect_permut; auto.
  - apply perp_col4 with A B C HC; Col; Perp; assert_diffs; auto.
  }
destruct (l8_18_existence a b c) as [Hc [HC5 HPerp2]]; [Col|].
assert (HPar3 : Par a k c Hc).
  {
  apply l12_9 with a b; Cop; Perp.
  apply coplanar_pseudo_trans with d k b; Cop.
  - cut (~ Col b d k); [Col|apply per_not_col; auto].
    apply rect_per2 with a, rect_permut; auto.
  - cut (Perp b a a k); [Perp|].
    cut (Per b a k); [apply per_perp; auto|].
    apply rect_per1 with d; auto.
  }
assert (HPar4 : Par b d c Hc).
  {
  apply l12_9 with a b; Cop; Perp.
  - cut (Par a b c d); [Cop|].
    apply par_col4__par with a b d k; Col.
    apply Rectangle_Parallelogram, plg_par in HR2; spliter; Par.
  - cut (Perp a b b d); [Perp|].
    cut (Per a b d); [apply per_perp; auto|].
    apply rect_per2 with k; auto.
  }
assert (HaHc : a <> Hc).
  {
  intro; treat_equalities; apply Hck.
  apply l6_21 with a k d k; Col.
  apply per_not_col; auto.
  apply rect_per4 with b; auto.
  }
assert (HbHc : b <> Hc).
  {
  intro; treat_equalities; apply Hcd.
  apply l6_21 with b d k d; Col.
  apply per_not_col; auto.
  apply rect_per2 with a, rect_permut; auto.
  }
assert (HR4 : Rectangle b Hc c d).
  {
  do 2 apply rect_permut; apply cop_perp3__rect; Cop.
  - apply perp_col4 with k d d b; Col; Perp.
    cut (Per k d b); [apply per_perp; auto|].
    apply rect_per4 with a; do 3 apply rect_permut; auto.
  - apply perp_col4 with d b b a; Col; Perp.
    cut (Per d b a); [apply per_perp; auto|].
    apply rect_per4 with k; do 2 apply rect_permut; auto.
  - apply perp_col4 with a b c Hc; Col; Perp; assert_diffs; auto.
  }
assert (HC6 : Cong C HC c Hc).
  {
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
    - apply l11_16; try solve [assert_diffs; auto].
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
intro HNCol.
apply not_col_distincts in HNCol; destruct HNCol as [HNCol [HNAB [HNBC HNAC ]]].
assert (HPar1 : exists N : Tpoint, Par A B C N) by (apply parallel_existence1; auto).
destruct HPar1 as [N HPar1].

assert (HPerp1 : exists X : Tpoint, Perp A B X B /\ Coplanar A B C X) by (apply ex_perp_cop; auto).
destruct HPerp1 as [X [HPerp1 HCop1]].
assert (HCop2 : Coplanar B C N X) by (apply coplanar_trans_1 with A; CopR).
assert (HPerp2 : Perp C N B X) by (apply cop_par_perp__perp with A B; Perp; Par; Cop).
assert (HD : exists D : Tpoint, Col C N D /\ Col B X D /\ Perp_at D C N B X)
  by (apply perp_inter_perp_in_n; Perp).
destruct HD as [D [HDCol1 [HDCol2 HPerp3]]].

assert (HPerp4 : exists Y : Tpoint, Perp A B Y A /\ Coplanar A B C Y) by (apply ex_perp_cop; auto).
destruct HPerp4 as [Y [HPerp4 HCop3]].
assert (HCop4 : Coplanar A C N Y) by (apply coplanar_trans_1 with B; Col; CopR).
assert (HPerp5 : Perp C N A Y) by (apply cop_par_perp__perp with A B; Perp; Par; Cop).
assert (HK : exists K : Tpoint, Col A Y K /\ Col C N K /\ Perp_at K A Y C N)
  by (apply perp_inter_perp_in_n; Perp).
destruct HK as [K [HKCol1 [HKCol2 HPerp6]]]; assert_diffs.
assert (HNBD : B <> D).
  {
  intro; treat_equalities.
  assert (HCol : Col A B C /\ Col A B N) by (apply not_strict_par with B; Par; Col).
  destruct HCol; auto.
  }
assert (HNAK : A <> K).
  {
  intro; treat_equalities.
  assert (HCol : Col A B C /\ Col A B N) by (apply not_strict_par with A; Par; Col).
  destruct HCol; auto.
  }
destruct (segment_construction D B B C) as [C' [HDBC' HC1]].
destruct (segment_construction K A B C) as [G [HKAG HC2]].
destruct (symmetric_point_construction A B) as [SAB HSAB].
assert (HNCol' : ~ Col B C' SAB).
  {
  cut (~ Col A B D); [intros HNC HF; apply HNC; ColR|].
  elim (eq_dec_points C D); [intro; treat_equalities; Col|intro HCD].
  apply par_strict_not_col_4 with C.
  apply par_not_col_strict with C; Col.
  apply par_col4__par with A B C N; Col.
  }
assert (HA' : exists A' : Tpoint, Cong_3 B C A B C' A' /\ OS B C' SAB A')
  by (apply l10_16; Col; Cong).
destruct HA' as [A' [HCong3 HOS1]].
assert (HPar2 : exists M : Tpoint, Par B C' A' M) by (apply parallel_existence1; assert_diffs; auto).
destruct HPar2 as [M HPar2].

assert (HPerp7 : Perp A B B D) by (apply perp_col1 with X; auto; Perp).
assert (HPerp8 : Perp A B B C')
  by (apply bet_col in HDBC'; apply perp_col1 with D; assert_diffs; auto; Col).

assert (HCop5 : Coplanar A' B A M).
  {
  apply par__coplanar in HPar2; apply perp__coplanar in HPerp8.
  apply coplanar_perm_1; apply os__coplanar in HOS1; assert_diffs.
  assert (HCop6 : Coplanar A' C' B A) by (apply col_cop__cop with SAB; Cop; Col).
  apply coplanar_trans_1 with C'; Cop.
  intro; treat_equalities.
  apply cong_3_sym in HCong3.
  assert (HCol : Col B C A) by (apply l4_13 with B C' A'; auto; Col).
  Col.
  }

assert (HPerp9 : Perp A B A' M)
  by (apply perp_sym; apply cop_par_perp__perp with B C'; Par; Perp; Cop).
assert (HF : exists F : Tpoint, Col A B F /\ Col A' M F /\ Perp_at F A B A' M)
  by (apply perp_inter_perp_in_n; Perp).
destruct HF as [F [HFCol1 [HFCol2 HPerp10]]].

assert (HPerp11 : Perp A B B D)
  by (apply perp_right_comm in HPerp1; apply perp_col1  with X; auto; Perp; Col).
assert (HP1 : Per A B D) by (apply perp_per_2; Perp).
assert (HP2 : Per A B C').
  {
  apply per_suppa__per with D B A; Perp.
  apply bet__suppa; auto; assert_diffs; auto.
  }
assert (HPerp12 : Perp B A A K)
  by (apply perp_left_comm in HPerp4; apply perp_col1  with Y; auto; Perp; Col).
assert (HP3 : Per B A K) by (apply perp_per_2; Perp).
assert (HP4 : Per B A G).
  {
  apply per_suppa__per with K A B; Perp.
  apply bet__suppa; auto; assert_diffs; auto.
  }
assert (HNDK : D <> K).
  intro; treat_equalities.
  apply l8_2 in HP1; apply l8_2 in HP3.
  assert (HAB : A = B).
  apply l8_7 with D; Perp.
  auto.
assert (HPar3 : Par A B K D).
  {
  elim (eq_dec_points C D).
  -intro; treat_equalities.
   elim (eq_dec_points C K).
   +intro; treat_equalities.
    assert (HPerp13 : Perp A B B C) by (apply perp_col1 with X; auto; Perp; Col).
    assert (HPerp14 : Perp A B A C) by (apply perp_col1 with Y; auto; Perp; Col).
    assert (HCol : Col C A B) by (apply cop_perp2__col with A B; Cop; Perp).
    exfalso; Col.
   +intro; apply par_right_comm; apply par_col_par with N; Par.
  -intro.
   elim (eq_dec_points C K).
   +intro; treat_equalities.
    apply par_col_par with N; auto.
   +intro.
    apply par_col_par with C; auto.
    apply par_right_comm; apply par_col_par with N; auto.
    assert (HCol : Col C D K) by (apply col_transitivity_1 with N; auto).
    Col.
  }
assert (HS : Saccheri B C' G A).
  {
  unfold Saccheri; do 2 (split; Perp).
  split; [apply cong_inner_transitivity with B C; Cong|].
  assert (HNC1 : ~ Col C' B A) by (apply per_not_col; assert_diffs; auto; Perp).
  assert (HNC2 : ~ Col D B A) by (apply per_not_col; auto; Perp).
  assert (HNC3 : ~ Col B A G) by (apply per_not_col; Perp; assert_diffs; auto).
  assert (HNC4 : ~ Col B A K) by (apply per_not_col; Perp).
  apply l9_8_1 with D.
  do 2 (split; auto); exists B; split; Col; Between.
  assert (HTS1 :TS B A K G) by (do 2 (split; Col); exists A; split; Col; Between).
  apply l9_2; apply l9_8_2 with K; auto.
  assert (HPS : Par_strict B A K D) by (apply par_not_col_strict with K; Par; Col).
  apply l12_6; auto.
  }
assert (HNCol1 : ~ Col B C' A').
  {
  intro; apply cong_3_sym in HCong3.
  assert (HC : Col B C A) by (apply l4_13 with B C' A'; auto).
  Col.
  }
assert (HNCol2 : ~ Col A B C') by (apply per_not_col; Perp; assert_diffs; auto).
assert (HCop6 : Coplanar C' G A' M) by (apply coplanar_pseudo_trans with A B C'; Cop; CopR).
assert (HCop7 : Coplanar K D A' M).
  {
  assert (HNC : ~ Col A B C') by (apply per_not_col; Perp; assert_diffs; auto).
  apply coplanar_pseudo_trans with A B C'; Cop; [|CopR..].
  apply coplanar_pseudo_trans with A B D; Cop.
  apply per_not_col; Perp; assert_diffs; auto.
  }
assert (HPar4 : Par B A C' G) by (apply sac__par1423; auto); apply par_left_comm in HPar4.
assert (HPerp13 : Perp C' G A' M) by (apply cop_par_perp__perp with A B; Par).
assert (HL : exists L : Tpoint, Col C' G L /\ Col A' M L /\ Perp_at L C' G A' M)
  by (apply perp_inter_perp_in_n; Perp).
destruct HL as [L [HLCol1 [HLCol2 HPerp14]]].

assert (HPerp15 : Perp K D A' M) by (apply cop_par_perp__perp with A B; Par).
assert (HE : exists E : Tpoint, Col K D E /\ Col A' M E /\ Perp_at E K D A' M)
  by (apply perp_inter_perp_in_n; Perp).
destruct HE as [E [HECol1 [HECol2 HPerp16]]].
apply cong_3_swap in HCong3.
assert (HCA1 : CongA A B C A' B C') by (apply conga_comm; apply cong3_conga; auto).
assert (HNBF : B <> F).
  {
  intro; treat_equalities.
  assert (HC : Col B C' A') by (apply not_strict_par1 with M B; Col).
  auto.
  }

assert (HTS2: TS B C' A F).
  {
  apply l9_2; apply l9_8_2 with SAB; apply midpoint_bet in HSAB.
  do 2 (split; Col); exists B; split; Col; Between.
  apply one_side_transitivity with A'; auto.
  elim (eq_dec_points A' F).
  intro; treat_equalities; apply one_side_reflexivity; Col.
  intro.
  assert (HPar5 : Par B C' A' F) by (apply par_col_par with M; auto).
  assert (HParS : Par_strict B C' A' F) by (apply par_not_col_strict with A'; Col).
  apply l12_6; auto.
  }
assert (HCop8 : Coplanar C' A' F B).
  {
  elim (eq_dec_points A' F).
  - intro; treat_equalities; Cop.
  - intro.
    assert (HPar5 : Par B C' A' F) by (apply par_col_par with M; auto).
    apply par__coplanar in HPar5; auto; Cop.
  }
assert (HB : Bet A B F) by (apply col_two_sides_bet with C'; Col).
assert (HR1 : Rectangle A B D K).
  {
  apply rect_permut, rect_permut, cop_perp3__rect; Cop; Perp.
  apply cop_par_perp__perp with A B; Par; Perp; Cop.
  }
elim (eq_dec_points C D).     (* Séparation C <> D *)
- intro; treat_equalities.
  assert (HP5 : Per A' B C') by (apply l11_17 with A B C; auto).
  assert (HP6 : Per C' B F)
    by (apply per_suppa__per with A B C'; Perp; apply bet__suppa; assert_diffs; auto).
  assert (HCol1 : Col A' F B) by (apply cop_per2__col with C'; assert_diffs; Perp).
  assert (HNCol3 : ~ Col B A' M)
    by (intro; assert (HCol : Col B C' A') by (apply not_strict_par1 with M B; Par; Col); auto).
  assert (HA'F : A' = F) by (apply col2__eq with B M; Col).
  treat_equalities; exists C, K, K, A; split; [|split]; [split; Col..|].
  + apply rect_permut; auto.
  + destruct (EqR_perm A B C K); spliter; auto.
- intro.
assert (HND : B <> D).
  {
  intro; treat_equalities.
  assert (HPar5 : Par A B C B) by (apply par_col_par with N; auto).
  assert (HC : Col A B C) by (apply not_strict_par1 with B B; Col).
  Col.
  }
assert (HP5 : Per C D B) by (apply perp_in_per_1 in HPerp3; Perp).
assert (HP6 : Per C D B) by (apply perp_in_per_1 in HPerp3; Perp).
assert (HNA'F : A' <> F).
  {
  intro; treat_equalities.
  assert (HP6 : Per C' B A')
    by (apply per_suppa__per with A B C'; Perp; apply bet__suppa; assert_diffs; auto).
  assert (HP7 : Per A B C) by (apply l11_17 with A' B C'; Perp; CongA).
  assert (Hcop8 : Coplanar A B C D).
    {
    assert (HPar6 : Par A B C D) by (apply par_col_par with N; auto).
    apply par__coplanar in HPar6; auto.
    }
  assert (HC : Col D C B) by (apply cop_per2__col with A; Cop; Perp).
  assert (HP : C = D \/ B = D) by (apply l8_9; Perp; Col).
  destruct HP; auto.
  }
assert (HCA2 : CongA C B D F B A').
  {
  apply conga_left_comm, (l11_22 D B C A F B A' C').
  split; [right; split|split; CongA].
  - apply l12_6, par_not_col_strict with C; Col.
    apply par_col4__par with A B C N; Col.
  - apply l12_6, par_not_col_strict with A'; Col.
    apply par_col4__par with B C' A' M; Col; assert_diffs; auto.
  - apply l11_16; Perp; [|assert_diffs; auto].
    cut (Perp F B B C'); [Perp|].
    apply perp_in_perp_bis in HPerp10.
    destruct HPerp10 as [HPerp10|HPerp10].
    + cut (Perp B C' B F); [Perp|].
      apply cop_par_perp__perp with A' M; Cop; Par; Perp.
    + apply perp_col4 with A F B C'; Col; [assert_diffs; auto|].
      cut (Perp B C' A F); [Perp|].
      apply cop_par_perp__perp with A' M; Cop; Par; Perp.
  }
assert (HNCol3 : ~ Col B D C)
  by (intro; assert (HP : C = D \/ B = D) by (apply l8_9; Col); destruct HP; auto).
assert (HP7 : Per B F A') by (apply perp_in_per_3 in HPerp10; auto).
assert (HCA3 : CongA B D C B F A') by (apply l11_16; Perp).
assert (HEQF : EqF B D B C B F B A') by (apply CongA2__EqF; CongA).
apply EqF_sym in HEQF; apply interchange_theorem in HEQF.
destruct HEQF as [P [Q [R [p [q [r HI]]]]]]; spliter.

assert (HCol : Col C D K) by (apply col_transitivity_1 with N; Col).
assert (HPS : Par_strict A B K D) by (apply par_not_col_strict with C; auto; Col).
assert (HNEF :  E <> F).
  {
  intro; treat_equalities.
  assert (HNC : ~ Col E K D) by (apply par_not_col with A B; Col).
  Col.
  }
assert (HNDE : D <> E).
  {
  intro; treat_equalities.
  apply (not_strict_par1 _ _ _ _ D) in HPar2; Col.
  }
assert (HCol1 : Col A' E F) by ColR.
assert (HNCol4 : ~ Col B D E).
  {
  cut (Par_strict A B D E); [apply par_strict_not_col_2|].
  apply par_strict_col2_par_strict with D K; Col; Par.
  }
assert (HPar7 : Par B D E F) by (apply par_col4__par with B C' A' M; Col).
assert (HPar8 : Par D E B F)
  by (apply par_col_par_2 with K; Col; apply par_col_par with A; Col; Par).
assert (HPA1 : Parallelogram B D E F) by (apply par_2_plg; Par).
assert (HPA2 : Parallelogram B C' G A) by (apply sac_plg; auto).
assert (HC3 : Cong B D E F) by (apply plg_cong_1 in HPA1; auto).
assert (HC4 : Cong P R E F) by (apply cong_inner_transitivity with B D; Cong).
assert (HC5 : Cong p q G C').
  {
  apply cong_inner_transitivity with B A'; Cong.
  apply cong_inner_transitivity with A B; unfold Cong_3 in HCong3; spliter; Cong.
  apply plg_cong_2 in HPA2; Cong.
  }
assert (HC6 : Cong p r B C') by (apply cong_inner_transitivity with B C; Cong).
assert (HEQF3 : EqF F B F E C' G C' B) by (exists P, Q, R, p, q, r; do 4 (split; Cong); auto).
assert (HP8 : Per B F E).
  {
  cut (Perp B F F E); [Perp|].
  apply perp_col4 with B F F A'; Col; Perp.
  }
assert (HP9 : Per B C' G)
  by (apply sac_rectangle in HS; apply rect_per2 in HS; auto).
assert (HCA4 : CongA F E B C' B G /\ CongA F B E C' G B)
  by (apply Per2_EqF__CongA; Perp; apply EqF_abcd_badc; auto).
destruct HCA4 as [HCA4 HCA5].
destruct (parallel_existence1 B C A) as [h hP]; [assert_diffs; auto|].
assert (HNC1 : ~ Col A B h)
  by (intro; apply (not_strict_par1 _ _ _ _ B) in hP; Col).
destruct (l8_18_existence A h B) as [k [HCol2 HPerp17]]; Col.
assert (HNC2 : ~ Col A C h)
  by (intro; apply (not_strict_par1 _ _ _ _ C) in hP; Col).
destruct (l8_18_existence A h C) as [d [HCol3 HPerp18]]; Col.
assert (HPar9 : Par B C d k).
  {
  apply par_col4__par with B C A h; Col; intro; treat_equalities.
  assert (HCol3 : Col d B C) by (apply cop_perp2__col with A h; Cop; Perp).
  apply (not_strict_par _ _ _ _ d) in hP; spliter; Col.
  }
assert (HPerp19 : Perp C d d k)
  by (apply perp_col4 with C d A h; Col; Perp; assert_diffs; auto).
assert (HPerp20 : Perp B k k d)
  by (apply perp_col4 with B k A h; Col; Perp; assert_diffs; auto).
assert (HR2 : Rectangle B C d k).
  {
  apply cop_perp3__rect; Cop; Perp.
  apply cop_par_perp__perp with d k; Par; Perp; Cop.
  }
exists D, K, d, k.
split; [split; Col|split; [split; [auto|ColR]|apply EqR_sym]].
assert (HCd : C <> d).
  {
  intro; treat_equalities.
  apply degenerated_rect_eq in HR2; treat_equalities; Col.
  }
apply EqR_trans with k B C d; [destruct (EqR_perm B C d k); spliter; auto|].
assert (HBk : B <> k).
  {
  intro; treat_equalities; do 2 apply rect_permut in HR2.
  apply degenerated_rect_eq in HR2; treat_equalities; Col.
  }
split; [auto|split; [auto|split; [do 3 apply rect_permut; auto|]]].
do 3 (split; [auto|]).
assert (HR3 : Rectangle F B C' L).
  {
  assert (HPar10 : Par F L B C').
    {
    apply par_col4__par with E F B D; Col; Par; [|assert_diffs; auto|ColR].
    intro; treat_equalities.
    apply (par_not_col_strict _ _ _ _ C') in HPar4; Col.
    apply (par_not_col _ _ _ _ F HPar4); Col.
    }
  apply plg_per_rect2; [|apply l8_2, l8_3 with A; Col; Perp].
  apply pars_par_plg; [|Par].
  apply par_not_col_strict with C'; Col; [|intro; apply HNCol2; ColR].
  apply par_col4__par with A B C' G; Col.
  assert (HParS : Par_strict B C' F L)
    by (apply par_not_col_strict with A'; Col; Par; ColR).
  intro; treat_equalities; apply (par_not_col _ _ _ _ C' HParS); Col.
  }
assert (HC7 : Cong k B F B).
  {
  cut (Cong B k B F); [Cong|].
  apply (Cong_3_same_height C B A k d C' B A' F L); Col; [|ColR| |ColR].
  - apply rect_comm2; auto.
  - apply rect_comm2, rect_permut; auto.
  }
exists F, B, A, K, D, E, G, L, C'; do 3 (split; [Cong|]).
split; [apply rect_comm2; auto|split; [Cong|]].
split; [apply Rectangle_Parallelogram, plg_cong in HR1; spliter; Cong|].
assert (HFL : F <> L).
  {
  intro; treat_equalities.
  apply rect_permut, rect_permut, degenerated_rect_eq in HR3.
  treat_equalities; Col.
  }
assert (HGC'L : Bet G C' L).
  {
  apply col_two_sides_bet with B; [ColR|].
  apply l9_8_2 with A; [apply l9_2, l9_8_2 with F|]; [Side|apply l12_6..].
  - apply par_not_col_strict with A'; Col; [|ColR].
    apply par_col4__par with B C' A' M; Col; assert_diffs; auto.
  - apply par_not_col_strict with A; Col.
    apply par_col4__par with B D A K; Col; [assert_diffs; auto..|].
    apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
  }
assert (HEDK : Bet E D K).
  {
  apply col_two_sides_bet with B; [ColR|].
  apply l9_8_2 with F; [apply l9_2, l9_8_2 with A|]; [|apply l12_6..].
  - apply col_preserves_two_sides with B C'; Col; Side.
  - apply par_not_col_strict with A; Col.
    + apply Rectangle_Parallelogram, plg_par in HR1; spliter; Par.
    + cut (~ Col B A D); [Col|apply perp_not_col; Perp].
  - cut (Par_strict E F B D); [Par|].
    apply par_not_col_strict with B; Col; Par.
    cut (~ Col F B E); [Col|apply perp_not_col].
    apply perp_col4 with F B F L; Col; [ColR|].
    cut (Perp B F F L); [Perp|].
    cut (Per B F L); [apply per_perp; assert_diffs; auto|].
    apply rect_per1 with C'; auto.
  }
assert (EFL : Bet E F L).
  {
  apply col_two_sides_bet with B; [ColR|].
  apply l9_8_2 with K; [apply l9_2, l9_8_2 with G|]; [|apply l12_6..].
  - split; [|split].
    + intro; apply (par_not_col_strict _ _ _ _ C') in HPar4; Col.
      apply (par_not_col _ _ _ _ G HPar4); Col; ColR.
    + intro; apply (par_not_col_strict _ _ _ _ C) in HPar1; Col.
      apply (par_not_col _ _ _ _ K HPar1); Col; ColR.
    + exists A; split; [Col|Between].
  - apply par_not_col_strict with C'; Col; [|intro; apply HNCol2; ColR].
    apply par_col4__par with A B C' G; Col.
    intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in HR3; treat_equalities; auto.
  - apply par_not_col_strict with C; Col; [..|intro; apply HNCol]; [|ColR..].
    apply par_col4__par with A B K D; Col.
    intro; treat_equalities; auto.
  }
repeat split; Between; apply between_symmetry.
assert (HNC : ~ Col B F L).
  {
  apply per_not_col; [intro; treat_equalities; auto..|].
  apply rect_per1 with C'; auto.
  }
apply CongA_OS_ParTS__Bet with C' F; CongA.
+ apply ncol124_plg__plgs in HPA2; [|Col].
  apply l9_8_1 with A.
  * apply plgs_two_sides in HPA2; spliter; Side.
  * apply invert_two_sides, bet__ts; Between.
    cut (~ Col B F G); [Col|apply par_strict_not_col_1 with C'].
    apply par_not_col_strict with L; Col.
    apply par_col4__par with A B C' G; Col; assert_diffs; auto.
+ apply par_col4__par with C' G A B; Col; Par; assert_diffs; auto.
+ apply l9_8_2 with L.
  * split; [intro; apply HNC; ColR|].
    split; [intro; apply HNC; ColR|].
    exists F; split; [Col|Between].
  * apply l12_6; apply par_not_col_strict with L; Col.
    apply par_col4__par with A B C' G; Col; assert_diffs; auto.
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
assert (HNBD : B <> D).
  {
  intro; treat_equalities.
  assert (HAK : A = K) by (apply degenerated_rect_eq with B; auto).
  treat_equalities; Col.
  }
assert (HR2 : Rectangle a b d k) by (destruct H2; auto).
assert (HC2 : Col c d k) by (destruct H2; auto).
assert (HNbd : b <> d).
  {
  intro; treat_equalities.
  assert (Hak : a = k) by (apply degenerated_rect_eq with b; auto).
  treat_equalities; Col.
  }
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
assert (HNBD : B <> D).
  {
  intro; treat_equalities.
  assert (HAK : A = K) by (apply degenerated_rect_eq with B; auto).
  treat_equalities; Col.
  }
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
  destruct HP.
  destruct H6; auto.
  destruct H6; auto.
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
assert (HNCol2 : ~ Col E B F).
  {
  intro; treat_equalities.
  destruct HEQT as [D [K [d [k [ HF1 [HF2 HEQR]]]]]].
  assert (HNP : A <> B /\ B <> D /\ E <> B /\ B <> d) by (apply EqR_diffs in HEQR; auto); spliter.
  destruct HF2.
  assert (HPA : Parallelogram E B d k) by (apply Rectangle_Parallelogram in H4; auto).
  assert (HPar1 :Par E B d k) by (apply plg_par_1; auto).
  cut (Col E B d).
  intro; assert (HPF : Parallelogram_flat E B d k) by (apply plg_col_plgf; auto).
  assert (HP : E = k /\ B = d \/ E = B /\ k = d) by (apply plgf_rect_id; auto).
  destruct HP; destruct H7; auto.
  assert (HC : Col E B d /\ Col E B k) by (apply not_strict_par with F; Col); spliter; auto.
  }
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
- assert (HCD : C <> D).
    {
    intro; treat_equalities.
    apply degenerated_rect_eq in H; treat_equalities; Col.
    }
  assert (Hdk : d <> k).
    {
    intro; treat_equalities.
    apply rect_permut, degenerated_rect_eq in H1; treat_equalities; Col.
    }
  assert (HdF : d <> F).
    {
    intro; treat_equalities.
    apply degenerated_rect_eq in H1; treat_equalities; Col.
    }
  assert (HP1 : Par B C d k).
    {
    apply par_col4__par with B F d k; Col; [assert_diffs; auto|].
    apply Rectangle_Parallelogram, plg_par in H1; spliter; Par.
    assert_diffs; auto.
    }
  assert (HCop : Coplanar d k D C).
    {
    apply coplanar_pseudo_trans with B C E; Cop.
    - intro; apply HNCol2; ColR.
    - elim (eq_dec_points d E); [intro; treat_equalities; Cop|intro HdE].
      cut (Par B C E d); [Cop|].
      apply par_col4__par with B C d k; Col; assert_diffs; auto.
    - elim (eq_dec_points E k); [intro; treat_equalities; Cop|intro HEk].
      cut (Par B C E k); [Cop|].
      apply par_col4__par with B C d k; Col; assert_diffs; auto.
    - elim (eq_dec_points A D); [intro; treat_equalities; Cop|intro HAD].
      apply coplanar_pseudo_trans with A B C; Cop.
      cut (Par A D B C); [Cop|].
      apply par_col4__par with D K B C; Col; [assert_diffs; auto|].
      apply Rectangle_Parallelogram, plg_par in H; spliter; Par.
      assert_diffs; auto.
    }
  assert (HNP : ~ Par d k D C).
    {
    apply perp_not_par, cop_par_perp__perp with B C; Cop.
    cut (Perp B C C D); [Perp|].
    cut (Per B C D); [apply per_perp; assert_diffs; auto|].
    apply rect_per2 with K; auto.
    }
  destruct (cop_npar__inter_exists d k D C HCop HNP) as [d' [HC1 HC2]].
  assert (HC3 : Col B K k).
    {
    elim (eq_dec_points B k); [intro; treat_equalities; Col|intro HBk].
    cut (Col k K B); [Col|apply cop_per2__col with C].
    - apply coplanar_pseudo_trans with B C E; Cop.
      + intro; apply HNCol2; ColR.
      + elim (eq_dec_points E k); [intro; treat_equalities; Cop|intro HEk].
        cut (Par B C E k); [Cop|].
        apply par_col4__par with B F d k; Col; [assert_diffs; auto|].
        apply Rectangle_Parallelogram, plg_par in H1; spliter; Par.
        assert_diffs; auto.
      + apply coplanar_pseudo_trans with A B C; Cop.
        elim (eq_dec_points A K); [intro; treat_equalities; Cop|intro HAK].
        cut (Par B C A K); [Cop|].
        apply par_col4__par with B C D K; Col; [assert_diffs; auto|].
        apply Rectangle_Parallelogram, plg_par in H; spliter; Par.
        assert_diffs; auto.
    - assert_diffs; auto.
    - cut (Perp k B B C); [Perp|].
      apply perp_col4 with k B B F; Col; [assert_diffs; auto|].
      cut (Per k B F); [apply per_perp; assert_diffs; auto|].
      apply rect_per1 in H1; Perp.
    - apply rect_per1 in H; Perp.
    }
  assert (HBK : B <> K).
    {
    intro; treat_equalities.
    apply rect_permut, rect_permut, degenerated_rect_eq in H; auto.
    }
  assert (Hd'k : d' <> k).
    {
    assert (HP : Per K B C) by (apply rect_per1 in H; Perp).
    assert (HParS : Par_strict B K C D).
      {
      apply col_cop_perp2__pars with C B; Col; Cop.
      - cut (~ Col K B C); [Col|apply per_not_col; assert_diffs; auto].
      - cut (Perp K B B C); [Perp|apply per_perp; assert_diffs; auto].
      - cut (Perp B C C D); [Perp|apply per_perp; [assert_diffs; auto..|]].
        apply rect_per2 in H; auto.
      }
    intro; treat_equalities.
    apply (par_not_col _ _ _ _ d' HParS); Col.
    }
  assert (HNCol3 : ~ Col d k B).
    {
    apply per_not_col; [assert_diffs; auto|..].
    - intro; treat_equalities.
      apply rect_permut, rect_permut, degenerated_rect_eq in H1; auto.
    - apply rect_per4 in H1; Perp.
    }
  assert (HB : Bet C d' D).
    {
    apply col_two_sides_bet with k; Col.
    apply col_preserves_two_sides with d k; Col.
    assert (HOS : OS d k A D).
      {
      elim (eq_dec_points A D); [intro; treat_equalities|intro HAD].
      - apply one_side_reflexivity; intro; apply HNCol3; ColR.
      - apply l12_6, par_not_col_strict with A; Col.
        + apply par_trans with B C; Par.
          apply par_col4__par with B C D K; Col; [assert_diffs; auto|].
          apply Rectangle_Parallelogram, plg_par in H; spliter; Par.
          assert_diffs; auto.
        + intro; apply HNCol3; ColR.
      }
    apply l9_2, l9_8_2 with A; [apply l9_2, l9_8_2 with B|Side].
    - split; [intro; apply HNCol3; ColR|].
      split; [intro; apply HNCol3; ColR|].
      exists E; split; [Col|Between].
    - apply l12_6, par_not_col_strict with B; Col; Par.
    }
  assert (HCong : Cong C d' F d).
    {
    cut (Rectangle C d' d F); [intro HR|].
    - apply Rectangle_Parallelogram, plg_cong in HR; spliter; Cong.
    - assert (Per C F d).
        {
        cut (Perp C F F d); [Perp|].
        apply perp_col4 with B F F d; Col.
        cut (Per B F d); [apply per_perp; assert_diffs; auto|].
        apply rect_per2 with k; auto.
        }
      apply plg_per_rect3; [apply parallelogram_to_plg|auto].
      assert (HPS : Par_strict d F C d').
        {
        apply par_not_col_strict with C; Col.
        - apply par_trans with B K.
          + apply par_col4__par with d F B k; Col.
            apply Rectangle_Parallelogram, plg_par in H1; spliter; Par.
            assert_diffs; auto.
          + apply par_col4__par with B K C D; Col.
            * intro; treat_equalities; apply HNCol3.
              apply not_strict_par1 with C C; Col; Par.
            * apply Rectangle_Parallelogram, plg_par in H; spliter; Par.
              assert_diffs; auto.
        - apply per_not_col; Perp.
        }
      do 2 apply plg_permut; apply par_2_plg; Par.
      + cut (~ Col B F d); [intros HNC HF; apply HNC; ColR|].
        apply per_not_col; [assert_diffs; auto..|].
        apply rect_per2 in H1; Perp.
      + apply par_col4__par with d k B F; Col.
        * intro; treat_equalities; apply (par_not_col _ _ _ _ d HPS); Col.
        * apply Rectangle_Parallelogram, plg_par in H1; spliter; Par.
          assert_diffs; auto.
    }
  apply cong2_lt__lt with C d' C D; Cong.
  apply bet__lt1213; Between.
  cut (D <> d'); auto; intro; treat_equalities.
  assert (HP2 : Par D K d k).
    {
    apply par_trans with B C; Par.
    apply Rectangle_Parallelogram, plg_par in H; spliter; Par.
    assert_diffs; auto.
    }
  apply HNAE, l6_21 with d k B A; Col; [assert_diffs; auto|].
  cut (Col d k K); [intro; ColR|].
  apply not_strict_par2 with D D; Col; Par.
Qed.

Definition Convex J K L M := exists E, Bet J E L /\ Bet K E M.

Definition circumscribed_rectangle J K L M A B C D :=
  Convex J K L M /\
  (First_circumscribed_rectangle J L K A B /\
   First_circumscribed_rectangle J L M D C \/
   First_circumscribed_rectangle K M J A B /\
   First_circumscribed_rectangle K M L D C).

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
clear J K L M A B C D; intros J K L M A B C D HNCE HC [HR1 HC1] [HR2 HC2].
assert (HAB : A <> B).
  {
  apply Rectangle_Parallelogram, plg_cong in HR1.
  intro; spliter; treat_equalities; destruct HNCE; Col.
  }
assert (HCD : C <> D).
  {
  apply Rectangle_Parallelogram, plg_cong in HR2.
  intro; spliter; treat_equalities; destruct HNCE; Col.
  }
assert (HJL : J <> L).
  {
  intro; destruct HNCE as [HF|HNC]; [treat_equalities; Col|apply HNC].
  destruct HC as [I [HB1 HB2]]; treat_equalities; Col.
  }
assert (HKM : K <> M).
  {
  destruct HC as [I [HB1 HB2]]; intro; treat_equalities.
  destruct HNCE as [HF|HF]; apply HF; Col.
  }
assert (HC3 : Col A D L).
  {
  apply cop_per2__col with J; [|assumption|..].
  - elim (col_dec J L A); [Cop|intro HNC1].
    elim (col_dec J L D); [Cop|intro HNC2].
    assert (HLA : L <> A) by (intro; treat_equalities; Col).
    assert (HLD : L <> D) by (intro; treat_equalities; Col).
    apply coplanar_pseudo_trans with J L K; Cop;
    [| |apply coplanar_pseudo_trans with J L M; Cop].
    + intro HF; apply HNC1.
      apply Rectangle_Parallelogram, plg_par_1 in HR1; [|assumption..].
      apply (not_strict_par1 _ _ _ _ K) in HR1; Col.
    + elim (eq_dec_points A K); [intro; treat_equalities; Cop|intro HAK].
      cut (Par J L K A); [Cop|].
      apply Rectangle_Parallelogram, plg_par_1 in HR1; [|assumption..].
      apply par_col4__par with J L A B; Col.
    + intro HF; apply HNC2.
      apply Rectangle_Parallelogram, plg_par_1 in HR2; [|assumption..].
      apply (not_strict_par1 _ _ _ _ M) in HR2; Col.
    + destruct HC as [I [HB1 HB2]]; exists I; left; split; Col.
    + elim (eq_dec_points D M); [intro; treat_equalities; Cop|intro HDM].
      cut (Par J L D M); [Cop|].
      apply Rectangle_Parallelogram, plg_par_1 in HR2; [|assumption..].
      apply par_col4__par with J L C D; Col; Par.
  - apply rect_per1 with B, rect_permut; assumption.
  - apply rect_per1 with C, rect_permut; assumption.
  }
assert (HCP : Col J K L -> Bet A L D).
  {
  intro HC4; cut (A = L); [intro; treat_equalities; Between|].
  destruct HNCE as [HF|HNC]; [exfalso; apply HF; Col|].
  assert (HJKD : ~ Col J L D).
    {
    assert (HLD : L <> D).
      {
      assert (HR := HR2); apply Rectangle_Parallelogram, plg_cong in HR.
      intro; spliter; treat_equalities; apply HNC; Col.
      }
    apply Rectangle_Parallelogram, plg_par_1 in HR2; [|assumption..].
    apply (par_not_col_strict _ _ _ _ M) in HR2; Col.
    apply par_strict_not_col_1 with C; Par.
    }
  elim (eq_dec_points L A); [auto|intro HLA].
  assert (HR := HR1); apply Rectangle_Parallelogram, plg_par in HR;
  [destruct HR as [HPar _]|assumption..].
  apply (not_strict_par _ _ _ _ K) in HPar; Col.
  apply l6_21 with J L D A; Col; [|destruct HPar; Col].
  destruct HPar as [HC5 HC6].
  apply Rectangle_Parallelogram, plg_par in HR2; [|assumption|].
  - destruct HR2 as [HPar _ ].
    apply (par_not_col_strict _ _ _ _ M) in HPar; Col.
    apply (par_not_col _ _ _ _ A) in HPar; Col.
    intro; treat_equalities; Col.
  - intro; treat_equalities; Col.
  }
elim (col_dec J K L); [apply HCP|clear HCP; intro HNC1].
assert (HCP : Col J L M -> Bet A L D).
  {
  intro HC4; cut (L = D); [intro; treat_equalities; Between|].
  destruct HNCE as [HNC|HF]; [|exfalso; apply HF; Col].
  assert (HJKD : ~ Col J L A).
    {
    assert (HLD : L <> A).
      {
      assert (HR := HR1); apply Rectangle_Parallelogram, plg_cong in HR.
      intro; spliter; treat_equalities; apply HNC; Col.
      }
    apply Rectangle_Parallelogram, plg_par_1 in HR1; [|assumption..].
    apply (par_not_col_strict _ _ _ _ K) in HR1; Col.
    apply par_strict_not_col_1 with B; Par.
    }
  elim (eq_dec_points L D); [auto|intro HLD].
  assert (HR := HR2); apply Rectangle_Parallelogram, plg_par in HR;
  [destruct HR as [HPar _]|assumption..].
  apply (not_strict_par _ _ _ _ M) in HPar; Col.
  apply l6_21 with J L A D; Col; [|destruct HPar; Col].
  destruct HPar as [HC5 HC6].
  apply Rectangle_Parallelogram, plg_par in HR1; [|assumption|].
  - destruct HR1 as [HPar _ ].
    apply (par_not_col_strict _ _ _ _ K) in HPar; Col.
    apply (par_not_col _ _ _ _ D) in HPar; Col.
    intro; treat_equalities; Col.
  - intro; treat_equalities; Col.
  }
elim (col_dec J L M); [apply HCP|clear HCP; intro HNC2].
apply col_two_sides_bet with J; [Col|].
apply l9_8_2 with K; [apply l9_2, l9_8_2 with M|].
- split; [Col|split; [Col|]].
  destruct HC as [I [HB1 HB2]]; exists I; split; [Col|Between].
- elim (eq_dec_points D M); [|intro HDM].
  + intro; treat_equalities; apply one_side_reflexivity; Col.
  + apply l12_6, par_not_col_strict with M; [|Col..].
    apply par_col4__par with J L D C; Col; assert (HR := HR2).
    apply Rectangle_Parallelogram, plg_par_1 in HR; Par.
    apply Rectangle_Parallelogram, plg_cong in HR2.
    intro; spliter; treat_equalities; apply HNC2; Col.
- elim (eq_dec_points A K); [|intro HAK].
  + intro; treat_equalities; apply one_side_reflexivity; Col.
  + apply l12_6, par_not_col_strict with K; [|Col..].
    apply par_col4__par with J L A B; Col; assert (HR := HR1).
    apply Rectangle_Parallelogram, plg_par_1 in HR; Par.
    apply Rectangle_Parallelogram, plg_cong in HR1.
    intro; spliter; treat_equalities; apply HNC1; Col.
Qed.

Lemma circumscribed_rectangle__rectangle J K L M A B C D :
  ~ Col J L K \/ ~ Col J L M ->
  circumscribed_rectangle J K L M A B C D ->
  Rectangle A B C D.
Proof.
assert (H : forall J K L M A B C D,
              ~ Col J L K \/ ~ Col J L M ->
              Convex J K L M ->
              First_circumscribed_rectangle J L K A B ->
              First_circumscribed_rectangle J L M D C ->
              Rectangle A B C D).
  {
  clear J K L M A B C D; intros J K L M A B C D HNCE HConvex HR1 HR2.
  apply extent_rect with J L.
  - apply (circumscribed_rectangle__bet L K J M B A D C).
    + destruct HNCE; [left|right]; Col.
    + destruct HConvex as [I []]; exists I; split; Between.
    + apply FCR_ABCDK_BACKD; assumption.
    + apply FCR_ABCDK_BACKD; assumption.
  - destruct HR1 as [HR1 _]; do 2 apply rect_permut; assumption.
  - destruct HR2 as [HR2 _]; apply rect_comm2; assumption.
  }
intros HNCE [HConvex [[HR1 HR2]|[HR1 HR2]]]; [apply (H J K L M); assumption|].
apply (H K J M L); [| |assumption..].
- assert (HNE : J <> L /\ K <> M); [|destruct HNE as [HJL HKM]].
    {
    destruct HConvex as [I []]; split; intro; treat_equalities;
    destruct HNCE as [HF|HF]; apply HF; Col.
    }
  elim (col_dec K M J); [|Col]; elim (col_dec K M L); [|Col].
  intros HC1 HC2; exfalso; cut (Col J L K /\ Col J L M); [|split; ColR].
  intros []; destruct HNCE; Col.
- destruct HConvex as [I []]; exists I; split; Between.
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
assert (HNCE2 : ~ Col K M J \/ ~ Col K M L).
  {
  elim (col_dec K M J); [|Col]; elim (col_dec K M L); [|Col].
  intros HC1 HC2; exfalso; cut (Col J L K /\ Col J L M); [|split; ColR].
  intros []; destruct HNCE1; Col.
  }
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
      assert (ER : EqT D a b a b D) by (apply B6_1; Col).
      destruct ER as [B' [A' [c' [d' [HR3 [HR4 ER]]]]]].
      assert (A = A' /\ B = B'); [|spliter; treat_equalities; clear HR3].
        {
        apply (Circumscribed_rectangle_unique a D b); [|assumption|].
        - assert_diffs; assumption.
        - apply FCR_ABCDK_BACKD; assumption.
        }
      assert (c = c' /\ d = d'); [|spliter; treat_equalities; clear HR4].
        {
        apply (Circumscribed_rectangle_unique a b D); [..|assumption].
        - assert_diffs; assumption.
        - apply FCR_ABCDK_BACKD; assumption.
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
        assert (HRect : Rectangle A B C D).
          {
          apply circumscribed_rectangle__rectangle with b K a M; Col.
          split; [exists K; split; Between|right; split; assumption].
          }
        assert (HAB : A <> B).
          {
          intro; treat_equalities; destruct HR1 as [HF _].
          apply rect_permut, degenerated_rect_eq in HF.
          treat_equalities; tauto.
          }
        destruct (EqR_perm A B C D); [..|spliter]; [assumption| |assumption..].
        assert (HConvex : Convex K b M a) by (exists K; split; Between).
        elim (circumscribed_rectangle__bet K b M a A B C D); [|assumption..].
        intros _ HB2 HBC; treat_equalities.
        apply degenerated_rect_eq in HRect; treat_equalities.
        elim (circumscribed_rectangle__bet B b M a A B B A); [|assumption..].
        intros HB2 _; treat_equalities.
        destruct HR1 as [_ HC1]; destruct HR2 as [_ HC2].
        destruct HNCE as [HF|HF]; apply HF; Col.
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
      destruct (Circumscribed_rectangle_exists b K M) as [N HR4]; [tauto|].
      assert (Hbc : b <> c).
        {
        intro; treat_equalities; destruct HR3 as [HRect HC].
        apply rect_permut, rect_permut, degenerated_rect_eq in HRect.
        treat_equalities; apply HNC2; ColR.
        }
      destruct HR4 as [c' HR4]; assert (c = c'); [|treat_equalities].
        {
        assert (Hab : a <> b) by (intro; treat_equalities; apply HNC1; Col).
        assert (Had : a <> d).
          {
          intro; treat_equalities; destruct HR3 as [HRect _].
          apply degenerated_rect_eq in HRect; treat_equalities; auto.
          }
        assert (Hcd : c <> d).
          {
          intro; treat_equalities; destruct HR3 as [HRect HC].
          apply rect_permut, degenerated_rect_eq in HRect.
          treat_equalities; apply HNC1; Col.
          }
        assert (HbK : b <> K) by (intro; treat_equalities; apply HNC3; Col).
        assert (HKN : K <> N).
          {
          intro; treat_equalities; destruct HR4 as [HRect HC].
          apply degenerated_rect_eq in HRect; treat_equalities; Col.
          }
        apply l6_21 with b c d c; Col.
        - apply (per_not_col _ _ _ Hbc Hcd), (rect_per3 a).
          destruct HR3; apply rect_comm2; assumption.
        - cut (Col c c' b); [Col|apply (cop_per2__col a)].
          + assert (HC1 : Col c d M) by (destruct HR3; ColR).
            apply coplanar_pseudo_trans with a b M; Col; Cop.
            * destruct HR3; cut (Coplanar a b c M); [Cop|].
              apply (col_cop__cop _ _ _ d); Cop.
            * destruct HR4 as [HRect HC].
              apply coplanar_pseudo_trans with b K M; Col; Cop.
              cut (Coplanar b K c' M); [Cop|].
              apply (col_cop__cop _ _ _ N); Col; Cop.
              intro; treat_equalities.
              apply rect_permut, degenerated_rect_eq in HRect.
              treat_equalities; apply HNC3; Col.
          + intro; treat_equalities; apply HNC1; Col.
          + destruct HR3 as [HRect _]; apply rect_per1 in HRect; Perp.
          + destruct HR4 as [HRect _]; apply rect_per1 in HRect.
            apply (per_col _ _ K); Col; Perp.
        - destruct HR3 as [HR3 HC1]; apply Rectangle_Parallelogram in HR3.
          destruct HR4 as [HR4 HC2]; apply Rectangle_Parallelogram in HR4.
          apply plg_par_1 in HR3; [|auto..].
          apply plg_par_1 in HR4; [|auto..].
          destruct (parallel_uniqueness a b c d c' N M); Col; Par.
          cut (Par c' N a b); [Par|].
          apply (par_col2_par _ _ b K); Col; Par.
        }
      assert (HRect : Rectangle K b c N)
        by (apply rect_comm2; destruct HR4; assumption).
      apply (B5_8 A B K M C D c b K N a d); [assumption..| |].
      + assert (ER : EqT M K b K b M) by (apply B6_1; Col).
        destruct ER as [B' [A' [c' [N' [HR5 [HR6 ER1]]]]]].
        assert (A = A' /\ B = B'); [|spliter; treat_equalities; clear HR5].
          {
          apply (Circumscribed_rectangle_unique K M b); [assumption..|].
          apply FCR_ABCDK_BACKD; assumption.
          }
        assert (c = c' /\ N = N'); [|spliter; treat_equalities; clear HR6].
          {
          assert (HbK : K <> b) by (intro; treat_equalities; apply HNC3; Col).
          cut (First_circumscribed_rectangle K b M c N).
          - intro; apply (Circumscribed_rectangle_unique K b M); assumption.
          - split; destruct HR4; Col.
          }
        assert (ER2 : EqR A B K M M K B A).
          {
          destruct (EqR_perm A B K M); [..|spliter; assumption].
          - intro; treat_equalities; destruct HR1 as [HR1 _].
            apply rect_permut, degenerated_rect_eq in HR1.
            treat_equalities; apply HNC2; Col.
          - intro; treat_equalities; destruct HR1 as [HR1 _].
            apply rect_permut, rect_permut, degenerated_rect_eq in HR1.
            treat_equalities; destruct ER1 as [_ [HF _]]; apply HF; auto.
          - destruct ER1 as [_ [_ [HR _]]].
            apply rect_comm2, rect_permut, rect_permut; assumption.
          }
        assert (ER3 : EqR K b c N c b K N).
          {
          destruct (EqR_perm K b c N); [..|assumption|spliter; assumption].
          - intro; treat_equalities; apply HNC3; Col.
          - intro; treat_equalities; apply degenerated_rect_eq in HRect.
            treat_equalities; destruct ER1; spliter; auto.
          }
        apply EqR_trans with M K B A; [assumption|].
        apply EqR_trans with K b c N; assumption.
      + assert (ER : EqT M K a K a M) by (apply B6_1; Col).
        destruct ER as [C' [D' [d' [N' [HR5 [HR6 ER1]]]]]].
        assert (H : Rectangle K a d N); [|clear HRect; rename H into HRect].
          {
          destruct HR3 as [HR3 _]; do 3 apply rect_permut in HR3.
          apply rect_permut, rect_comm2 in HRect.
          apply rect_permut, rect_comm2.
          apply (rect_2_rect c b); [auto|assumption..].
          }
        assert (D = D' /\ C = C'); [|spliter; treat_equalities; clear HR5].
          {
          apply (Circumscribed_rectangle_unique K M a); [assumption..|].
          apply FCR_ABCDK_BACKD; assumption.
          }
        assert (d = d' /\ N = N'); [|spliter; treat_equalities; clear HR4].
          {
          assert (HbK : K <> a) by (intro; treat_equalities; apply HNC2; Col).
          cut (First_circumscribed_rectangle K a M d N).
          - intro; apply (Circumscribed_rectangle_unique K a M); assumption.
          - destruct HR3; destruct HR4; split; Col.
            destruct (eq_dec_points c M); [treat_equalities|ColR].
            cut (Bet c N d); [Col|apply (Bet_Rect2__Bet c b K N a d); Between].
            + do 3 apply rect_permut; assumption.
            + do 2 apply rect_permut; apply (rect_2_rect c b); [auto|..].
              * do 3 apply rect_permut; assumption.
              * do 3 apply rect_permut; assumption.
          }
        assert (ER2 : EqR K a d N N K a d).
          {
          destruct (EqR_perm K a d N); [..|assumption|spliter; assumption].
          - intro; treat_equalities; apply HNC2; Col.
          - intro; treat_equalities; apply degenerated_rect_eq in HRect.
            treat_equalities; destruct ER1; spliter; auto.
          }
        apply EqR_trans with K a d N; assumption.
    }
  intros J K L M A B C D a b c d HNCE1 HNCE2 HR1 HR2 HConvex HJL HKM HR3 HR4.
  assert (HRP : A <> B /\ B <> C /\ Rectangle A B C D /\
                a <> b /\ b <> c /\ Rectangle a b c d).
    {
    assert (H : forall J K L M A B C D,
                  First_circumscribed_rectangle J L K A B ->
                  First_circumscribed_rectangle J L M D C ->
                  Convex J K L M ->
                  ~ Col J L K \/ ~ Col J L M ->
                  A <> B /\ B <> C /\ Rectangle A B C D).
      {
      clear HDQOC J K L M A B C D a b c d
            HNCE1 HNCE2 HR1 HR2 HConvex HJL HKM HR3 HR4.
      intros J K L M A B C D HR1 HR2 HConvex HNCE.
      assert (HRect : Rectangle A B C D).
        {
        apply (circumscribed_rectangle__rectangle J K L M); [assumption|].
        split; [assumption|left; split; assumption].
        }
      split; [|split]; [intro; treat_equalities..|assumption].
      - destruct HR1 as [HR1 _]; apply rect_permut in HR1.
        apply degenerated_rect_eq in HR1; treat_equalities.
        destruct HNCE as [HF|HF]; apply HF; Col.
      - assert (HE : Bet B J B).
          {
          cut (Bet B J B /\ Bet A L D); [intros [HB _]; assumption|].
          apply (circumscribed_rectangle__bet L K J M B A D B).
          - destruct HNCE as [HNC|HNC]; [left|right]; intro; apply HNC; Col.
          - destruct HConvex as [I []]; exists I; split; Between.
          - apply FCR_ABCDK_BACKD; assumption.
          - apply FCR_ABCDK_BACKD; assumption.
          }
        apply degenerated_rect_eq in HRect; treat_equalities.
        destruct HR1 as [HR HC1]; destruct HR2 as [_ HC2].
        assert (HF : OS B L A B).
          {
          apply pars__os3412.
          assert (HPar : Par B L A B).
            {
            apply Rectangle_Parallelogram in HR.
            apply plg_par_1 in HR; [Par|intro; treat_equalities..].
            - destruct HNCE as [HF|HF]; apply HF; Col.
            - apply plg_col_plgf in HR; [|Col].
              destruct HR as [_ [HC3 [_ [HCong HE]]]].
              treat_equalities; destruct HNCE as [HF|HF]; apply HF; Col.
            }
          cut (Par_strict B L A B); [Par|].
          destruct HNCE as [HNC|HNC]; [apply par_not_col_strict with K; Col|].
          apply par_not_col_strict with M; Col.
          }
        apply one_side_not_col124 in HF; apply HF; Col.
      }
    assert (HC: Convex K J M L)
      by (destruct HConvex as [I [HB1 HB2]]; exists I; split; Between).
    destruct (H K J M L A B C D) as [HAB [HBC HRect1]]; [assumption..|].
    destruct (H J K L M a b c d) as [Hab [Hbc HRect2]]; tauto.
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
    assert (HE1 : forall I J K L M a b c d b' Iab,
                    J <> L ->
                    First_circumscribed_rectangle J L K a b ->
                    First_circumscribed_rectangle J L M d c ->
                    a <> b -> b <> c -> Rectangle a b c d ->
                    ~ Col J L K -> ~ Col J L M ->
                    Bet J I L -> Bet K I M -> I <> J ->
                    First_circumscribed_rectangle I J K b' Iab ->
                    b = b').
      {
      clear J K L M A B C D a b c d HR1 HR2 HConvex HJL HKM
            HR3 HR4 HAB HBC HRect1 Hab Hbc HRect2 HNC1 HNC2 HNC3 HNC4.
      intros I J K L M a b c d b' Iab HJL HR3 HR4.
      intros Hab Hbc HRect2 HNC1 HNC2 HB1 HB2 HIJ HR5.
      assert (HCop1 : Coplanar J K L M) by (exists I; right; left; split; Col).
      assert (HCop2 : Coplanar J L b K)
        by (destruct HR3; apply col_cop__cop with a; Col; Cop).
      destruct HR3 as [HR3 HC1]; destruct HR5 as [HR5 HC2].
      apply l6_21 with a b c b; Col.
      - apply per_not_col; [auto..|apply (rect_per2 _ _ _ d); assumption].
      - destruct (parallel_uniqueness J L a b Iab b' K); Col.
        + cut (a <> L).
          * intro; apply Rectangle_Parallelogram, plg_par_1 in HR3; Par.
          * intro; treat_equalities; apply degenerated_rect_eq in HR3.
            treat_equalities; apply HNC1; Col.
        + cut (b' <> J).
          * intro; apply Rectangle_Parallelogram, plg_par_1 in HR5; Par.
            cut (Par b' Iab J L); [Par|].
            apply (par_col2_par _ _ I J); Col; Par.
          * intro; treat_equalities; apply degenerated_rect_eq in HR5.
            treat_equalities; apply HNC1; ColR.
      - assert (HaJ : b <> J).
          {
          intro; treat_equalities; do 2 apply rect_permut in HR3.
          apply degenerated_rect_eq in HR3; treat_equalities; Col.
          }
        assert (HPer1 : Per b J L) by (apply rect_per1 in HR3; Perp).
        assert (HPer2 : Per c J L)
          by (destruct HR4 as [HR4 _]; apply rect_per1 in HR4; Perp).
        assert (Hcd : c <> d).
          {
          intro; treat_equalities; apply rect_permut in HRect2.
          apply degenerated_rect_eq in HRect2; auto.
          }
        cut (Col c b J /\ Col b b' J); [intros []; ColR|split].
        + apply (cop_per2__col L); Perp.
          apply coplanar_pseudo_trans with J L K; Cop.
          apply coplanar_pseudo_trans with J L M; Cop.
          cut (Coplanar J L c M); [Cop|].
          destruct HR4 as [HR4 HC].
          apply col_cop__cop with d; Col; Cop.
        + apply (cop_per2__col L); Perp.
          * apply coplanar_pseudo_trans with J L K; Cop.
            cut (Coplanar b' K J L); [Cop|].
            apply col_cop__cop with I; Col.
            cut (Coplanar J I b' K); [Cop|].
            apply col_cop__cop with Iab; Col; Cop.
            intro; treat_equalities; apply rect_permut in HR5.
            apply degenerated_rect_eq in HR5; auto.
          * cut (Per L J b'); [Perp|apply (l8_3 I); Col].
            apply rect_per2 in HR5; Perp.
      }
    assert (HE2 : forall I J K L a b M N,
                    First_circumscribed_rectangle I J K b M ->
                    First_circumscribed_rectangle I L K a N ->
                    Bet J I L -> I <> J -> I <> L ->
                    M = N).
      {
      clear J K L M A B C D a b c d HR1 HR2 HConvex HJL HKM
            HR3 HR4 HAB HBC HRect1 Hab Hbc HRect2 HNC1 HNC2 HNC3 HNC4 HE1.
      intros I J K L a b M N HR1 HR2 HB HIJ HIL.
      assert (HaN : a <> N).
        {
        intro; treat_equalities; destruct HR2 as [HR2 _].
        apply rect_permut, degenerated_rect_eq in HR2; treat_equalities; auto.
        }
      assert (HbM : b <> M).
        {
        intro; treat_equalities; destruct HR1 as [HR1 _].
        apply rect_permut, degenerated_rect_eq in HR1; treat_equalities; auto.
        }
      destruct (col_dec J L K) as [HC|HNC1].
      - apply FCR_Col__eq in HR1; [|ColR|auto].
        apply FCR_Col__eq in HR2; [|ColR|auto].
        spliter; treat_equalities; auto.
      - destruct HR1 as [HR1 HC1]; destruct HR2 as [HR2 HC2].
        assert (HIM : I <> M).
          {
          intro; treat_equalities; do 2 apply rect_permut in HR1.
          apply degenerated_rect_eq in HR1; treat_equalities; apply HNC1; ColR.
          }
        assert (HIN : I <> N).
          {
          intro; treat_equalities; do 2 apply rect_permut in HR2.
          apply degenerated_rect_eq in HR2; treat_equalities; apply HNC1; ColR.
          }
        assert (HCs : Col a b M /\ Col a b N).
          {
          destruct (parallel_uniqueness J L a N b M K); Col; [..|split; ColR].
          - cut (Par a N J L); [Par|].
            apply (par_col2_par _ _ I L); [intro; treat_equalities|..]; Col.
            apply plg_par_1; auto; apply Rectangle_Parallelogram.
            do 2 apply rect_permut; assumption.
          - cut (Par b M J L); [Par|].
            apply (par_col2_par _ _ I J); [intro; treat_equalities|..]; Col.
            apply plg_par_1; auto; apply Rectangle_Parallelogram.
            do 2 apply rect_permut; assumption.
          }
        destruct HCs as [HC3 HC4].
        assert (HNC2 : ~ Col a b I).
          {
          assert (HPer1 : Per L J b).
            {
            cut (Per b J L); [Perp|apply per_col with I; Col].
            apply rect_per2 in HR1; Perp.
            }
          assert (HPer2 : Per J L a).
            {
            cut (Per a L J); [Perp|apply per_col with I; Col].
            apply rect_per2 in HR2; Perp.
            }
          assert (Hab : a <> b).
            {
            assert (HF : J <> L) by (intro; treat_equalities; auto).
            intro; treat_equalities; apply HF, (l8_7 a); Perp.
            }
          cut (Par_strict I J b M);
          [intros [_ HF] HC5; apply HF; exists I; split; [Col|ColR]|].
          apply par_not_col_strict with K; [|Col|intro HF; apply HNC1; ColR].
          apply plg_par_1; [auto| |apply Rectangle_Parallelogram; assumption].
          intro; treat_equalities; apply degenerated_rect_eq in HR1; auto.
          }
        apply (l6_21 a b I M); Col.
        cut (Col M N I); [Col|apply (cop_per2__col J); [|auto|..]].
        + apply coplanar_pseudo_trans with J K L; Col; Cop.
          * cut (Coplanar K M J L); [Cop|apply col_cop__cop with I; Col].
            cut (Coplanar J I M K); [Cop|].
            apply col_cop__cop with b; Col; Cop.
          * cut (Coplanar K N L J); [Cop|apply col_cop__cop with I; Col].
            cut (Coplanar L I N K); [Cop|].
            apply col_cop__cop with a; Col; Cop.
        + apply rect_per1 in HR1; Perp.
        + apply per_col with L; Col.
          apply rect_per1 in HR2; Perp.
      }
    inversion HConvex as [I [HB1 HB2]].
    assert (HIJ : I <> J) by (intro; treat_equalities; apply HNC3; Col).
    assert (HIK : I <> K) by (intro; treat_equalities; apply HNC1; Col).
    assert (HIL : I <> L) by (intro; treat_equalities; apply HNC4; Col).
    assert (HIM : I <> M) by (intro; treat_equalities; apply HNC2; Col).
    destruct (Circumscribed_rectangle_exists I J K) as [b' HR5]; [tauto|].
    destruct HR5 as [Iab HR5].
    assert (b = b') by (apply (HE1 I J K L M a b c d b' Iab); auto).
    destruct (Circumscribed_rectangle_exists I J M) as [c' HR6]; [tauto|].
    destruct HR6 as [Icd HR6].
    assert (c = c'); [|treat_equalities].
      {
      apply (HE1 I J M L K d c b a c' Icd); Between; Col.
      - intro; treat_equalities; apply rect_permut in HRect2.
        apply degenerated_rect_eq in HRect2; auto.
      - apply rect_comm2, rect_permut, rect_permut; assumption.
      }
    destruct (Circumscribed_rectangle_exists I L K) as [a' HR7]; [tauto|].
    destruct HR7 as [Iab' HR7].
    assert (a = a'); [|treat_equalities].
      {
      apply (HE1 I L K J M b a d c a' Iab'); Between; Col.
      - apply FCR_ABCDK_BACKD; assumption.
      - apply FCR_ABCDK_BACKD; assumption.
      - intro; treat_equalities; do 2 apply rect_permut in HRect2.
        apply degenerated_rect_eq in HRect2; auto.
      - apply rect_comm2; assumption.
      }
    assert (HE : Iab = Iab') by (apply (HE2 I J K L a b); assumption).
    destruct (Circumscribed_rectangle_exists I L M) as [d' HR8]; [tauto|].
    destruct HR8 as [Icd' HR8].
    assert (d = d'); [|treat_equalities].
      {
      apply (HE1 I L M J K c d a b d' Icd'); Between; Col.
      - apply FCR_ABCDK_BACKD; assumption.
      - apply FCR_ABCDK_BACKD; assumption.
      - intro; treat_equalities; apply rect_permut in HRect2.
        apply degenerated_rect_eq in HRect2; auto.
      - intro; treat_equalities; do 2 apply rect_permut in HRect2.
        apply degenerated_rect_eq in HRect2; auto.
      - apply rect_permut, rect_permut; assumption.
      }
    assert (HE : Icd = Icd') by (apply (HE2 I J M L d c); assumption).
    destruct (Circumscribed_rectangle_exists I K J) as [B' HR9]; [tauto|].
    destruct HR9 as [IAB HR9].
    assert (B = B') by (apply (HE1 I K J M L A B C D B' IAB); Col).
    destruct (Circumscribed_rectangle_exists I M J) as [A' HR10]; [tauto|].
    destruct HR10 as [IAB' HR10].
    assert (A = A'); [|treat_equalities].
      {
      apply (HE1 I M J K L B A D C A' IAB'); Between; Col.
      - apply FCR_ABCDK_BACKD; assumption.
      - apply FCR_ABCDK_BACKD; assumption.
      - intro; treat_equalities; do 2 apply rect_permut in HRect1.
        apply degenerated_rect_eq in HRect1; auto.
      - apply rect_comm2; assumption.
      }
    assert (HE : IAB = IAB') by (apply (HE2 I K J M A B); assumption).
    destruct (Circumscribed_rectangle_exists I K L) as [C' HR11]; [tauto|].
    destruct HR11 as [ICD HR11].
    assert (C = C'); [|treat_equalities].
      {
      apply (HE1 I K L M J D C B A C' ICD); Between; Col.
      - intro; treat_equalities; apply rect_permut in HRect1.
        apply degenerated_rect_eq in HRect1; auto.
      - apply rect_comm2, rect_permut, rect_permut; assumption.
      }
    destruct (Circumscribed_rectangle_exists I M L) as [D' HR12]; [tauto|].
    destruct HR12 as [ICD' HR12].
    assert (D = D'); [|treat_equalities].
      {
      apply (HE1 I M L K J C D A B D' ICD'); Between; Col.
      - apply FCR_ABCDK_BACKD; assumption.
      - apply FCR_ABCDK_BACKD; assumption.
      - intro; treat_equalities; apply rect_permut in HRect1.
        apply degenerated_rect_eq in HRect1; auto.
      - intro; treat_equalities; do 2 apply rect_permut in HRect1.
        apply degenerated_rect_eq in HRect1; auto.
      - do 2 apply rect_permut; assumption.
      }
    assert (HE : ICD = ICD') by (apply (HE2 I K L M D C); assumption).
    treat_equalities; clear HE1 HE2.
    assert (HNC5 : ~ Col I J K).
      {
      intro HC; cut (I <> J); [intro; apply HNC1; ColR|].
      intro; treat_equalities; apply HNC3; Col.
      }
    assert (ER1 : EqT K I J I J K) by (apply B6_1; Col).
    destruct ER1 as [IAB' [B' [b' [Iab' [HR13 [HR14 ER1]]]]]].
    apply FCR_ABCDK_BACKD in HR13.
    assert (B = B' /\ IAB = IAB'); [|spliter; treat_equalities].
      {
      eapply Circumscribed_rectangle_unique in HR13; eauto.
      }
    assert (b = b' /\ Iab = Iab'); [|spliter; treat_equalities].
      {
      eapply Circumscribed_rectangle_unique in HR14; eauto.
      }
    assert (HNC6 : ~ Col I J M).
      {
      intro HC; cut (I <> J); [intro; apply HNC2; ColR|].
      intro; treat_equalities; apply HNC3; Col.
      }
    assert (ER2 : EqT M I J I J M) by (apply B6_1; Col).
    destruct ER2 as [IAB' [A' [c' [Icd' [HR13 [HR14 ER2]]]]]].
    apply FCR_ABCDK_BACKD in HR13.
    assert (A = A' /\ IAB = IAB'); [|spliter; treat_equalities].
      {
      eapply Circumscribed_rectangle_unique in HR13; eauto.
      }
    assert (c = c' /\ Icd = Icd'); [|spliter; treat_equalities].
      {
      eapply Circumscribed_rectangle_unique in HR14; eauto.
      }
    assert (HNC7 : ~ Col I L M).
      {
      intro HC; cut (I <> L); [intro; apply HNC4; ColR|].
      intro; treat_equalities; apply HNC4; Col.
      }
    assert (ER3 : EqT M I L I L M) by (apply B6_1; Col).
    destruct ER3 as [ICD' [D' [d' [Icd' [HR13 [HR14 ER3]]]]]].
    apply FCR_ABCDK_BACKD in HR13.
    assert (D = D' /\ ICD = ICD'); [|spliter; treat_equalities].
      {
      eapply Circumscribed_rectangle_unique in HR13; eauto.
      }
    assert (d = d' /\ Icd = Icd'); [|spliter; treat_equalities].
      {
      eapply Circumscribed_rectangle_unique in HR14; eauto.
      }
    assert (HNC8 : ~ Col K I L).
      {
      intro HC; cut (I <> L); [intro; apply HNC4; ColR|].
      intro; treat_equalities; apply HNC4; Col.
      }
    assert (ER4 : EqT K I L I L K) by (apply B6_1; Col).
    destruct ER4 as [ICD' [C' [a' [Iab' [HR13 [HR14 ER4]]]]]].
    apply FCR_ABCDK_BACKD in HR13.
    assert (C = C' /\ ICD = ICD'); [|spliter; treat_equalities].
      {
      eapply Circumscribed_rectangle_unique in HR13; eauto.
      }
    assert (a = a' /\ Iab = Iab'); [|spliter; treat_equalities].
      {
      eapply Circumscribed_rectangle_unique in HR14; eauto.
      }
    assert (ER5 : EqR c b a d a b c d)
      by (apply EqR_sym; destruct (EqR_perm a b c d); [..|spliter]; auto).
    apply EqR_trans with c b a d; [clear ER5|assumption].
    assert (HB3 : Bet B K C).
      {
      assert (HE : ~ Col K M J \/ ~ Col K M L) by tauto.
      clear HConvex; assert (H : Convex K J M L) by (exists I; split; Between).
      destruct (circumscribed_rectangle__bet K J M L A B C D); assumption.
      }
    assert (HB4 : Bet a Iab b).
      {
      apply (Bet_Rect2__Bet a L I Iab J b); Between.
      - destruct HR7 as [HR7 _].
        do 3 apply rect_permut; apply rect_comm2; assumption.
      - destruct HR5 as [HR5 _]; do 3 apply rect_permut; assumption.
      }
    assert (HB5 : Bet Iab I Icd).
      {
      assert (HE : ~ Col I J K \/ ~ Col I J M) by tauto.
      assert (H : Convex I K J M) by (exists I; split; Between).
      destruct (circumscribed_rectangle__bet I K J M b Iab Icd c); assumption.
      }
    apply (B5_8 A B K M C D c b Iab Icd a d); Between.
    + assert (ER5 : EqR A B K M A M K B).
        {
        assert (HR : Rectangle A B K M)
          by (destruct HR1; do 2 apply rect_permut; assumption).
        destruct (EqR_perm A B K M); [..|spliter]; auto.
        intro; treat_equalities; apply degenerated_rect_eq in HR.
        treat_equalities; apply HNC3; destruct HR1; Col.
        }
      apply EqR_trans with A M K B; [assumption|clear ER5].
      assert (ER5 : EqR c Icd Iab b c b Iab Icd).
        {
        assert (HR : Rectangle c Icd Iab b).
          {
          apply extent_rect with I J; Between.
          - destruct HR6 as [HR6 _]; do 2 apply rect_permut; assumption.
          - destruct HR5 as [HR5 _]; apply rect_comm2; assumption.
          }
        destruct (EqR_perm c Icd Iab b); [..|assumption|spliter; assumption].
        - intro; treat_equalities; do 3 apply rect_permut in HR.
          apply degenerated_rect_eq in HR; treat_equalities.
          destruct HR5 as [HR5 _]; apply rect_permut in HR5.
          apply degenerated_rect_eq in HR5; treat_equalities; auto.
        - intro; treat_equalities; apply degenerated_rect_eq in HR; auto.
        }
      apply EqR_trans with c Icd Iab b; [clear ER5|assumption].
      apply (B5_8 A M I IAB K B c Icd I J Iab b); Between.
      * assert (ER5 : EqR A M I IAB M I IAB A).
          {
          assert (HR : Rectangle A M I IAB).
            {
            destruct HR10 as [HR10 _].
            do 3 apply rect_permut; apply rect_comm2; assumption.
            }
          destruct (EqR_perm A M I IAB); [|auto..|spliter; assumption].
          intro; treat_equalities; do 3 apply rect_permut in HR.
          apply degenerated_rect_eq in HR; treat_equalities.
          apply HNC6; destruct HR10; Col.
          }
        apply EqR_trans with M I IAB A; [assumption|clear ER5].
        apply EqR_trans with I J c Icd; [assumption|].
        assert (HR : Rectangle I J c Icd) by (destruct HR6; assumption).
        destruct (EqR_perm I J c Icd); [..|spliter; assumption]; auto.
        intro; treat_equalities; apply degenerated_rect_eq in HR.
        treat_equalities; apply HNC6; destruct HR6; Col.
      * assert (ER5 : EqR IAB I K B K I IAB B).
          {
          assert (HR : Rectangle IAB I K B)
            by (destruct HR9 as [HR9 _]; do 3 apply rect_permut; assumption).
          destruct (EqR_perm IAB I K B); [..|spliter; assumption]; auto.
          intro; treat_equalities; do 3 apply rect_permut in HR.
          apply degenerated_rect_eq in HR; treat_equalities.
          apply HNC5; destruct HR9; Col.
          }
        apply EqR_trans with K I IAB B; [assumption|clear ER5].
        apply EqR_trans with I J b Iab; [assumption|].
        assert (HR : Rectangle I J b Iab) by (destruct HR5; assumption).
        destruct (EqR_perm I J b Iab); [..|spliter; assumption]; auto.
        intro; treat_equalities; apply degenerated_rect_eq in HR.
        treat_equalities; apply HNC5; destruct HR5; Col.
    + assert (ER5 : EqR M K C D D M K C).
        {
        assert (HR : Rectangle M K C D).
          {
          apply rect_permut, extent_rect with I ICD; Between.
          - destruct HR12 as [HR12 _]; do 3 apply rect_permut.
            apply rect_comm2; assumption.
          - destruct HR11 as [HR11 _]; do 3 apply rect_permut; assumption.
          }
        destruct (EqR_perm M K C D); [..|spliter; assumption]; auto.
        intro; treat_equalities; apply degenerated_rect_eq in HR.
        treat_equalities; destruct HR12 as [HR12 _].
        apply degenerated_rect_eq in HR12; treat_equalities.
        apply HNC8; destruct HR11; Col.
        }
      apply EqR_trans with D M K C; [assumption|clear ER5].
      assert (ER5 : EqR d Icd Iab a Icd Iab a d).
        {
        assert (HR : Rectangle d Icd Iab a).
          {
          apply extent_rect with I L; Between.
          - destruct HR8 as [HR8 _]; do 2 apply rect_permut; assumption.
          - destruct HR7 as [HR7 _]; apply rect_comm2; assumption.
          }
        destruct (EqR_perm d Icd Iab a); [..|spliter; assumption]; auto.
        - intro; treat_equalities; destruct HR8 as [HR8 _].
          apply rect_permut, degenerated_rect_eq in HR8; auto.
        - intro; treat_equalities; apply degenerated_rect_eq in HR.
          treat_equalities; do 2 apply rect_permut in HRect2.
          apply degenerated_rect_eq in HRect2; auto.
        }
      apply EqR_trans with d Icd Iab a; [clear ER5|assumption].
      apply (B5_8 D M I ICD K C d Icd I L Iab a); Between.
      * assert (ER5 : EqR D M I ICD M I ICD D).
          {
          assert (HR : Rectangle D M I ICD).
            {
            destruct HR12 as [HR12 _].
            do 3 apply rect_permut; apply rect_comm2; assumption.
            }
          destruct (EqR_perm D M I ICD); [..|spliter; assumption]; auto.
          intro; treat_equalities; do 3 apply rect_permut in HR.
          apply degenerated_rect_eq in HR; treat_equalities.
          apply HNC7; destruct HR12; Col.
          }
        apply EqR_trans with M I ICD D; [assumption|clear ER5].
        apply EqR_trans with I L d Icd; [assumption|].
        assert (HR : Rectangle I L d Icd) by (destruct HR8; assumption).
        destruct (EqR_perm I L d Icd); [..|spliter; assumption]; auto.
        intro; treat_equalities; apply degenerated_rect_eq in HR.
        treat_equalities; apply HNC7; destruct HR8; Col.
      * assert (ER5 : EqR ICD I K C K I ICD C).
          {
          assert (HR : Rectangle ICD I K C)
            by (destruct HR11; do 3 apply rect_permut; assumption).
          destruct (EqR_perm ICD I K C); [..|spliter; assumption]; auto.
          intro; treat_equalities; do 3 apply rect_permut in HR.
          apply degenerated_rect_eq in HR; treat_equalities.
          apply HNC8; destruct HR11; Col.
          }
        apply EqR_trans with K I ICD C; [assumption|clear ER5].
        apply EqR_trans with I L a Iab; [assumption|].
        assert (HR : Rectangle I L a Iab) by (destruct HR7; assumption).
        destruct (EqR_perm I L a Iab); [..|spliter; assumption]; auto.
        intro; treat_equalities; apply degenerated_rect_eq in HR.
        treat_equalities; apply HNC8; destruct HR7; Col.
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

Lemma EqQ_abcd_bcda_not_col A B C D :
  Convex A B C D -> ~ Col A B C -> ~ Col A C D -> EqQ A B C D B C D A.
Proof.
intros HC HNC1 HNC2.
destruct HC as [E [HB1 HB2]].
assert (HCV : Convex A B C D) by (exists E; auto).
assert (HCV2 : Convex B C D A) by (exists E; Between).
apply not_col_distincts in HNC1; apply not_col_distincts in HNC2.
destruct HNC1 as [HNC1 [HNAC [HNBC HNAB]]]; destruct HNC2 as [HNC2 [_ [HNCD HNAD]]].
assert (H1 : exists F G : Tpoint, First_circumscribed_rectangle A C D F G)
  by (apply Circumscribed_rectangle_exists; Col).
assert (H2 : exists I H : Tpoint, First_circumscribed_rectangle A C B I H)
  by (apply Circumscribed_rectangle_exists; Col).
destruct H1 as [F [G H1]]; destruct H2 as [I [H H2]].
assert (HR1 : Rectangle A C F G) by (destruct H1; auto).
assert (HR2 : Rectangle A C I H) by (destruct H2; auto).
assert (HC1 : Col D F G) by (destruct H1; auto).
assert (HC2 : Col B I H) by (destruct H2; auto).
assert (HF1 : First_circumscribed_rectangle C A B H I)
  by (split; Col; apply rect_comm2 in HR2; auto).
assert (HF2 : First_circumscribed_rectangle C A D G F)
  by (split; Col; apply rect_comm2 in HR1; auto).
exists I, H, G, F, H, I, F, G.
split; unfold circumscribed_rectangle; auto.
split.
split; unfold circumscribed_rectangle; auto.
assert (HNIH :  I <> H)
  by (intro; treat_equalities; apply rect_permut in HR2; apply degenerated_rect_eq in HR2; auto).
assert (HNCF : C <> F).
  {
  intro; treat_equalities.
  assert (HAG : A = G) by (apply degenerated_rect_eq with C; auto).
  treat_equalities; Col.
  }
assert (HNCI :  C <> I).
  {
  intro; treat_equalities.
  assert (HAG : A = H) by (apply degenerated_rect_eq with C; auto).
  treat_equalities; Col.
  }
assert (HNCol : ~ Col G A C).
  {
  elim (eq_dec_points G D).
  - intros HGD HNC; treat_equalities; Col.
  - intros HNGD HNC.
    assert (HP : Par A C G D).
    apply Rectangle_Parallelogram in HR1; apply plg_par_1 in HR1; auto.
    apply par_col_par with F; Par; Col.
    assert (HC : Col A C D) by (apply not_strict_par2 with G G; Col).
    Col.
  }
assert (HNCol2 :  ~ Col A C I).
  {
  elim (eq_dec_points I B).
  - intros HIB HC; treat_equalities; Col.
  - intros HNIB HC.
    assert (HP : Par A C I B).
    apply Rectangle_Parallelogram in HR2; apply plg_par_1 in HR2; auto.
    apply par_col_par with H; Par; Col.
    assert (HCol : Col A C B).
    apply not_strict_par2 with I I; Col.
    Col.
  }
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
  - apply coplanar_pseudo_trans with A C B; Col; Cop.
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
apply EqR_perm; auto.
Qed.

Lemma EqQ_abcd_bcda A B C D :
  Convex A B C D -> ~ Col A B C \/ ~ Col A C D -> EqQ A B C D B C D A.
Proof.
intros HC HNC; destruct HC as [E [HB1 HB2]].
assert (HCV : Convex A B C D) by (exists E; auto).
assert (HCV2 : Convex B C D A) by (exists E; Between).
destruct HNC as [HNC1 | HNC2].
-elim (col_dec A D C).
+intro.
 apply not_col_distincts in HNC1.
 destruct HNC1 as [HNC1 [HNAC [HNBC HNAB]]].
 assert (H1 : exists F G : Tpoint, First_circumscribed_rectangle A C B F G)
   by (apply Circumscribed_rectangle_exists; Col).
 destruct H1 as [F [G H1]].
 assert (HR1 : Rectangle A C F G) by (destruct H1; auto).
 assert (HR2 : Rectangle A C C A) by (apply rect_permut; apply Rectangle_triv; auto).
 assert (HR3 : Rectangle C A G F) by (apply rect_comm2; auto).
 assert (HR4 : Rectangle C A A C) by (apply rect_comm2; auto).
 assert (HR5 : Rectangle F G A C) by (do 2 (apply rect_permut); auto).
 assert (HC1 : Col B F G) by (destruct H1; auto).
 exists F, G, A, C, G, F, C, A.
 split.
 split; auto.
 left; split; auto; do 2 (split; Col).
 split.
 split; auto.
 right; split; auto; split; Col.
 assert (HNFG : F <> G)
   by (intro; treat_equalities; apply rect_permut in HR1; apply degenerated_rect_eq in HR1; auto).
 assert (HNCF : C <> F).
 {
   intro; treat_equalities.
   assert (HAG : A = G) by (apply degenerated_rect_eq with C; auto).
   treat_equalities; Col.
 }
 assert (HNGA : G <> A) by (intro; treat_equalities; apply degenerated_rect_eq in HR5; auto).
 apply EqR_perm; auto.

+intro HNC2; apply EqQ_abcd_bcda_not_col; Col.

-elim (col_dec A C B).
+intro HC.
apply not_col_distincts in HNC2.
destruct HNC2 as [HNC2 [HNAC [HNBC HNAB]]].
assert (H1 : exists F G : Tpoint, First_circumscribed_rectangle A C D F G)
  by (apply Circumscribed_rectangle_exists; Col).
destruct H1 as [F [G H1]].
assert (HR1 : Rectangle A C F G) by (destruct H1; auto).
assert (HR2 : Rectangle A C C A) by (apply rect_permut; apply Rectangle_triv; auto).
assert (HR3 : Rectangle C A G F) by (apply rect_comm2; auto).
assert (HR4 : Rectangle C A A C) by (apply rect_comm2; auto).
assert (HR5 : Rectangle F G A C) by (do 2 (apply rect_permut); auto).
assert (HC1 : Col D F G) by (destruct H1; auto).
exists C, A, G, F, A, C, F, G.
split.
split; auto.
left; split; auto; do 2 (split; Col).
split.
split; auto.
right; split; auto; split; Col.
assert (HNCF : C <> F).
  {
  intro; treat_equalities.
  assert (HAG : A = G) by (apply degenerated_rect_eq with C; auto).
  treat_equalities; Col.
  }
assert (HNAG : A <> G) by (intro; treat_equalities; apply degenerated_rect_eq in HR3; auto).
apply EqR_perm; auto.

+intro HNC1; apply EqQ_abcd_bcda_not_col; Col.
Qed.

Lemma EqQ_abcd_adcb_not_col A B C D :
  Convex A B C D -> ~ Col A B C -> ~ Col A C D -> EqQ A B C D A D C B.
Proof.
intros HC HNC1 HNC2; destruct HC as [E [HB1 HB2]].
assert (HCV : Convex A B C D) by (exists E; auto).
assert (HCV2 : Convex A D C B) by (exists E; Between).
apply not_col_distincts in HNC1; apply not_col_distincts in HNC2.
destruct HNC1 as [HNC1 [HNAC [HNBC HNAB]]]; destruct HNC2 as [HNC2 [_ [HNCD HNAD]]].
assert (H1 : exists F G : Tpoint, First_circumscribed_rectangle A C D F G)
  by (apply Circumscribed_rectangle_exists; Col).
assert (H2 : exists I H : Tpoint, First_circumscribed_rectangle A C B I H)
  by (apply Circumscribed_rectangle_exists; Col).
destruct H1 as [F [G H1]]; destruct H2 as [I [H H2]].
assert (HR1 : Rectangle A C F G) by (destruct H1; auto).
assert (HR2 : Rectangle A C I H) by (destruct H2; auto).
assert (HC1 : Col D F G) by (destruct H1; auto).
assert (HC2 : Col B I H) by (destruct H2; auto).
assert (HF1 : First_circumscribed_rectangle C A B H I)
  by (split; Col; apply rect_comm2 in HR2; auto).
assert (HF2 : First_circumscribed_rectangle C A D G F)
  by (split; Col; apply rect_comm2 in HR1; auto).
exists I, H, G, F, F, G, H, I.
split.
split; auto.
unfold circumscribed_rectangle; auto.
split.
split; auto.
assert (HNIH :  I <> H)
  by (intro; treat_equalities; apply rect_permut in HR2; apply degenerated_rect_eq in HR2; auto).
assert (HNCF : C <> F).
  {
  intro; treat_equalities.
  assert (HAG : A = G) by (apply degenerated_rect_eq with C; auto).
  treat_equalities; Col.
  }
assert (HNCI :  C <> I).
  {
  intro; treat_equalities.
  assert (HAG : A = H) by (apply degenerated_rect_eq with C; auto).
  treat_equalities; Col.
  }
assert (HNCol : ~ Col G A C).
  {
  elim (eq_dec_points G D).
  - intros HGD HNC; treat_equalities; Col.
  - intros HNGD HNC.
    assert (HP : Par A C G D).
    apply Rectangle_Parallelogram in HR1; apply plg_par_1 in HR1; auto.
    apply par_col_par with F; Par; Col.
    assert (HC : Col A C D) by (apply not_strict_par2 with G G; Col).
    Col.
  }
assert (HNCol2 :  ~ Col A C I).
  {
  elim (eq_dec_points I B).
  - intros HIB HC; treat_equalities; Col.
  - intros HNIB HC.
    assert (HP : Par A C I B).
    apply Rectangle_Parallelogram in HR2; apply plg_par_1 in HR2; auto.
    apply par_col_par with H; Par; Col.
    assert (HCol : Col A C B).
    apply not_strict_par2 with I I; Col.
    Col.
  }
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
  - apply coplanar_pseudo_trans with A C B; Col; Cop.
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
apply EqR_perm; auto.
Qed.

Lemma EqQ_abcd_adcb A B C D :
  Convex A B C D -> ~ Col A B C \/ ~ Col A C D -> EqQ A B C D A D C B.
Proof.
intros HC HNC; destruct HC as [E [HB1 HB2]].
assert (HCV : Convex A B C D) by (exists E; auto).
assert (HCV2 : Convex A D C B) by (exists E; Between).
destruct HNC as [HNC1 | HNC2].
-elim (col_dec A D C).
 +intro.
  apply not_col_distincts in HNC1.
  destruct HNC1 as [HNC1 [HNAC [HNBC HNAB]]].
  assert (H1 : exists F G : Tpoint, First_circumscribed_rectangle A C B F G)
    by (apply Circumscribed_rectangle_exists; Col).
  destruct H1 as [F [G H1]].
  assert (HR1 : Rectangle A C F G) by (destruct H1; auto).
  assert (HR2 : Rectangle A C C A) by (apply rect_permut; apply Rectangle_triv; auto).
  assert (HR3 : Rectangle C A G F) by (apply rect_comm2; auto).
  assert (HR4 : Rectangle C A A C) by (apply rect_comm2; auto).
  assert (HR5 : Rectangle F G A C) by (do 2 (apply rect_permut); auto).
  assert (HC1 : Col B F G) by (destruct H1; auto).
  exists F, G, A, C, C, A, G, F.
  split.
  split; auto.
  left; split; auto; do 2 (split; Col).
  split.
  split; auto.
  left; split; auto; split; Col.
  assert (HNFG : F <> G)
    by (intro; treat_equalities; apply rect_permut in HR1; apply degenerated_rect_eq in HR1; auto).
  assert (HNCF : C <> F).
  {
    intro; treat_equalities.
    assert (HAG : A = G) by (apply degenerated_rect_eq with C; auto).
    treat_equalities; Col.
  }
  assert (HNGA : G <> A) by (intro; treat_equalities; apply degenerated_rect_eq in HR5; auto).
  apply EqR_perm; auto.
 +intro HNC2; apply EqQ_abcd_adcb_not_col; Col.

- elim (col_dec A C B).
 +intro HC.
  apply not_col_distincts in HNC2.
  destruct HNC2 as [HNC2 [HNAC [HNBC HNAB]]].
  assert (H1 : exists F G : Tpoint, First_circumscribed_rectangle A C D F G)
    by (apply Circumscribed_rectangle_exists; Col).
  destruct H1 as [F [G H1]].
  assert (HR1 : Rectangle A C F G) by (destruct H1; auto).
  assert (HR2 : Rectangle A C C A) by (apply rect_permut; apply Rectangle_triv; auto).
  assert (HR3 : Rectangle C A G F) by (apply rect_comm2; auto).
  assert (HR4 : Rectangle C A A C) by (apply rect_comm2; auto).
  assert (HR5 : Rectangle F G A C) by (do 2 (apply rect_permut); auto).
  assert (HC1 : Col D F G) by (destruct H1; auto).
  exists C, A, G, F, F, G, A, C.
  split.
  split; auto.
  left; split; auto; do 2 (split; Col).
  split.
  split; auto.
  left; split; auto; split; Col.
  assert (HNCF : C <> F).
  {
    intro; treat_equalities.
    assert (HAG : A = G) by (apply degenerated_rect_eq with C; auto).
    treat_equalities; Col.
  }
  assert (HNAG : A <> G) by (intro; treat_equalities; apply degenerated_rect_eq in HR3; auto).
  apply EqR_perm; auto.
 +intro; apply EqQ_abcd_adcb_not_col; Col.
Qed.

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
- destruct HR2 as [HConvex [[HR2 HR5]|[HR2 HR5]]].
  + assert (E = f /\ G = e); [|spliter; treat_equalities].
      {
      apply (FCR_Col__eq E G F e f); Col.
      intro; treat_equalities; destruct HR2 as [HR2 _].
      do 3 apply rect_permut in HR2; apply degenerated_rect_eq in HR2.
      treat_equalities; destruct ER1; spliter; auto.
      }
    assert (E = g /\ G = h); [|spliter; treat_equalities].
      {
      apply (FCR_Col__eq E G H h g); Col.
      intro; treat_equalities; destruct HR5 as [HR5 _].
      do 3 apply rect_permut in HR5; apply degenerated_rect_eq in HR5.
      treat_equalities; destruct ER1; spliter; auto.
      }
    destruct ER1; spliter; exfalso; auto.
  + assert (HC3 : Col E F H).
      {
      destruct (eq_dec_points E G) as [|]; [treat_equalities|ColR].
      destruct HConvex as [M []]; treat_equalities; Col.
      }
   assert (F = f /\ H = e); [|spliter; treat_equalities].
      {
      apply (FCR_Col__eq F H E e f); Col.
      intro; treat_equalities; destruct HR2 as [HR2 _].
      do 3 apply rect_permut in HR2; apply degenerated_rect_eq in HR2.
      treat_equalities; destruct ER1; spliter; auto.
      }
    assert (HC4 : Col F G H).
      {
      destruct (eq_dec_points E G) as [|]; [treat_equalities|ColR].
      destruct HConvex as [M []]; treat_equalities; Col.
      }
    assert (F = g /\ H = h); [|spliter; treat_equalities].
      {
      apply (FCR_Col__eq F H G h g); Col.
      intro; treat_equalities; destruct HR5 as [HR5 _].
      do 3 apply rect_permut in HR5; apply degenerated_rect_eq in HR5.
      treat_equalities; destruct ER1; spliter; auto.
      }
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
Lemma rectangle_cut_in_halves A B C D P Q a b c d p q:
  Midpoint q b c -> Midpoint Q C D ->
  EqR A B C D a b c d ->
  EqR P Q C B a b q p.
Proof.
intros HM1 HM2 HEQR.
destruct HEQR as [HNAB [HNBC [HR1 [HNab [HNbc [HR2 H]]]]]].
destruct H as [E [F [G [H [I [J [K [L [M H1]]]]]]]]]; spliter.
destruct (midpoint_existence H I) as [P2 HM5].
destruct (midpoint_existence G F) as [Q2 HM6].
destruct (midpoint_existence F M) as [p2 HM7].
destruct (midpoint_existence E L) as [q2 HM8].
Admitted.

Lemma EqT_not_col A B C a b c : EqT A B C a b c -> ~ Col A B C /\ ~ Col a b c.
Proof.
intro HEQT.
destruct HEQT as [D [K [d [k [HF1 [HF2 HEQR]]]]]].
destruct HF1; destruct HF2.
assert (HP : A <> B /\ B <> D /\ a <> b /\ b <> d) by (apply EqR_diffs with K k; auto); spliter.
split; intro.
- assert (HP : Parallelogram A B D K) by (apply Rectangle_Parallelogram in H; auto).
assert (HC : Col A B D) by (apply not_strict_par1 with K C; Col; apply plg_par_1 in HP; auto).
assert (HPF : Parallelogram_flat A B D K) by (apply plg_col_plgf; auto).
assert (HPts : A = K /\ B = D \/ A = B /\ K = D) by (apply plgf_rect_id; auto).
destruct HPts; destruct H8; auto.
-assert (HP : Parallelogram a b d k) by (apply Rectangle_Parallelogram in H1; auto).
assert (HC : Col a b d) by (apply not_strict_par1 with k c; Col; apply plg_par_1 in HP; auto).
assert (HPF : Parallelogram_flat a b d k) by (apply plg_col_plgf; auto).
assert (HPts : a = k /\ b = d \/ a = b /\ k = d) by (apply plgf_rect_id; auto).
destruct HPts; destruct H8; auto.
Qed.

Lemma EqT_Convex A B C D E F G H:
  Convex A C B D -> ~ Col A B C -> ~ Col A B D -> First_circumscribed_rectangle A B C E F ->
  First_circumscribed_rectangle A B D H G -> Bet G A F /\ Bet H B E.
Proof.
intros HCV HNC1 HNC2 HF1 HF2.
apply not_col_distincts in HNC1; apply not_col_distincts in HNC2.
destruct HNC1 as [HNC1 [HNAC [HNBC HNAB]]]; destruct HNC2 as [HNC2 [_ [HNBD HNAD]]].
destruct HCV as [M [HB1 HB2]].
assert (HCV : Convex A C B D) by (exists M; auto).
assert (HR1 : Rectangle A B E F) by (destruct HF1; auto).
assert (HR2 : Rectangle A B H G) by (destruct HF2; auto).
assert (HC1 : Col C E F) by (destruct HF1; auto).
assert (HC2 : Col D H G) by (destruct HF2; auto).
assert (HNBE : B <> E)
  by (intro; treat_equalities; apply degenerated_rect_eq in HR1; treat_equalities; Col).
assert (HNBH : B <> H)
  by (intro; treat_equalities; apply degenerated_rect_eq in HR2; treat_equalities; Col).
assert (HTS1 : TS A B C D) by (do 2 (split; Col); exists M; split; Col).
split.
-assert (HC3 : Col G F A).
  {
  assert (HPer1 : Per B A F) by (apply rect_per1 in HR1; Perp).
  assert (HPer2 : Per B A G) by (apply rect_per1 in HR2; Perp).
  assert (HCop1 : Coplanar B F G A).
  apply coplanar_pseudo_trans with B A C; Cop; Col.
   - elim (eq_dec_points C F); [intro; treat_equalities; Cop|intro HAS].
     cut (Par A B C F); [Cop|].
     apply par_col4__par with A B F E; Col.
     apply Rectangle_Parallelogram, plg_par_1 in HR1; Par.
   - apply coplanar_pseudo_trans with A B D; Cop.
     elim (eq_dec_points G D); [intro; treat_equalities; Cop|intro HBT].
     cut (Par A B D G); [Cop|].
     apply par_col4__par with A B H G; Col.
     apply Rectangle_Parallelogram, plg_par_1 in HR2; Par.
  - apply cop_per2__col with B; Perp; Cop.
  }
assert (HTS2 : TS A B G F).
  {
  apply l9_2.
  assert (HOS1 : OS A B C F).
    {
    elim (eq_dec_points C F); [intro; treat_equalities; apply one_side_reflexivity; Col|intro].
    apply Rectangle_Parallelogram, plg_par_1 in HR1; auto.
    assert (HPar : Par A B F C) by (apply par_col_par with E; Par; Col).
    apply l12_6; apply par_not_col_strict with C; Col; Par.
    }
  assert (HOS2 : OS A B D G).
    {
    elim (eq_dec_points D G); [intro; treat_equalities; apply one_side_reflexivity; Col|intro].
    apply Rectangle_Parallelogram, plg_par_1 in HR2; auto.
    assert (HPar : Par A B G D) by (apply par_col_par with H; Col; Par).
    apply l12_6; apply par_not_col_strict with D; Col; Par.
    }
  apply l9_8_2 with C; auto.
  apply l9_2.
  apply l9_8_2 with D; auto; apply l9_2; auto.
  }
apply col_two_sides_bet with B; Col.

-assert (HC3 : Col H E B).
  {
  assert (HPer1 : Per A B H) by (apply rect_per2 in HR2; Perp).
  assert (HPer2 : Per A B E) by (apply rect_per2 in HR1; Perp).
  assert (HCop1 : Coplanar A E H B).
  apply coplanar_pseudo_trans with A B C; Cop; Col.
   - elim (eq_dec_points C E); [intro; treat_equalities; Cop|intro HAS].
     cut (Par A B C E); [Cop|].
     apply par_col4__par with A B F E; Col.
     apply Rectangle_Parallelogram, plg_par_1 in HR1; Par.
   - apply coplanar_pseudo_trans with B A D; Cop; Col.
     elim (eq_dec_points H D); [intro; treat_equalities; Cop|intro HBT].
     cut (Par A B D H); [Cop|].
     apply par_col4__par with A B H G; Col.
     apply Rectangle_Parallelogram, plg_par_1 in HR2; Par.
  - apply cop_per2__col with A; Perp; Cop.
  }
assert (HTS2 : TS B A H E).
  {
  apply l9_2.
  assert (HOS1 : OS B A C E).
    {
    elim (eq_dec_points C E); [intro; treat_equalities; apply one_side_reflexivity; Col|intro].
    apply Rectangle_Parallelogram, plg_par_1 in HR1; auto.
    assert (HPar : Par A B E C) by (apply par_col_par with F; Par; Col).
    apply l12_6; apply par_not_col_strict with C; Col; Par.
    }
  assert (HOS2 : OS B A D H).
    {
    elim (eq_dec_points D H); [intro; treat_equalities; apply one_side_reflexivity; Col|intro].
    apply Rectangle_Parallelogram, plg_par_1 in HR2; auto.
    assert (HPar : Par A B H D) by (apply par_col_par with G; Col; Par).
    apply l12_6; apply par_not_col_strict with D; Col; Par.
    }
  apply l9_8_2 with C; auto.
  apply l9_2.
  apply l9_8_2 with D; auto; apply l9_2, invert_two_sides; auto.
  }
apply col_two_sides_bet with A; Col.
Qed.

(* 7.5 A priori pas utilisé*)
Lemma quadrilateral_cut_in_halves A B C D P Q S T :
  Convex S P T Q ->
  First_circumscribed_rectangle P Q S A D ->
  First_circumscribed_rectangle P Q T B C ->
  EqT P Q S P Q T ->
  EqR P Q A D P Q B C.
Proof.
intros HCV HF1 HF2 HEQT.
assert (HNC :  ~ Col P Q S /\ ~ Col P Q T) by (apply EqT_not_col; auto).
destruct HNC as [HNC1 HNC2].
destruct HEQT as [E [F [e [f [HF3 [HF4 HEQR]]]]]].
destruct HCV as [M [HB1 HB2]].
assert (HCV2 : Convex P S Q T) by (exists M; auto).
assert (HR1 : Rectangle P Q A D) by (destruct HF1; auto).
assert (HR2 : Rectangle P Q B C) by (destruct HF2; auto).
assert (HR3 : Rectangle P Q E F) by (destruct HF3; auto).
assert (HR4 : Rectangle P Q e f) by (destruct HF4; auto).
assert (HC1 : Col S A D) by (destruct HF1; auto).
assert (HC2 : Col T B C) by (destruct HF2; auto).
assert (HC3 : Col S E F) by (destruct HF3; auto).
assert (HC4 : Col T e f) by (destruct HF4; auto).
assert (HP : P <> Q /\ Q <> E /\ P <> Q /\ Q <> e) by (apply EqR_diffs with F f; auto); spliter.
assert (HCong1 : Cong Q E Q e) by (apply B5_5 in HEQR; auto; Cong).

assert (HNQA : Q <> A)
  by (intro; treat_equalities; apply degenerated_rect_eq in HR1; treat_equalities; Col).
assert (HNQB : Q <> B)
  by (intro; treat_equalities; apply degenerated_rect_eq in HR2; treat_equalities; Col).
apply B5_5; auto; Cong.

assert (HPar1 : Par A D E F).
  {
  apply Rectangle_Parallelogram in HR1; apply Rectangle_Parallelogram in HR3.
  apply plg_par_1 in HR1; apply plg_par_1 in HR3; auto.
  apply par_trans with P Q; Par.
  }
assert (HB : Bet C P D /\ Bet B Q A) by (apply EqT_Convex with S T; auto).
assert (HC5 : Col A D E) by (apply not_strict_par1 with F S; Col).

assert (HCop3 : Coplanar P A E Q).
  {
  apply coplanar_pseudo_trans with P Q S; Cop.
  - elim (eq_dec_points A S); [intro; treat_equalities; Cop|intro HAS].
    cut (Par P Q A S); [Cop|].
    apply par_col4__par with P Q A D; Col.
    apply Rectangle_Parallelogram, plg_par_1 in HR1; Par.
  - elim (eq_dec_points E S); [intro; treat_equalities; Cop|intro HES].
    cut (Par P Q E S); [Cop|].
    apply par_col4__par with P Q E F; Col.
    apply Rectangle_Parallelogram, plg_par_1 in HR3; Par.
  }
assert (HC8 : Col A E Q).
  {
  apply (cop_per2__col P A E Q); Perp.
  apply rect_per4 with D, rect_permut, rect_permut; auto.
  apply rect_per4 with F, rect_permut, rect_permut; auto.
  }
assert (HAE : A = E).
  {
  apply l6_21 with A D Q A; Col.
  apply Rectangle_Parallelogram, plg_par_1 in HR1; Par.
  apply (par_not_col_strict _ _ _ _ S) in HR1; Col.
  intro; apply (par_not_col _ _ _ _ Q) in HR1; Col.
  }
cut (B = e); [intro; treat_equalities; Cong|].
assert (HCop4 : Coplanar P B e Q).
  {
  apply coplanar_pseudo_trans with P Q T; Cop.
  - elim (eq_dec_points B T); [intro; treat_equalities; Cop|intro HBT].
    cut (Par P Q B T); [Cop|].
    apply par_col4__par with P Q B C; Col.
    apply Rectangle_Parallelogram, plg_par_1 in HR2; Par.
  - elim (eq_dec_points e T); [intro; treat_equalities; Cop|intro HeT].
    cut (Par P Q e T); [Cop|].
    apply par_col4__par with P Q e f; Col.
    apply Rectangle_Parallelogram, plg_par_1 in HR4; Par.
  }
assert (HC9 : Col B e Q).
  {
  apply (cop_per2__col P B e Q); Perp.
  apply rect_per4 with C, rect_permut, rect_permut; auto.
  apply rect_per4 with f, rect_permut, rect_permut; auto.
  }
assert (HNC5 : ~ Col B C Q).
  {
  intro.
  apply rect_permut in HR2.
  assert (HPF : Parallelogram_flat Q B C P)
    by (apply Rectangle_Parallelogram in HR2; apply plg_col_plgf; Col).
  assert (HP : Q = P /\ B = C \/ Q = B /\ P = C) by (apply plgf_rect_id; auto).
  destruct HP; destruct H4; auto.
  }
assert (HPar2 : Par B C e f).
  {
  apply Rectangle_Parallelogram in HR2; apply Rectangle_Parallelogram in HR4.
  apply plg_par_1 in HR2; apply plg_par_1 in HR4; auto.
  apply par_trans with P Q; Par.
  }
assert (HC10 :  Col B C e) by (apply not_strict_par1 with f T; Col).
apply l6_21 with B C Q B; Col.
Qed.

(* 7.6 *)
Lemma halves_of_equals A B C D a b c d :
  TS A C B D -> TS a c b d ->
  EqT A C B A C D -> EqT a c b a c d ->
  EqQ A B C D a b c d ->
  EqT A C B a c b.
Proof.
intros HTS1 HTS2 HE1 HE2 HEQ1.
assert (HNC : ~ Col A C B /\ ~ Col A C D) by (apply EqT_not_col; auto).
assert (HNC0 : ~ Col a c b /\ ~ Col a c d) by (apply EqT_not_col; auto).
destruct HNC as [HNC1 HNC2].
destruct HNC0 as [HNC3 HNC4].
destruct HEQ1 as [G [H [I [J [g [h [i [j [HCR1 [HCR2 HEQR1]]]]]]]]]].
destruct HE1 as [K [L [N [M [HF1 [HF2 HEQR2]]]]]].
destruct HE2 as [k [l [n [m [HF3 [HF4 HEQR3]]]]]].
assert (HP : A <> C /\ C <> K /\ A <> C /\ C <> N) by (apply EqR_diffs with L M; auto); spliter.
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
cut (EqR M L K N l k n m).
intro HEQR4.
assert (HEQR5 : EqR A C K L l k c a) by (apply rectangle_cut_in_halves with M N n m; auto).
exists K, L, k, l.
do 2 (split; auto).
assert (HNlk : l <> k)
  by (intro; treat_equalities; apply rect_permut in HR3; apply degenerated_rect_eq in HR3; auto).
assert (HR5 : Rectangle l k c a) by (apply rect_comm2 in HR3; do 2 (apply rect_permut in HR3); auto).
apply EqR_trans with l k c a; auto.
apply EqR_perm; auto.
(*il faut utiliser EqR G H I J g h i j en montrant que c'est la même équivalence, donc détruire HCR1 et HCR2 mais on a besoin de l'équivalence des rectangles circonscrits*)
Admitted.

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

Lemma paste4 A B C D F G H J K L M P e m :
  EqQ A B m D F K H G -> EqQ D B e C G H M L ->
  Bet A P C -> Bet B P D -> Bet K H M -> Bet F G L ->
  Bet B m D -> Bet B e C -> Bet F J M -> Bet K J L ->
  EqQ A B C D F K M L.
Proof.
Admitted.

End Beeson.