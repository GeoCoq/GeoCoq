Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Main.Meta_theory.Parallel_postulates.tarski_s_euclid_remove_degenerated_cases.
Require Import GeoCoq.Main.Annexes.perp_bisect.
Require Import GeoCoq.Main.Tarski_dev.Ch12_parallel.

Section TCP_tarski.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma impossible_case_1 :
  forall A B C x y,
  Bet A B x ->
  Bet C y A ->
  Par_strict B C x y ->
  False.
Proof.
intros A B C x y.
intros HABx HACy HPar.
apply between_symmetry in HABx.
assert (HI := inner_pasch x C A B y HABx HACy); destruct HI as [I [HBCI HIxy]].
apply HPar; exists I; split; Col.
Qed.

Lemma impossible_case_2 :
  forall A B C D T x y,
  A <> D ->
  B <> D ->
  C <> D ->
  D <> T ->
  ~ Col A B C ->
  Col A B x ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet y A C ->
  Bet x T y ->
  False.
Proof.
intros A B C D T x y.
intros HAD HBD HCD HDT.
intros HABC HABx HADT HBCT HBDC HACy HxTy.
assert (HAy : A <> y) by (intro; apply HBCT; ColR).
revert HABx.
apply one_side_not_col124 with T.
apply bet_ts__os with y; Between.
apply l9_2, l9_8_2 with C.
  apply bet__ts; Between.
assert (HOS : OS A B C D) by (apply invert_one_side, out_one_side; [Col|Out]).
apply one_side_transitivity with D; Side.
apply one_side_not_col124 in HOS.
apply out_one_side; Out.
Qed.

Lemma impossible_case_3 :
  forall A B C D T x y,
  A <> D ->
  B <> D ->
  C <> D ->
  D <> T ->
  ~ Col A B C ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B x A ->
  Bet x T y ->
  Par_strict B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HAD HBD HCD HDT.
intros HABC HADT HBCT HBDC HABx HxTy HPar.
apply l12_6 in HPar.
absurd (TS B C x y); Side.
apply bet_ts__ts with T; trivial.
apply l9_8_2 with A.
  repeat split; Col; exists D; split; Col.
assert_diffs; apply out_one_side; [Col|Out].
Qed.

Lemma impossible_case_4_1 :
  forall A B C D T x y,
  A <> D ->
  C <> D ->
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Out A B x ->
  Bet T y x ->
  False.
Proof.
intros A B C D T x y.
intros HAD HCD.
intros HABC HACy HADT HBCT HBDC HABx HTyx.
revert HACy.
apply one_side_not_col124 with T.
apply l9_17 with x; trivial.
assert (HOS : OS A C B D) by (apply invert_one_side, out_one_side; [Col|Out]).
apply one_side_transitivity with D.
  apply one_side_not_col124 in HOS; apply out_one_side; Out.
apply one_side_transitivity with B; [Side|].
assert (HACA : Col A C A) by Col.
assert (HABx' : Col B x A) by Col.
assert (H := l9_19 A C B x A HACA HABx'); rewrite H.
split; Col.
Qed.

Lemma impossible_case_4_2 :
  forall A B C D T x y,
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B A x ->
  Bet T y x ->
  Par_strict B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HABC HACy HADT HBCT HBDC HABx HTyx HPar.
assert (HTS : TS B C A T) by (repeat split; [..|exists D; split]; Col).
assert (HOS : OS B C A x).
{
  assert (HBCB : Col B C B) by Col.
  assert (HABx' : Col A x B) by Col.
  assert (H := l9_19 B C A x B HBCB HABx'); rewrite H.
  apply not_col_distincts in HABC; spliter.
  split; [Out|Col].
}
assert (HTS' : TS B C x T) by (apply l9_8_2 with A; assumption);
clear HTS; clear HOS; destruct HTS' as [_ [_ [I [HBCI HITx]]]].
assert (HTx : T <> x) by (intro; treat_equalities; apply HBCT; Col).
assert (HPar' : Par_strict B C x T) by (apply par_strict_col_par_strict with y; Col).
apply HPar'; exists I; split; Col.
Qed.

Lemma impossible_case_4 :
  forall A B C D T x y,
  A <> D ->
  B <> D ->
  C <> D ->
  D <> T ->
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col A B x ->
  Bet T y x ->
  Par_strict B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HAD HBD HCD HDT.
intros HABC HACy HADT HBCT HBDC HABx HTyx HPar.
revert HABx.
destruct (or_bet_out B A x) as [HABx|[HABx|HABx]]; [intro..|Col].

  apply (impossible_case_4_2 A B C D T x y); auto.

  apply (impossible_case_4_1 A B C D T x y); auto.
Qed.

Lemma impossible_two_sides_not_col : forall A B C D T Y,
  A <> D ->
  B <> D ->
  C <> D ->
  D <> T ->
  ~ Col A B C ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B Y T ->
  ~ Col A C Y.
Proof.
intros A B C D T Y HAD HBD HCD HDT.
intros HABC HADT HBCT HBDC HBYT.
apply one_side_not_col124 with B.
apply l9_17 with T; trivial.
assert (HOS : OS A C B D).
  apply invert_one_side, out_one_side; [Col|Out].
apply one_side_transitivity with D; trivial.
apply one_side_not_col124 in HOS.
apply out_one_side; Out.
Qed.

(*
Lemma triangle_circumscription_aux : forall A B C P,
  Cong A P B P -> Cong A P C P -> exists CC, Cong A CC B CC /\ Cong A CC C CC /\ Coplanar A B C CC.
Proof.
  intros A B C D HCong1 HCong2.
  destruct (cop_dec A B C D).
    exists D; repeat split; assumption.
  destruct (l11_62_existence A B C D) as [CC [HCop HCC]].
  exists CC.
  assert (CC <> D) by (intro; subst; Cop).
  assert (Per B CC D) by Cop.
  assert (A <> CC).
  { intro; subst CC.
    destruct (l11_46 B A D) as [_ []]; auto.
    assert_diffs; apply per_not_col; auto.
  }
  assert (Per A CC D) by Cop.
  repeat split; trivial.
  - destruct (cong2_per2__cong_conga2 A CC D B CC D); Cong.
    intro; subst CC.
    destruct (l11_46 A B D) as [_ []]; Cong.
    assert_diffs; apply per_not_col; auto.
  - assert (Per C CC D) by Cop.
    destruct (cong2_per2__cong_conga2 A CC D C CC D); Cong.
    intro; subst CC.
    destruct (l11_46 A C D) as [_ []]; Cong.
    apply per_not_col; auto.
Qed.
*)

Lemma triangle_circumscription_implies_tarski_s_euclid_aux1 :
  forall A B C D T X Y Z M1 Z1,
  triangle_circumscription_principle ->
  B <> D ->
  C <> D ->
  D <> T ->
  T <> X ->
  ~ Col A B C ->
  Col A B M1 ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col T Y Z ->
  Bet Y T X ->
  Bet Y M1 Z1 ->
  Cong Y T T X ->
  Cong Y M1 M1 Z1 ->
  Perp B C T Z ->
  Perp A B Y Z1 ->
  exists x, Col A B x /\ Par_strict B C x T /\ Cong X x Y x.
Proof.
intros A B C D T X Y Z M1 Z1; intro HTC.
intros HBD HCD HDT HTX.
intros HABC HABM1 HADT HBCT HBDC HTYZ HYTX HYM1Z1.
intros HCong1 HCong2 HPerp1 HPerp2.
assert (A <> D) by (intro; subst; apply HABC; Col).
assert_diffs.
assert (HCopA : Coplanar B C T A) by (exists D; left; split; Col).
assert (HCopB : Coplanar B C T B) by Cop.
assert (HCopC : Coplanar B C T C) by Cop.
assert (HCopT : Coplanar B C T T) by Cop.
assert (HCopZ : Coplanar B C T Z) by Cop.
assert (HCopY : Coplanar B C T Y) by (apply col_cop__cop with Z; Col).
assert (HCopX : Coplanar B C T X) by (apply col_cop__cop with Y; Col).
assert (HXYZ1 : ~ Col X Y Z1).
  {
  intro; apply HABC, col_permutation_4, par_id.
  assert (Col T Z Z1) by ColR.
  assert (Coplanar B C Y Z1) by (apply col2_cop__cop with T Z; Col).
  apply l12_9 with Y Z1; [Cop..| |Perp|].
    apply coplanar_pseudo_trans with B C T; auto; apply col_cop__cop with Z; auto.
  apply perp_sym, perp_col2 with T Z; Perp; Col.
  }
destruct (HTC X Y Z1 HXYZ1) as [x [HCong3 [HCong4 HCop1]]]; exists x.
assert (HYM1 : Y <> M1) by (intro; treat_equalities; auto).
assert (HCopZ1 : Coplanar B C T Z1).
  {
  assert (~ Col A B Y)
    by (intro; destruct (perp_not_col2 A B Y Z1) as [|HNCol]; Perp; apply HNCol; ColR).
  apply coplanar_pseudo_trans with A B Y; [| |apply coplanar_pseudo_trans with B C T..|]; Cop.
  }
assert (HCopx : Coplanar B C T x).
  apply coplanar_pseudo_trans with X Y Z1; trivial; apply coplanar_pseudo_trans with B C T; assumption.
assert (Col A B x).
  {
  apply cong_cop2_perp_bisect_col with Y Z1; trivial.
    apply coplanar_pseudo_trans with B C T; assumption.
    apply coplanar_pseudo_trans with B C T; assumption.
    apply cong_transitivity with X x; Cong.
  repeat split; Perp.
  exists M1; repeat split; Between; Cong.
  }
do 2 (split; trivial).
apply par_not_col_strict with T; Col.
apply l12_9 with X Y; [apply coplanar_pseudo_trans with B C T; assumption..| |].
  apply perp_sym, perp_col2 with T Z; Perp; ColR.
apply perp_bisect_perp; apply cong_cop_perp_bisect; Cong; [|Cop].
intro; subst; apply HABC; ColR.
Qed.

Lemma triangle_circumscription_implies_tarski_s_euclid_aux :
  forall A B C D T X Y Z M1 Z1 M2 Z2,
  triangle_circumscription_principle ->
  B <> D ->
  C <> D ->
  D <> T ->
  T <> X ->
  ~ Col A B C ->
  Col A B M1 ->
  Col A C M2 ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col T Y Z ->
  Bet Y T X ->
  Bet Y M1 Z1 ->
  Bet Y M2 Z2 ->
  Cong Y T T X ->
  Cong Y M1 M1 Z1 ->
  Cong Y M2 M2 Z2 ->
  Perp B C T Z ->
  Perp A B Y Z1 ->
  Perp A C Y Z2 ->
  exists x, exists y, Bet A B x /\ Bet A C y /\ Bet x T y.
Proof.
intros A B C D T X Y Z M1 Z1 M2 Z2; intro HTC.
intros HBD HCD HDT HTX.
intros HABC HABM1 HACM2 HADT HBCT HBDC HTYZ HYTX HYM1Z1.
intros HYM2Z2 HCong5 HCong6 HCong7 HPerp1 HPerp2 HPerp3.
assert (Hx := triangle_circumscription_implies_tarski_s_euclid_aux1 A B C D T X Y Z M1 Z1).
destruct Hx as [x [HABx [Hx1 Hx2]]]; [assumption..|]; exists x.
assert (Hy := triangle_circumscription_implies_tarski_s_euclid_aux1 A C B D T X Y Z M2 Z2).
destruct Hy as [y [HACy [Hy1 Hy2]]]; [Between; Col; Perp..|]; exists y.
assert (HxTy : Col x T y).
  {
  elim (eq_dec_points T x); intro; [|elim (eq_dec_points T y); intro]; [subst; Col..|].
  assert_diffs.
  apply col_permutation_4, cop_perp2__col with X Y;
    [|apply perp_bisect_perp, cong_cop_perp_bisect; Cong; Cop..].
  assert (Coplanar B C T Y) by (apply col_cop__cop with Z; Col; Cop).
  assert (Coplanar B C T X) by (apply col_cop__cop with Y; Col).
  apply coplanar_pseudo_trans with B C T; Cop.
  }
assert (HPar : Par_strict B C x y).
  {
  apply par_strict_col_par_strict with T; Col.
  intro; subst y.
  destruct HPerp3 as [_ [HAC _]].
  assert (A = x) by (apply (l6_21 A B C A); Col).
  subst; apply Hx1; exists D; split; Col.
  }
assert (A <> D) by (intro; subst; apply HABC; Col).

elim HxTy; clear HxTy; intro HxTy.

  elim HABx; clear HABx; intro HABx.

    elim HACy; clear HACy; intro HACy; auto.
    exfalso; elim HACy; clear HACy; intro HACy.

      apply (impossible_case_1 A B C x y); assumption.

      apply (impossible_case_2 A B C D T x y); Col.

    exfalso; elim HABx; clear HABx; intro HABx.

      apply (impossible_case_3 A B C D T x y); assumption.

      apply (impossible_case_2 A C B D T y x); Col; Between.

  exfalso; elim HxTy; clear HxTy; intro HxTy.

    apply (impossible_case_4 A B C D T x y); assumption.

    apply (impossible_case_4 A C B D T y x); Between; Col; Par.
Qed.

Lemma triangle_circumscription_implies_tarski_s_euclid :
  triangle_circumscription_principle ->
  tarski_s_parallel_postulate.
Proof.
unfold tarski_s_parallel_postulate.
intro HTC; apply tarski_s_euclid_remove_degenerated_cases.
intros A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC HBCT.
clear HAT HBT HCT.
assert (HY := l8_18_existence B C T HBCT); destruct HY as [Y [HBCY HPerp]].
revert B C HAB HAC HBC HBD HCD HABC HBDC HBCT HBCY HPerp.
cut (forall B C, A <> B -> A <> C -> B <> C -> B <> D -> C <> D -> ~ Col A B C ->
                 Bet B D C -> ~ Col B C T -> Col B C Y -> Perp B C T Y -> B <> Y ->
                 exists x y : Tpoint, Bet A B x /\ Bet A C y /\ Bet x T y).
  {
  intros Haux B C HAB HAC HBC HBD HCD HABC HBDC HBCT HBCY HPerp.
  elim (eq_dec_points B Y); auto.
  intro HBY.
  elim (eq_dec_points C Y); intro HCY.
    subst; exfalso; apply HBC; reflexivity.
  apply between_symmetry in HBDC.
  apply perp_left_comm in HPerp.
  destruct (Haux C B) as [y [x [HACy [HABx HxTy]]]]; Col.
  exists x, y; repeat split; Between.
  }
intros B C HAB HAC HBC HBD HCD HABC HBDC HBCT HBCY HPerp HBY.
elim (eq_dec_points C Y); intro HCY.

  {
  treat_equalities.
  assert (HCT : C <> T) by (apply not_col_distincts in HBCT; spliter; auto).
  assert (HY := midpoint_existence C T); destruct HY as [Y HY].
  assert (HAY : A <> Y) by (intro; treat_equalities; apply HABC; ColR).
  assert (H := midpoint_distinct_1 Y C T HCT HY); destruct H as [HCY HTY];
  apply not_eq_sym in HCY; apply not_eq_sym in HTY.
  assert (HBY : B <> Y) by (intro; subst; apply HBCT; Col).
  destruct HY as [HCTY HCYTY].
  assert (HACY : ~ Col A B Y) by (apply impossible_two_sides_not_col with C D T; Between; Col).
  assert (HX := symmetric_point_construction Y T); destruct HX as [X HX].
  assert (H := midpoint_distinct_2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; [|contradiction]; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; [|contradiction]; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  elim HZ2; clear HZ2; intro HZ2; [|treat_equalities; exfalso; apply HABC; ColR].
  elim HZ1; clear HZ1; intro HZ1; [|treat_equalities; contradiction].
  apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y C M1 Z1 M2 Z2; Col.
  }

  {
  assert (HX := symmetric_point_construction Y T); destruct HX as [X HX].
  assert (H := perp_distinct B C T Y HPerp); destruct H as [Hclear HTY]; clear Hclear.
  assert (H := midpoint_distinct_2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; [|contradiction]; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; [|contradiction]; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  assert (HABY : ~ Col A B Y) . (intro; apply HBY; apply l6_21 with A B C B; Col).
  assert (HACY : ~ Col A C Y) by (intro; apply HCY; apply l6_21 with A C B C; Col).
  elim HZ1; clear HZ1; intro HZ1; [|treat_equalities; contradiction].
  elim HZ2; clear HZ2; intro HZ2; [|treat_equalities; contradiction].
  apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y Y M1 Z1 M2 Z2; Col.
  }
Qed.

End TCP_tarski.
