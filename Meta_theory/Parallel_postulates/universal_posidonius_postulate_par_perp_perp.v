Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.rah_thales_postulate.
Require Import GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_weak_triangle_circumscription_principle.
Require Import GeoCoq.Meta_theory.Parallel_postulates.thales_postulate_thales_converse_postulate.
Require Import GeoCoq.Meta_theory.Parallel_postulates.weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section universal_posidonius_postulate_perpendicular_transversal_postulate.

Context `{T2D:Tarski_2D}.

Lemma universal_posidonius_postulate__perpendicular_transversal_postulate :
  universal_posidonius_postulate -> perpendicular_transversal_postulate.
Proof.
intros HP A B C D P Q HPar HPerp1.
elim HPar; intro HParS; [|destruct HParS as [_ [_ [HC1 HC2]]]; assert_diffs;
                          apply perp_sym; apply perp_col0 with A B; Col; ColR].
assert (H := HPerp1); destruct H as [R HR];
apply perp_in_col in HR; destruct HR as [HC1 HC2].
assert (HEF : exists E F, Col A B E /\ Col C D F /\ Perp A B E F /\ E <> R).
  {
  destruct (l8_18_existence A B C) as [E1 [HC3 HPerp2]];
  [apply par_strict_not_col_1 with D; Par|].
  destruct (l8_18_existence A B D) as [E2 [HC4 HPerp3]];
  [apply par_strict_not_col_1 with C; Par|].
  elim (eq_dec_points E1 R); intro; treat_equalities;
  [|exists E1, C; repeat (split; Col; Perp)].
  elim (eq_dec_points E1 E2); intro; treat_equalities;
  [|exists E2, D; repeat (split; Col; Perp)].
  assert (HC4 : Col E1 C D) by (apply perp_perp_col with A B; Perp).
  destruct HParS as [_ [_ [_ HF]]]; exfalso; apply HF; exists E1; Col.
  }
destruct HEF as [E [F [HC3 [HC4 [HPerp2 HD1]]]]].
assert (HGH : exists G H,
                Col A B G /\ Col C D H /\ Perp A B G H /\ E <> G /\ F <> H).
  {
  destruct (l8_18_existence A B C) as [E1 [HC5 HPerp3]];
  [apply par_strict_not_col_1 with D; Par|].
  destruct (l8_18_existence A B D) as [E2 [HC6 HPerp4]];
  [apply par_strict_not_col_1 with C; Par|].
  elim (eq_dec_points E1 E); intro HD; treat_equalities;
  [|exists E1, C; repeat (split; Col; Perp); intro; treat_equalities; apply HD;
    apply l6_21 with A B F E; assert_diffs; Col;
    [elim (perp_not_col2 _ _ _ _ HPerp2); Col|
     apply perp_perp_col with A B; Perp]].
  elim (eq_dec_points E1 E2); intro HD'; treat_equalities;
  [assert (HC7 : Col E1 C D) by (apply perp_perp_col with A B; Perp);
   destruct HParS as [_ [_ [_ HF]]]; exfalso; apply HF; exists E1; Col|].
  exists E2, D; repeat (split; Col; Perp); intro; treat_equalities; apply HD'.
  apply l6_21 with A B F E1; assert_diffs; Col;
  [elim (perp_not_col2 _ _ _ _ HPerp2); Col|apply perp_perp_col with A B; Perp].
  }
destruct HGH as [G [H [HC5 [HC6 [HPerp3 [HD2 HD3]]]]]].
assert (HSacc1 : Saccheri E F H G).
  {
  split; [apply perp_per_1; apply perp_col0 with A B; Perp|].
  split; [apply perp_per_1; apply perp_sym; apply perp_col0 with A B; Perp|].
  split; [assert (Cong E F G H); Cong; apply HP with A B C D; Col|].
  apply l12_6; apply par_strict_col2_par_strict with C D; Col.
  apply par_strict_symmetry;
  apply par_strict_col2_par_strict with A B; Col; Par.
  }
destruct (midpoint_existence E G) as [M1 HMid1].
destruct (midpoint_existence F H) as [M2 HMid2].
assert (HLamb := mid2_sac__lam6521 _ _ _ _ _ _ HSacc1 HMid2 HMid1).
assert (HSacc2 : Saccheri E F M2 M1).
  {
  split; [unfold Lambert in *; spliter; Perp|].
  split; [unfold Lambert in *; spliter; Perp|].
  assert (HCong : Cong E F M1 M2); [|split; Cong].
    {
    apply HP with A B C D; Col; try solve [assert_diffs; assert_cols; ColR].
    apply perp_sym; apply perp_col0 with E M1;
    try solve [assert_diffs; assert_cols; Col; ColR].
    apply per_perp; unfold Lambert in *; spliter; Perp.
    }
  apply l12_6; apply par_strict_col2_par_strict with C D; Col;
  try solve [assert_diffs; assert_cols; Col; ColR].
  apply par_strict_symmetry;
  apply par_strict_col2_par_strict with A B; Col; Par;
  assert_diffs; assert_cols; Col; ColR.
  }
assert (HRAH : postulate_of_right_saccheri_quadrilaterals)
  by (apply per_sac__rah with M1 M2 F E; try apply sac_perm;
      unfold Lambert in *; spliter; auto).
assert (HP' : forall A1 A2 B1 B2 C1 C2 D1 D2,
          Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
          ~ Col A1 A2 D1 -> ~ Col B1 B2 C1 ->
          exists I, Col C1 C2 I /\ Col D1 D2 I).
  {
  cut bachmann_s_lotschnittaxiom.

    {
    clear HP; clear dependent P; clear dependent Q; clear dependent R.
    intros bla A1 A2 B1 B2 C1 C2 D1 D2 HPerpAB HPerpAC HPerpBD HNCol1 HNCol2.
    assert (HParA : Par_strict A1 A2 D1 D2).
      apply par_not_col_strict with D1; Col; apply l12_9 with B1 B2; Perp.
    assert (HParB : Par_strict B1 B2 C1 C2).
      apply par_not_col_strict with C1; Col; apply l12_9 with A1 A2; Perp.
    assert (HP := HPerpAC); destruct HP as [P [_ [_ [HP1 [HP2 HP3]]]]].
    assert (HQ := HPerpAB); destruct HQ as [Q [_ [_ [HQ1 [HQ2 HQ3]]]]].
    assert (HR := HPerpBD); destruct HR as [R [_ [_ [HR1 [HR2 HR3]]]]].
    assert (HNCol3 : ~ Col P B1 B2) by (apply par_not_col with C1 C2; Par).
    assert (HNCol4 : ~ Col R A1 A2) by (apply par_not_col with D1 D2; Par).
    assert (HPQ : P <> Q) by (intro; subst; contradiction).
    assert (HQR : Q <> R) by (intro; subst; contradiction).
    assert (Per P Q R) by (apply HQ3; trivial).
    destruct (diff_col_ex3 C1 C2 P) as [P1 [HC1P1 [HC2P1 [HPP1 HCP1]]]]; Col.
    destruct (diff_col_ex3 D1 D2 R) as [R1 [HD1R1 [HD2R1 [HRR1 HDR1]]]]; Col.
    destruct (bla P Q R P1 R1) as [I [HI1 HI2]]; auto.
      apply HP3; Col.
      apply HR3; Col.
    exists I.
    split; assert_diffs; ColR.
    }

    {
    apply weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom.
    apply thales_converse_postulate__weak_triangle_circumscription_principle.
    apply thales_postulate__thales_converse_postulate.
    apply rah__thales_postulate; assumption.
    }
  }
destruct (HP' A B E F P Q C D) as [S [HC7 HC8]]; Col;
[apply perp_col0 with F M2; try (apply perp_sym; apply per_perp);
 try solve [assert_diffs; assert_cols; Col; ColR];
 rewrite (lam_per__rah M1 _ _ _); try apply lam_perm; assumption|
 intro; destruct HParS as [_ [_ [_ HF]]]; exfalso; apply HF; exists C; Col|
 intro; apply HD1; assert (HC7 : Col Q E F)
   by (apply perp_perp_col_col with P A B; Col; Perp);
 elim (perp_not_col2 _ _ _ _ HPerp2); intro;
 [apply l6_21 with A B E F|apply l6_21 with A B F E]; assert_diffs; Col; ColR|].
assert (HSacc3 : Saccheri E F S R).
  {
  split; [apply perp_per_1; apply perp_col0 with A B; Perp|].
  split; [apply perp_per_1; apply perp_col0 with P Q; try apply perp_col0 with A B; Perp;
          intro; treat_equalities; destruct HParS as [_ [_ [_ HF]]];
          exfalso; apply HF; exists S; Col|].
  split; [assert (Cong E F R S); Cong; apply HP with A B C D; Col;
          apply perp_col0 with P Q; Perp; intro; treat_equalities;
          destruct HParS as [_ [_ [_ HF]]]; exfalso; apply HF; exists R; Col|].
  apply l12_6; apply par_strict_col2_par_strict with C D; Col;
  try solve [assert_diffs; assert_cols; Col; ColR];
  try apply par_strict_symmetry;
  try apply par_strict_col2_par_strict with A B; Col; Par.
  intro; treat_equalities; assert (HC8 : Col E P Q)
    by (apply perp_perp_col_col with F A B; Col; Perp).
  apply HD1; elim (perp_not_col2 _ _ _ _ HPerp2); intro;
  [apply l6_21 with A B E F|apply l6_21 with A B F E];
  assert_diffs; Col; try ColR.
  }
apply perp_col0 with S R; try solve [assert_diffs; assert_cols; Col; ColR].
apply perp_col0 with F S; try solve [assert_diffs; assert_cols; Col; ColR].
apply per_perp; try solve[apply sac_distincts in HSacc3; spliter; auto].
apply l8_2; apply HRAH with E; apply sac_perm; assumption.
Qed.

End universal_posidonius_postulate_perpendicular_transversal_postulate.