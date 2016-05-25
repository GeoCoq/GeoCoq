Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_thales_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_weak_triangle_circumscription_principle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_postulate_thales_converse_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.

Section posidonius_second_postulate_perpendicular_transversal_postulate.

Context `{T2D:Tarski_2D}.

Lemma posidonius_second_postulate__perpendicular_transversal_postulate :
  posidonius_second_postulate -> perpendicular_transversal_postulate.
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
  split; [apply perp_per_1; [assert_diffs|apply perp_col0 with A B]; Perp|].
  split; [apply perp_per_1; [assert_diffs|
                             apply perp_sym; apply perp_col0 with A B]; Perp|].
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
assert (HP' : bachmann_s_lotschnittaxiom).
  {
  apply weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom.
  apply thales_converse_postulate__weak_triangle_circumscription_principle.
  apply thales_postulate__thales_converse_postulate.
  apply rah__thales_postulate; assumption.
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
  split; [apply perp_per_1; [assert_diffs|apply perp_col0 with A B]; Perp|].
  split; [apply perp_per_1; [assert_diffs|apply perp_col0 with P Q;
                               try apply perp_col0 with A B]; Perp;
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

End posidonius_second_postulate_perpendicular_transversal_postulate.