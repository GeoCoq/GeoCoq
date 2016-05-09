Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section bachmann_s_lotschnittaxiom_existential_inverse_projection_postulate.

Context `{T2D:Tarski_2D}.

Lemma bachmann_s_lotschnittaxiom__existential_inverse_projection_postulate :
  bachmann_s_lotschnittaxiom -> existential_inverse_projection_postulate.
Proof.
intro HP; destruct lower_dim as [C [E [D H]]].
assert (HNC : ~ Col C E D) by auto; clear H.
destruct (l8_18_existence D E C) as [B [HC1 HPerp]]; Col.
assert (HF : exists F, Col D E F /\ B <> F); [|destruct HF as [F [HC2 HNE]]].
  {
  elim (perp_not_col2 _ _ _ _ (perp_sym _ _ _ _ HPerp)); intro;
  [exists D|exists E]; split; assert_diffs; Col.
  }
destruct (segment_construction_2 F B B C) as [A [H HCong1]]; auto.
assert (HC3 : Col D E A) by (induction H; assert_diffs; assert_cols; ColR).
clear H; assert (HPerp1 : Perp B A C B)
  by (apply perp_sym; apply perp_col0 with D E; assert_diffs; Perp).
clear HPerp; clear HC1; clear HC2; clear HC3;
clear HNE; clear HNC; clear D; clear E; clear F.
assert (HNC := perp_not_col _ _ _ HPerp1).
destruct (midpoint_existence A C) as [D HD]; exists A, B, D.
split; [intro; apply HNC; assert_diffs; assert_cols; ColR|split].

  {
  exists A, B, C; split; [apply perp_per_1; assert_diffs; auto|split].

    {
    exists D; split; try apply conga_refl; repeat split;
    try (intro; treat_equalities; apply HNC; assert_cols; Col); exists D; split;
    [unfold Midpoint in *; spliter; auto|right; apply out_trivial].
    intro; treat_equalities; apply HNC; Col.
    }

    {
    intro HCongA; assert (HPer1 : Per A B D)
      by (apply l11_17 with A B C; CongA; apply perp_per_1; assert_diffs; Perp).
    assert (HPer2 : Per C B D).
      {
      apply l11_17 with A B D; auto; apply cong3_conga;
      try (intro; treat_equalities; apply HNC; assert_cols; Col).
      repeat split; try solve[unfold Midpoint in *; spliter; Cong].
      }
    assert (HSumA : SumA A B D C B D A B C).
      {
      exists C; split; [apply conga_pseudo_refl|split;[|apply conga_refl]];
      try solve[intro; treat_equalities; apply HNC; assert_cols; Col].
      apply l9_9; split;
      [intro; treat_equalities; apply HNC; assert_cols; Col|].
      split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
      split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
      exists D; split; Col; unfold Midpoint in *; spliter; auto.
      }
    assert (HC := per2_suma__bet _ _ _ _ _ _ _ _ _ HPer1 HPer2 HSumA);
    apply HNC; assert_cols; Col.
    }
  }

  {
  intros P Q HOut1 HNE1 HPer.
  destruct (segment_construction_2 C B B P) as [P' [H HCong2]];
  [assert_diffs; auto|]. assert (HOut2 : Out B C P')
    by (assert_diffs; repeat (split; auto)); clear H.
  destruct (perp_exists P' B C) as [Q' HPerp2]; [assert_diffs; auto|].
  assert (HPerp3 : Perp B A Q P).
    {
    apply l8_16_2 with B; assert_diffs; Col; Perp.
    apply per_not_col in HPer; auto.
    intro; apply HPer; assert_cols; ColR.
    }
  destruct (HP B A B C P Q P' Q') as [I [HC1 HC2]]; Perp;
  try (intro; apply HNC; assert_diffs; assert_cols; ColR).
  assert (HNE2 : B <> D)
    by (intro; treat_equalities; apply HNC; assert_cols; Col).
  assert (HOS : OS B C P I).
    {
    apply l12_6; apply par_strict_col_par_strict with Q; Col.

      {
      intro; treat_equalities; apply (perp_not_col _ _ _ HPerp1).
      destruct (not_strict_par A B P' Q' P) as [HC3 HC4];
      try apply l12_9 with B C; Perp; try solve[assert_cols; Col].
      assert_diffs; assert_cols; ColR.
      }

      {
      apply par_not_col_strict with P; try apply l12_9 with A B; Perp; Col.
      intro; apply HNC; assert_diffs; assert_cols; ColR.
      }
    }
  exists I; split; Col; apply l6_4_2; split;
  try (intro; apply (l9_9_bis _ _ _ _ HOS)).

    {
    elim (eq_dec_points D I); intro HNE3; treat_equalities; Col.
    destruct HD as [_ HD]; apply perp_perp_col with A C;
    apply perp_bisect_perp; apply cong_perp_bisect;
    try solve[assert_diffs; Cong]. assert (HPerp4 : Perp P I B P).
      {
      apply perp_col0 with A B; try apply perp_col0 with P Q;
      try solve[assert_diffs; assert_cols; Col; Perp].
      intro; treat_equalities; apply HNC.
      assert (H : Par B A P' Q') by (apply l12_9 with B C; Perp).
      destruct (not_strict_par B A P' Q' P);
      assert_diffs; assert_cols; Col; ColR.
      }
    assert (HPerp5 : Perp P' I B P').
      {
      apply perp_col0 with B C; try apply perp_col0 with P' Q';
      try solve[assert_diffs; assert_cols; Col; Perp].
      intro; treat_equalities; apply HNC.
      assert (H : Par B C P Q) by (apply l12_9 with B A; Perp).
      destruct (not_strict_par B C P Q P');
      assert_diffs; assert_cols; Col; ColR.
      }
    destruct (per_lt B P I) as [HLt _];
    try solve[assert_diffs; try apply perp_per_1; Perp].
    destruct (l11_52 I P B I P' B) as [_ [_ HCongA2]]; Cong;
    try (apply l11_16; assert_diffs; try apply perp_per_1; auto);
    [apply lt__le; apply lt_comm; auto|clear HNE3; clear HLt; clear HOS].
    apply cong2_conga_cong with B B; Cong; apply out_conga with P I P' I; auto;
    apply l6_6; auto; apply out_trivial;
    apply perp_not_col in HPerp4; assert_diffs; auto.
    }

    {
    apply l9_8_2 with D; try apply one_side_transitivity with A.

      {
      apply one_side_symmetry in HOS; apply one_side_not_col in HOS.
      assert_diffs; assert_cols; split; auto.
      split; [intro; apply HNC; ColR|split; Col].
      exists B; split; Col.
      }

      {
      assert_diffs; assert_cols; apply l9_19 with C; Col.
      split; [repeat (split; Between)|intro; apply HNC; ColR].
      }

      {
      assert_diffs; assert_cols; apply l9_19 with B; Col.
      }
    }
  }
Qed.

End bachmann_s_lotschnittaxiom_existential_inverse_projection_postulate.