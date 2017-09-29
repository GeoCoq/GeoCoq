Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section bachmann_s_lotschnittaxiom_legendre_s_parallel_postulate.

Context `{T2D:Tarski_2D}.

Lemma bachmann_s_lotschnittaxiom__legendre_s_parallel_postulate :
  bachmann_s_lotschnittaxiom -> legendre_s_parallel_postulate.
Proof.
intro bla.
cut (forall A1 A2 B1 B2 C1 C2 D1 D2,
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        ~ Col A1 A2 D1 -> ~ Col B1 B2 C1 ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).
  {
  clear bla; intro bla.
  cut (exists A B C,
          ~ Col A B C /\ Acute A B C /\
          forall P Q,
            Out B A P -> P <> Q -> Per B P Q ->
            exists Y, Out B C Y /\ Col P Q Y).
    {
    intros [A [B [C [HNC [HAcute HP]]]]]; exists A, B, C; split; try split; Col.
    intros T HInAngle; elim (Col_dec A B T); intro HABT.

      {
      assert (HNC' : ~ Col B C T)
        by (intro; apply HNC; unfold InAngle in *; spliter; ColR).
      destruct (l8_18_existence B C T) as [Y [HC HPerp]]; [auto|exists T, Y].
      assert (HOut : Out B A T).
        {
        apply col_in_angle_out with C; try (intro; apply HNC; assert_cols); Col.
        }
      split; [|split]; Between.
      apply l6_6; apply acute_col_perp__out with T; Col.
      apply acute_conga__acute with A B C; auto.
      apply out213_suma__conga with T B A; try apply l6_6; auto.
      exists C; split; [|split]; try apply col123__nos; Col;
      apply conga_refl; assert_diffs; auto.
      }

      {
      destruct (l8_18_existence A B T) as [X [HC HPerp]]; Col.
      assert (HOut1 : Out B A X).
        {
        apply l6_6; apply acute_col_perp__out with T; Col; Perp.
        apply acute_lea_acute with A B C; auto.
        apply lea_left_comm; apply l11_29_b;
        exists C; split; auto; apply conga_refl; assert_diffs; auto.
        }
      destruct (HP X T) as [Y [HOut2 H]];
      try apply perp_per_1; try solve[assert_diffs; auto];
      try apply perp_sym; try apply perp_col0 with A B;
      try solve[assert_diffs; assert_cols; Col].
      exists X, Y; repeat (split; auto); elim H; clear H; intro H; auto.
      elim (eq_dec_points T Y); intro HTY; treat_equalities; Between.
      assert (HACT : ~ Col B C T).
        {
        intro; apply HTY; apply l6_21 with B C X T; Col;
        try solve[assert_diffs; auto];
        try (intro; apply HNC; assert_diffs; ColR).
        elim H; assert_cols; Col.
        }
      elim H; clear H; intro HBet.

        {
        assert (HOS : OS C B T A)
          by (apply in_angle_one_side; try apply l11_24; Col).
        exfalso; apply (l9_9_bis _ _ _ _ HOS).
        apply l9_2; apply l9_8_2 with X.

          {
          split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
          split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
          exists Y; assert_cols; split; Col; Between.
          }

          {
          apply l9_19 with B; try split; try apply l6_6; assert_diffs;
          assert_cols; Col; intro; apply HNC; ColR.
          }
        }

        {
        assert (HOS : OS A B T C) by (apply in_angle_one_side; Col).
        exfalso; apply (l9_9_bis _ _ _ _ HOS).
        apply l9_2; apply l9_8_2 with Y.

          {
          split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
          split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
          exists X; assert_cols; split; Col; Between.
          }

          {
          apply l9_19 with B; try split; try apply l6_6; assert_diffs;
          assert_cols; Col; intro; apply HNC; ColR.
          }
        }
      }
    }

    {
    destruct lower_dim_ex as [C [E [D H]]].
    assert (HNC : ~ Col C E D) by auto; clear H.
    destruct (l8_18_existence D E C) as [B [HC1 HPerp]]; Col.
    assert (HF : exists F, Col D E F /\ B <> F);
    [|destruct HF as [F [HC2 HNE]]].
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
        try (intro; treat_equalities; apply HNC; assert_cols; Col); exists D;
        split; [unfold Midpoint in *; spliter; auto|right; apply out_trivial].
        intro; treat_equalities; apply HNC; Col.
        }

        {
        intro HCongA; assert (HPer1 : Per A B D).
          {
          apply l11_17 with A B C; CongA; apply perp_per_1; assert_diffs; Perp.
          }
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
          apply l9_9.
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
      destruct (bla B A B C P Q P' Q') as [I [HC1 HC2]]; Perp;
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
        apply cong2_conga_cong with B B; Cong; apply out_conga with P I P' I;
        auto; apply l6_6; auto; apply out_trivial;
        apply perp_not_col in HPerp4; assert_diffs; auto.
        }

        {
        apply l9_8_2 with D; try apply one_side_transitivity with A.

          {
          apply one_side_symmetry in HOS; apply one_side_not_col123 in HOS.
          assert_diffs; assert_cols.
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
    }
  }

  {
  intros A1 A2 B1 B2 C1 C2 D1 D2 HPerpAB HPerpAC HPerpBD HNCol1 HNCol2.
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
Qed.

End bachmann_s_lotschnittaxiom_legendre_s_parallel_postulate.