Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section Euclid_aux_3.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma euclid_5_implies_strong_parallel_postulate_aux_2 :
  euclid_5 ->
  (forall P Q R S T U X: Tpoint,
   BetS P T Q ->
   BetS R T S ->
   ~ Col P R U ->
   Cong P T Q T ->
   Cong R T S T ->
   OS P R S U ->
   OS P S R U ->
   ~ Col P Q S ->
   Col P R X ->
   Col Q U X ->
   exists I : Tpoint, Col S Q I /\ Col P U I).
Proof.
intros HE5 P Q R S T U X HPTQ HRTS HNC HCong1 HCong2 HOS1 HOS2 HPQS H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HRTS.
elim H1; clear H1; intro H1; try (elim H1; clear H1; intro H1).

  {
  elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

    {
    assert (H := inner_pasch P Q X R U); destruct H as [I [HQRI HPUI]]; Between.
    elim (eq_dec_points Q I); intro HQI; elim (eq_dec_points R I); intro HRI; treat_equalities.

      {
      exfalso; assert_cols; Col.
      }

      {
      exists Q; assert_cols; Col.
      }

      {
      exfalso; assert_cols; Col.
      }

      {
      assert (HQIR : BetS Q I R) by (show_distinct Q R; Col; split; Col; Between).
      elim (eq_dec_points P I); intro HPI; treat_equalities.

        {
        exists P; split; Col; spliter; assert_cols; ColR.
        }

        {
        unfold BetS in *; destruct (HE5 P Q R S T I) as [I' [HQSI' HPII']];
        try split; spliter; Col.
        exists I'; unfold BetS in *; spliter; assert_cols; split; ColR.
        }
      }
    }

    {
    apply l9_9_bis in HOS1; exfalso; apply HOS1.
    apply l9_8_2 with Q.

      {
      assert_diffs; spliter; split; Col.
      split; try (intro; apply HPQS; assert_cols; ColR).
      split; Col.
      exists X; split; Col; Between.
      }

      {
      apply l12_6; apply par_strict_symmetry.
      apply par_not_col_strict with P; Col.
      assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    }

    {
    elim (Col_dec Q S U); intro HQSU.

      {
      exists U; Col.
      }

      {
      elim (eq_dec_points Q X); intro HQX; treat_equalities.

        {
        spliter; assert_cols; exists P; split; Col; ColR.
        }

        {
        assert (HQS : Q <> S) by (assert_diffs; Col).
        assert (HQU : Q <> U) by (assert_diffs; Col).
        assert (HTS : TS Q S P U).
          {
          apply l9_8_2 with X.

            {
            spliter; assert_cols.
            split; Col.
            split; try (intro; apply HQSU; ColR).
            split; Col.
            exists Q; Col.
            }

            {
            apply one_side_symmetry; apply l12_6.
            apply par_strict_col_par_strict with R; assert_cols;
            try (intro; treat_equalities); Col.
            apply par_not_col_strict with X; try (intro; apply HQSU; ColR); Col.
            apply l12_17 with T; try split; spliter; Cong; Between.
            }
          }
        destruct HTS as [Hc1 [Hc2 [Hc3 [I [H3 H4]]]]]; assert_cols.
        exists I; Col.
        }
      }
    }
  }

  {
  elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

    {
    assert (H := outer_pasch R Q X P U); destruct H as [I [HQRI HPUI]]; Between.
    elim (eq_dec_points Q I); intro HQI; elim (eq_dec_points R I); intro HRI; treat_equalities.

      {
      exfalso; assert_cols; Col.
      }

      {
      exists Q; assert_cols; Col.
      }

      {
      exfalso; assert_cols; Col.
      }

      {
      assert (HQIR : BetS Q I R) by (show_distinct Q R; Col; split; Col; Between).
      elim (eq_dec_points P I); intro HPI; treat_equalities.

        {
        exists P; split; Col; spliter; assert_cols; ColR.
        }

        {
        unfold BetS in *;
        destruct (HE5 P Q R S T I) as [I' [HQSI' HPII']]; try split; spliter; Col.
        unfold BetS in *; exists I'; spliter; assert_cols; split; ColR.
        }
      }
    }

    {
    apply l9_9_bis in HOS1; exfalso; apply HOS1.
    apply l9_8_2 with Q.

      {
      assert_diffs; spliter; split; Col.
      split; try (intro; apply HPQS; assert_cols; ColR).
      split; Col.
      exists X; split; Col; Between.
      }

      {
      apply l12_6; apply par_strict_symmetry.
      apply par_not_col_strict with P; Col.
      assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    }

    {
    elim (Col_dec Q S U); intro HQSU.

      {
      exists U; Col.
      }

      {
      elim (eq_dec_points Q X); intro HQX; treat_equalities.

        {
        spliter; assert_cols; exists P; split; Col; ColR.
        }

        {
        elim (eq_dec_points P X); intro HPX; treat_equalities.

          {
          exists Q; assert_cols; Col.
          }

          {
          assert (HQS : Q <> S) by (assert_diffs; Col).
          assert (HQU : Q <> U) by (assert_diffs; Col).
          assert (HTS : TS Q S P U).
            {
            apply l9_8_2 with X.

              {
              spliter; assert_cols.
              split; Col.
              split; try (intro; apply HQSU; ColR).
              split; Col.
              exists Q; Col.
              }

              {
              apply one_side_symmetry; apply l12_6.
              apply par_strict_col_par_strict with R; Col.
              apply par_not_col_strict with X; try (intro; apply HQSU; assert_cols; ColR); Col.
              apply l12_17 with T; try split; spliter; Cong; Between.
              }
            }
          destruct HTS as [Hc1 [Hc2 [Hc3 [I [H3 H4]]]]]; assert_cols.
          exists I; Col.
          }
        }
      }
    }
  }

  {
  elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

    {
    elim (eq_dec_points P X); intro HPX; treat_equalities.

      {
      exists Q; assert_cols; Col.
      }

      {
      assert (HTS : TS P S Q X).
        {
        apply l9_8_2 with R.

          {
          assert_diffs; split; Col.
          spliter; split; try (intro; apply HPQS; assert_cols; ColR).
          split; try (intro; apply HPQS; assert_cols; ColR).
          exists P; split; Col; Between.
          }

          {
          apply l12_6.
          apply par_not_col_strict with Q; try (intro; apply HQSU; assert_cols; ColR); Col.
          apply par_left_comm; assert_diffs.
          apply l12_17 with T; try split; spliter; Cong; Between.
          }
        }
      destruct HTS as [Hc1 [Hc2 [Hc3 [I' [HPSI' HQXI']]]]]; clear Hc1; clear Hc2; clear Hc3.
      assert (H := l5_3 Q U I' X); elim H; clear H; Col; intro HQUI'.

        {
        assert (HTS : TS Q X P S).
          {
          apply l9_31.

            {
            exists R; split.

              {
              spliter; split; Col.
              show_distinct Q X; Col.
              split; try (intro; apply HPQS; assert_cols; ColR).
              split; try (intro; apply HPQS; assert_cols; ColR).
              exists P; Col.
              }

              {
              spliter; split; Col.
              split; Col.
              split; try (intro; apply HPQS; assert_cols; ColR).
              exists T; assert_cols; split; Col; Between.
              }
            }

            {
            apply l12_6; apply par_strict_right_comm;
            apply par_strict_col_par_strict with R; assert_cols; Col.
            apply par_not_col_strict with P; try (intro; apply HQSU; assert_cols; ColR); Col.
            apply l12_17 with T; try split;
            spliter; assert_diffs; Cong; Between.
            }
          }
        destruct HTS as [Hc1 [Hc2 [Hc3 [I'' [HQXI'' HPSI'']]]]]; clear Hc1; clear Hc2; clear Hc3.
        assert (I' = I''); treat_equalities.
          {
          apply l6_21 with P S Q X; Col; intro; treat_equalities; assert_cols; Col.
          }
        assert (H := outer_pasch S Q I' P U); destruct H as [I [HQSI HPUI]]; Between.
        exists I; assert_cols; Col.
        }

        {
        elim (Col_dec P S U); intro HPQU.

          {
          exists S; Col.
          }

          {
          apply l9_9_bis in HOS2; exfalso; apply HOS2.
          apply l9_8_2 with Q.

            {
            spliter; assert_diffs; split; Col.
            split; Col.
            split; Col.
            exists I'; Col.
            }

            {
            apply l12_6.
            apply par_not_col_strict with Q; try (intro; apply HQSU; assert_cols; ColR); Col.
            apply l12_17 with T; try split;
            spliter; assert_diffs; Cong; Between.
            }
          }
        }
      }
    }

    {
    assert (H := outer_pasch Q R X U P); destruct H as [I [HQRI HPUI]]; Between.
    elim (eq_dec_points Q I); intro HQI; elim (eq_dec_points R I); intro HRI; treat_equalities.

      {
      exfalso; assert_cols; Col.
      }

      {
      exists Q; assert_cols; Col.
      }

      {
      exfalso; assert_cols; Col.
      }

      {
      assert (HQIR : BetS Q I R) by (show_distinct Q R; Col; split; Col).
      elim (eq_dec_points P I); intro HPI; treat_equalities.

        {
        exists P; split; Col; spliter; assert_cols; ColR.
        }

        {
        destruct (HE5 P Q R S T I) as [I' [HQSI' HPII']]; try split; spliter; Col.
        unfold BetS in *; exists I'; spliter; assert_cols; split; ColR.
        }
      }
    }

    {
    assert (H := inner_pasch R U X P Q); destruct H as [I [HPUI HQRI]]; Between.
    elim (eq_dec_points Q I); intro HQI; elim (eq_dec_points R I); intro HRI; treat_equalities.

      {
      exfalso; assert_cols; Col.
      }

      {
      exists Q; assert_cols; Col.
      }

      {
      exfalso; assert_cols; Col.
      }

      {
      assert (HQIR : BetS Q I R) by (show_distinct Q R; Col; split; Col; Between).
      elim (eq_dec_points P I); intro HPI; treat_equalities.

        {
        exists P; split; Col; spliter; assert_cols; ColR.
        }

        {
        destruct (HE5 P Q R S T I) as [I' [HQSI' HPII']]; try split; spliter; Col.
        unfold BetS in *; exists I'; spliter; assert_cols; split; ColR.
        }
      }
    }
  }
Qed.

Lemma euclid_5_implies_strong_parallel_postulate_aux_3 :
  euclid_5 ->
  (forall P Q R S T U X: Tpoint,
   BetS P T Q ->
   BetS R T S ->
   ~ Col P R U ->
   Cong P T Q T ->
   Cong R T S T ->
   OS P R S U ->
   OS P S R U ->
   ~ Col P Q S ->
   Col P U X ->
   Col Q R X ->
   exists I : Tpoint, Col S Q I /\ Col P U I).
Proof.
intros HE5 P Q R S T U X HPTQ HRTS HNC HCong1 HCong2 HOS1 HOS2 HPQS H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HRTS.
elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

  {
  elim H1; clear H1; intro H1; try (elim H1; clear H1; intro H1).

    {
    apply l9_9_bis in HOS1; exfalso; apply HOS1.
    apply l9_8_2 with Q.

      {
      apply l9_2; apply l9_8_2 with X.

        {
        assert_diffs; spliter; split; Col.
        show_distinct P X; Col; split; try (intro; apply HNC; assert_cols; ColR).
        split; try (intro; apply HPQS; assert_cols; ColR).
        exists R; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H3 : P <> R) by (assert_diffs; Col).
        assert (H4 : Col P R P) by Col.
        assert (H5 : Col U X P) by (assert_cols; Col).
        assert (H := l9_19 P R U X P H3 H4 H5); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities); Between.
        }
      }

      {
      apply l12_6; apply par_strict_symmetry.
      apply par_not_col_strict with P; Col.
      assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    }

    {
    apply l9_9_bis in HOS1; exfalso; apply HOS1.
    apply l9_8_2 with Q.

      {
      apply l9_2; apply l9_8_2 with X.

        {
        assert_diffs; spliter; split; Col.
        show_distinct P X; assert_cols; try (apply HPQS; ColR);
        split; try (intro; apply HNC; ColR).
        split; try (intro; apply HPQS; assert_cols; ColR).
        exists R; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H3 : P <> R) by (assert_diffs; Col).
        assert (H4 : Col P R P) by Col.
        assert (H5 : Col U X P) by (assert_cols; Col).
        assert (H := l9_19 P R U X P H3 H4 H5); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; Between.
        intro; treat_equalities; apply HPQS; spliter; assert_cols; ColR.
        }
      }

      {
      apply l12_6; apply par_strict_symmetry.
      apply par_not_col_strict with P; Col.
      assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    }

    {
    elim (Col_dec P S U); intro HPSU.

      {
      exists S; Col.
      }

      {
      apply l9_9_bis in HOS2; exfalso; apply HOS2.
      apply l9_8_2 with X.

        {
        spliter; assert_diffs; split; Col.
        show_distinct P X; try (assert_cols; apply HPQS; ColR).
        split; try (intro; assert_cols; apply HPSU; ColR).
        split; Col.
        exists P; Col.
        }

        {
        apply l12_6.
        apply par_strict_right_comm.
        apply par_strict_col_par_strict with Q; try (intro; treat_equalities; assert_cols); Col.
        apply par_strict_right_comm.
        apply par_not_col_strict with Q; Col.
        apply l12_17 with T; try split; spliter; assert_diffs; Cong; Between.
        }
      }
    }
  }

  {
  elim (eq_dec_points Q X); intro HQX; elim (eq_dec_points R X); intro HRX; treat_equalities.

    {
    exfalso; assert_cols; Col.
    }

    {
    exists Q; assert_cols; Col.
    }

    {
    exfalso; assert_cols; Col.
    }

    {
    assert (HQIR : BetS Q X R) by (show_distinct Q R; Col; split; Col; Between).
    unfold BetS in *;
    destruct (HE5 P Q R S T X) as [I [HQSI HPII]]; try split; spliter; Col.
    unfold BetS in *; exists I; spliter; assert_cols; split; ColR.
    }
  }

  {
  elim (Col_dec Q S U); intro HQSU.

    {
    exists U; Col.
    }

    {
    elim (Col_dec Q S R); intro HQSR.

      {
      exists P; spliter; assert_cols; split; Col; ColR.
      }

      {
      elim (Col_dec Q S X); intro HQSX.

        {
        exists X; assert_cols; Col.
        }

        {
        assert (HPX : P <> X).
          {
          intro; treat_equalities; apply HQSR; spliter; assert_cols; ColR.
          }
        assert (HQR : Q <> R) by (assert_diffs; Col).
        assert (HQS : Q <> S) by (assert_diffs; Col).
        assert (HRS : R <> S) by (assert_diffs; Col).
        assert (HTS : TS Q S P X).
          {
          apply l9_8_2 with R.

            {
            spliter; assert_cols.
            split; Col.
            split; Col.
            split; Col.
            exists Q; split; Col; Between.
            }

            {
            apply one_side_symmetry; apply l12_6.
            apply par_not_col_strict with R; Col.
            apply l12_17 with T; try split; spliter; Cong; Between.
            }
          }
        destruct HTS as [Hc1 [Hc2 [Hc3 [I [H3 H4]]]]]; assert_cols.
        exists I; split; ColR.
        }
      }
    }
  }
Qed.

Lemma euclid_5_both_sides_3_1 :
  euclid_5 ->
  (forall P Q Q' R R' S T T' X,
   Cong P T Q T ->
   Cong P T' Q' T' ->
   Cong R T S T ->
   Cong R' T' S T' ->
   Cong Q S Q' S ->
   BetS P T Q ->
   BetS P T' Q' ->
   BetS R T S ->
   BetS R' T' S ->
   BetS Q S Q' ->
   ~ Col P Q S ->
   ~ Col P Q' S ->
   ~ Col P R R' ->
   Col P R' X ->
   Bet S R X ->
   False).
Proof.
intros HE5 P Q Q' R R' S T T' X Hcong1 HCong2 HCong3 HCong4 HCong5;
intros HPTQ HPT'Q' HRTS HR'T'S HQSQ' HPQS HPQ'S HPRR' H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HPT'Q'; apply BetSEq in HRTS;
apply BetSEq in HR'T'S; apply BetSEq in HQSQ'.
assert (HTS : TS P S R R').
  {
  apply l9_8_2 with T.

    {
    apply l9_2; apply l9_8_2 with T'.

      {
      apply l9_8_2 with Q'.

        {
        apply l9_2; apply l9_8_2 with Q.

          {
          assert_diffs; split; Col.
          split; Col.
          split; Col.
          exists S; spliter; Col.
          }

          {
          assert (H3 : P <> S) by (assert_diffs; Col).
          assert (H4 : Col P S P) by Col.
          assert (H5 : Col Q T P) by (spliter; assert_cols; Col).
          assert (H := l9_19 P S Q T P H3 H4 H5); rewrite H.
          split; Col.
          spliter; split; Col.
          }
        }

        {
        assert (H3 : P <> S) by (assert_diffs; Col).
        assert (H4 : Col P S P) by Col.
        assert (H5 : Col Q' T' P) by (spliter; assert_cols; Col).
        assert (H := l9_19 P S Q' T' P H3 H4 H5); rewrite H.
        split; Col.
        spliter; split; Col.
        }
      }

      {
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S S) by Col.
      assert (H5 : Col T' R' S) by (spliter; assert_cols; Col).
      assert (H := l9_19 P S T' R' S H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQ'S; assert_cols; ColR).
      split; Col.
      split; try (intro; treat_equalities); Between.
      }
    }

    {
    assert (H3 : P <> S) by (assert_diffs; Col).
    assert (H4 : Col P S S) by Col.
    assert (H5 : Col T R S) by (spliter; assert_cols; Col).
    assert (H := l9_19 P S T R S H3 H4 H5); rewrite H.
    spliter; split; try (intro; apply HPQS; assert_cols; ColR).
    split; Col.
    split; try (intro; treat_equalities); Between.
    }
  }
elim (eq_dec_points R' X); intro HRX; treat_equalities.

  {
  apply l9_9 in HTS; apply HTS.
  assert (H3 : P <> S) by (assert_diffs; Col).
  assert (H4 : Col P S S) by Col.
  assert (H5 : Col R R' S) by (assert_cols; Col).
  assert (H := l9_19 P S R R' S H3 H4 H5); rewrite H.
  spliter; split; try (intro; apply HPQS; assert_cols; ColR).
  split; try (intro; treat_equalities; Col).
  split; try (intro; treat_equalities; Col).
  Between.
  }

  {
  elim H1; clear H1; intro H1; try (elim H1; clear H1; intro H1).

    {
    apply l9_9 in HTS; apply HTS; apply one_side_transitivity with X.

      {
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S S) by Col.
      assert (H5 : Col R X S) by (assert_cols; Col).
      assert (H := l9_19 P S R X S H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQ'S; assert_cols; ColR).
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S P) by Col.
      assert (H5 : Col R' X P) by (assert_cols; Col).
      assert (H := l9_19 P S R' X P H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQS; assert_cols; ColR).
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; apply HPQ'S; assert_cols; ColR).
      Between.
      }
    }

    {
    apply l9_9 in HTS; apply HTS; apply one_side_transitivity with X.

      {
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S S) by Col.
      assert (H5 : Col R X S) by (assert_cols; Col).
      assert (H := l9_19 P S R X S H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQ'S; assert_cols; ColR).
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S P) by Col.
      assert (H5 : Col R' X P) by (assert_cols; Col).
      assert (H := l9_19 P S R' X P H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQS; assert_cols; ColR).
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; apply HPQ'S; assert_cols; ColR).
      Between.
      }
    }

    {
    assert (H : TS R R' P S).
      {
      apply l9_8_2 with X.

        {
        assert_diffs; split; Col.
        split; try (intro; apply HPRR'; assert_cols; ColR).
        split; try (intro; spliter; assert_cols; apply HPRR'; ColR).
        exists R; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H3 : R <> R') by (assert_diffs; Col).
        assert (H4 : Col R R' R') by Col.
        assert (H5 : Col P X R') by (assert_cols; Col).
        assert (H := l9_19 R R' P X R' H3 H4 H5); rewrite H.
        split; Col.
        assert_diffs; split; Between.
        }
      }
    clear H1; clear H2; clear HRX; clear X.
    destruct H as [Hc1 [Hc2 [Hc3 [X [HRR'X HPSX]]]]]; clear Hc1; clear Hc2; clear Hc3.
    elim HRR'X; clear HRR'X; intro HRR'X; try (elim HRR'X; clear HRR'X; intro HRR'X).

      {
      apply l9_9 in HTS; apply HTS.
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S X) by (assert_cols; Col).
      assert (H5 : Col R R' X) by (assert_cols; Col).
      assert (H := l9_19 P S R R' X H3 H4 H5); rewrite H.
      spliter; split; try (intro; assert_cols; apply HPQS; ColR).
      split; try (intro; treat_equalities; assert_cols; apply HPQS; ColR).
      split; try (intro; treat_equalities; assert_cols; apply HPQS; ColR).
      Between.
      }

      {
      apply l9_9 in HTS; apply HTS.
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S X) by (assert_cols; Col).
      assert (H5 : Col R R' X) by (assert_cols; Col).
      assert (H := l9_19 P S R R' X H3 H4 H5); rewrite H.
      spliter; split; try (intro; assert_cols; apply HPQS; ColR).
      split; try (intro; treat_equalities; assert_cols; apply HPQS; ColR).
      split; try (intro; treat_equalities; assert_cols; apply HPQS; ColR).
      Between.
      }

      {
      clear HTS; elim (eq_dec_points S X); intro HSX; treat_equalities.

        {
        elim (Col_dec Q R R'); intro HQRR'.

          {
          apply HPQS; spliter; assert_diffs; assert_cols; ColR.
          }

          {
          assert (HTS : TS R R' Q Q').
            {
            assert_diffs; split; Col.
            split; Col.
            spliter; assert_cols; split; try (intro; apply HQRR'; ColR).
            exists S; Col.
            }
          apply l9_9 in HTS; apply HTS; exists P; split.

            {
            assert_diffs; split; Col.
            split; Col.
            split; Col.
            exists T; spliter; assert_cols; split; Between; ColR.
            }

            {
            assert_diffs; split; Col.
            spliter; assert_cols; split; try (intro; apply HQRR'; ColR).
            split; Col.
            exists T'; split; Between; ColR.
            }
          }
        }

        {
        assert (HSXP : BetS S X P).
          {
          split; Between.
          split; intro; treat_equalities; assert_cols; Col.
          }
        assert (HQRXS : ~ Col Q R S).
          {
          intro; spliter; assert_cols; apply HPQS; ColR.
          }
        assert (HQ'R'XS : ~ Col Q' R' S).
          {
          intro; spliter; assert_cols; apply HPQ'S; ColR.
          }
        destruct (HE5 R S P Q T X) as [I1 [HQSI1 HRXI1]];
        unfold BetS in *; try split; spliter; Col; Cong.
        destruct (HE5 R' S P Q' T' X) as [I2 [HQ'SI2 HR'XI2]]; try split; Col; Cong.
        assert (HQRS : ~ Col Q R S).
          {
          intro; spliter; assert_cols; apply HPQS; ColR.
          }
        unfold BetS in *.
        assert (HCol1 : Col Q I1 I2) by (spliter; assert_cols; ColR).
        assert (HCol2 : Col R I1 I2) by (spliter; assert_cols; ColR).
        assert (HCol3 : Col S I1 I2) by (spliter; assert_cols; ColR).
        assert (HDiff : I1 <> I2).
          {
          spliter; elim (l5_2 Q S Q' I1); elim (l5_2 Q' S Q I2); Between; intros;
          assert (Bet I1 S I2) by (assert_diffs; eBetween); intro; treat_equalities; Col.
          }
        apply HQRS; ColR.
        }
      }
    }
  }
Qed.

Lemma euclid_5_both_sides_3_2 :
  euclid_5 ->
  (forall P Q Q' R R' S T T' X,
   Cong P T Q T ->
   Cong P T' Q' T' ->
   Cong R T S T ->
   Cong R' T' S T' ->
   Cong Q S Q' S ->
   BetS P T Q ->
   BetS P T' Q' ->
   BetS R T S ->
   BetS R' T' S ->
   BetS Q S Q' ->
   ~ Col P Q S ->
   ~ Col P Q' S ->
   ~ Col P R R' ->
   Col P R' X ->
   Bet R X S ->
   False).
Proof.
intros HE5 P Q Q' R R' S T T' X Hcong1 HCong2 HCong3 HCong4 HCong5;
intros HPTQ HPT'Q' HRTS HR'T'S HQSQ' HPQS HPQ'S HPRR' H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HPT'Q'; apply BetSEq in HRTS;
apply BetSEq in HR'T'S; apply BetSEq in HQSQ'.
assert (H := l5_3 R T X S); elim H; clear H; try intro HRTX; Col.

  {
  assert (H := outer_pasch Q S T P X); destruct H as [I [HPXI HQSI]];
  spliter; eBetween.
  elim (eq_dec_points P X); intro HPX; treat_equalities.

    {
    apply HPQS; assert_cols; ColR.
    }

    {
    assert (HPar : Par_strict Q' S P R').
      {
      apply par_not_col_strict with P; Col.
      assert (HI := mid_plgs Q' S P R' T'); destruct HI as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; apply HFalse.
    exists I; assert_cols; split; ColR.
    }
  }

  {
  assert (H := outer_pasch Q R T P X); destruct H as [U [HQRU HPXU]];
  spliter; Between.
  assert (HPar : Par_strict Q' S P R').
    {
    apply par_not_col_strict with P; Col.
    assert (HI := mid_plgs Q' S P R' T'); destruct HI as [Hc1 [Hc2 HCong6]];
    try (split); Cong; Col; try (spliter; Between).
    }
  elim (eq_dec_points P X); intro HPX; treat_equalities.

    {
    apply HPQS; assert_cols; ColR.
    }

    {
    destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; clear Hc1; clear Hc2; clear Hc3.
    assert (HQUR' : BetS Q U R).
      {
      split; Col.
      split; try (intro; treat_equalities; apply HFalse; exists Q; assert_cols; split; ColR).
      intro; treat_equalities; assert_cols; apply HPRR'; ColR.
      }
    assert (HI := HE5 P Q R S T U). destruct HI as [I [HQSI HPUI]]; Col; try split; Cong.
    unfold BetS in *; apply HFalse; exists I; spliter; assert_cols; split; ColR.
    }
  }

  {
  spliter; Col.
  }
Qed.

Lemma euclid_5_both_sides_3_3 :
  euclid_5 ->
  (forall P Q Q' R R' S T T' X,
   Cong P T Q T ->
   Cong P T' Q' T' ->
   Cong R T S T ->
   Cong R' T' S T' ->
   Cong Q S Q' S ->
   BetS P T Q ->
   BetS P T' Q' ->
   BetS R T S ->
   BetS R' T' S ->
   BetS Q S Q' ->
   ~ Col P Q S ->
   ~ Col P Q' S ->
   ~ Col P R R' ->
   Col P R' X ->
   Bet X S R ->
   False).
Proof.
intros HE5 P Q Q' R R' S T T' X Hcong1 HCong2 HCong3 HCong4 HCong5;
intros HPTQ HPT'Q' HRTS HR'T'S HQSQ' HPQS HPQ'S HPRR' H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HPT'Q'; apply BetSEq in HRTS;
apply BetSEq in HR'T'S; apply BetSEq in HQSQ'.
elim (eq_dec_points S X); intro HSX; treat_equalities.

  {
  apply HPQS; spliter; assert_cols; ColR.
  }

  {
  elim (eq_dec_points P X); intro HPX; treat_equalities.

    {
    apply HPQ'S; spliter; assert_cols; ColR.
    }

    {
    assert (HTS : TS Q' S P X).
      {
      apply l9_8_2 with R.

        {
        spliter; split; Col.
        split; try (intro; apply HPQ'S; assert_cols; ColR).
        split; try (intro; apply HPQS; assert_cols; ColR).
        exists S; split; Col; Between.
        }

        {
        apply l12_6; apply par_not_col_strict with P; Col.
        apply par_comm; apply par_symmetry; apply par_col_par with Q;
        spliter; assert_cols; Col.
        assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
        try (split); Cong; Col; try (spliter; Between); Par.
        }
      }
    assert (HPar : Par_strict Q' S P R').
      {
      apply par_not_col_strict with P; Col.
      assert (HI := mid_plgs Q' S P R' T'); destruct HI as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; clear Hc1; clear Hc2; clear Hc3.
    destruct HTS as [Hc1 [Hc2 [Hc3 [I [HQ'SI HPXI]]]]]; clear Hc1; clear Hc2; clear Hc3.
    apply HFalse; exists I; assert_cols; split; ColR.
    }
  }
Qed.

End Euclid_aux_3.
