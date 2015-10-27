Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section Euclid_aux_2.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma euclid_5_implies_strong_parallel_postulate_aux_1_2 :
  euclid_5 ->
  (forall P Q R S T U X : Tpoint,
   BetS P T Q ->
   BetS R T S ->
   ~ Col P R U ->
   Cong P T Q T ->
   Cong R T S T ->
   one_side P R S U ->
   one_side P S R U ->
   ~ Col P Q S ->
   Bet Q X P ->
   Col R U X ->
   exists I : Tpoint, Col S Q I /\ Col P U I).
Proof.
intros HE5 P Q R S T U X HPTQ HRTS HNC HCong1 HCong2 HOS1 HOS2 HPQS H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HRTS.
elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

  {
  assert (H := outer_pasch Q R X P U H1 H2); destruct H as [I [HQRI HPUI]].
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
      apply BetSEq in HPTQ; apply BetSEq in HRTS.
      assert (H := HE5 P Q R S T I); destruct H as [I' [HQSI' HPII']]; Col.
      apply BetSEq in HQSI'; apply BetSEq in HPII'.
      exists I'; spliter; assert_cols; split; ColR.
      }
    }
  }

  {
  elim (Col_dec Q S U); intro HQSU.

    {
    exists U; Col.
    }

    {
    assert (H := l5_3 P T X Q); spliter;
    elim H; Between; clear H; try intro HPTX.

      {
      assert (H := outer_pasch S Q T R X); destruct H as [I' [HQSI' HRXI']]; eBetween.
      assert (HRX : R <> X) by (intro; treat_equalities; apply HPQS; assert_cols; ColR).
      assert (H := l5_2 R X U I'); elim H; Between; clear H; intro HXUI'.

        {
        assert (H := outer_pasch Q I' X P U); destruct H as [I [HQII' HPUI]]; Between.
        assert (HQSI : Bet Q I S) by eBetween.
        exists I; assert_cols; Col.
        }

        {
        assert (HTS : two_sides Q S P U).
          {
          elim (eq_dec_points Q X); intro HQX; treat_equalities.

            {
            apply l9_8_2 with R.

              {
              assert_diffs; split; Col.
              split; try (intro; apply HPQS; assert_cols; ColR).
              split; Col.
              exists Q; split; Col; Between.
              }

              {
              apply one_side_symmetry.
              apply l12_6.
              apply par_not_col_strict with P; Col.
              assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
              try (split); Cong; Col; try (spliter; Between).
              }
            }

            {
            apply l9_8_2 with X.

              {
              assert_diffs; split; Col.
              split; try (intro; apply HPQS; assert_cols; ColR).
              split; Col.
              exists I'; assert_cols; Col.
              }

              {
              apply one_side_symmetry.
              assert (HH3 : Q <> S) by (assert_diffs; Col).
              assert (HH4 : Col Q S Q) by Col.
              assert (HH5 : Col P X Q) by (assert_cols; Col).
              assert (HH := l9_19 Q S P X Q HH3 HH4 HH5); rewrite HH.
              split; Col.
              split; Col.
              }
            }
          }
        destruct HTS as [Hc1 [Hc2 [Hc3 [I [HH3 HH4]]]]]; assert_cols.
        exists I; Col.
        }
      }

      {
      assert (H := outer_pasch S P T R X); destruct H as [I' [HPSI' HRXI']]; Between.
      assert (HRX : R <> X) by (intro; treat_equalities; apply HPQS; assert_cols; ColR).
      assert (H := l5_2 R X U I'); elim H; clear H; Between; intro HXUI'.

        {
        assert (HRUI' : Bet R U I') by eBetween.
        assert (H := outer_pasch S R I' P U). destruct H as [I'' [HRSI'' HPUI'']]; Between.
        assert (H := l5_3 R T I'' S); elim H; Between; clear H; intro HRTI''.

          {
          assert (H := outer_pasch Q S T P I''); destruct H as [I [HQSI HPI''I]]; eBetween.
          show_distinct P I''; Col.
          exists I; assert_cols; split; ColR.
          }

          {
          elim (eq_dec_points T I''); intro HTI''; treat_equalities.

            {
            exists Q; assert_cols; split; Col; ColR.
            }

            {
            assert (H := outer_pasch Q R T P I''); destruct H as [U' [HQRU HPI''U]]; eBetween.
            assert (HQIR : BetS Q U' R).
              {
              split; Col.
              split; try (intro; treat_equalities; apply HTI''; apply l6_21 with P Q S R; Col).
              elim (eq_dec_points U' I''); intro; treat_equalities.

                {
                intro; treat_equalities; assert_cols; Col.
                }

                {
                intro; treat_equalities; apply HPQS; assert_cols; ColR.
                }
              }
            assert (H := HE5 P Q R S T U'); destruct H as [I [HQSI HPUI]]; Col; try split; Col.
            show_distinct P I''; Col.
            unfold BetS in *; exists I; spliter; assert_cols; split; ColR.
            }
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
            assert_diffs; split; Col.
            show_distinct P X; assert_cols; Col.
            split; try (intro; assert_cols; apply HPQS; ColR).
            split; Col.
            exists I'; Col.
            }

            {
            apply one_side_transitivity with Q.

              {
              apply one_side_symmetry.
              assert (HH3 : P <> S) by (assert_diffs; Col).
              assert (HH4 : Col P S P) by Col.
              assert (HH5 : Col Q X P) by (assert_cols; Col).
              assert (HH := l9_19 P S Q X P HH3 HH4 HH5); rewrite HH.
              split; Col.
              split; Col.
              split; try (intro; treat_equalities; assert_cols; Col).
              Between.
              }

              {
              apply l12_6.
              apply par_not_col_strict with Q; Col.
              assert (HI := mid_plgs P S Q R T); destruct HI as [Hc1 [Hc2 HCong6]];
              try (split); Cong; Col; try (spliter; Between).
              }
            }
          }
        }
      }
    }
  }

  {
  apply l9_9_bis in HOS1; exfalso; apply HOS1.
  apply l9_8_2 with Q.

    {
    apply l9_8_2 with X.

      {
      assert_diffs; spliter; split; Col.
      show_distinct P X; Col; split; try (intro; assert_cols; apply HPQS; ColR).
      split; try (intro; assert_cols; apply HNC; ColR).
      exists R; Col.
      }

      {
      apply one_side_symmetry.
      assert (H3 : P <> R) by (assert_diffs; Col).
      assert (H4 : Col P R P) by Col.
      assert (H5 : Col Q X P) by (assert_cols; Col).
      assert (H := l9_19 P R Q X P H3 H4 H5); rewrite H.
      assert_diffs; spliter; split;
      try (intro; assert_cols; apply HPQS; ColR).
      split; Col.
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
Qed.

Lemma euclid_5_both_sides_2_1 :
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
   Col P R X ->
   Bet S R' X ->
   False).
Proof.
intros HE5 P Q Q' R R' S T T' X Hcong1 HCong2 HCong3 HCong4 HCong5;
intros HPTQ HPT'Q' HRTS HR'T'S HQSQ' HPQS HPQ'S HPRR' H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HPT'Q'; apply BetSEq in HRTS;
apply BetSEq in HR'T'S; apply BetSEq in HQSQ'.
assert (HTS : two_sides P S R R').
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
elim (eq_dec_points R X); intro HRX; treat_equalities.

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
      assert (H4 : Col P S P) by Col.
      assert (H5 : Col R X P) by (assert_cols; Col).
      assert (H := l9_19 P S R X P H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQS; assert_cols; ColR).
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; apply HPQ'S; assert_cols; ColR).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S S) by Col.
      assert (H5 : Col R' X S) by (assert_cols; Col).
      assert (H := l9_19 P S R' X S H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQ'S; assert_cols; ColR).
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }

    {
    apply l9_9 in HTS; apply HTS; apply one_side_transitivity with X.

      {
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S P) by Col.
      assert (H5 : Col R X P) by (assert_cols; Col).
      assert (H := l9_19 P S R X P H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQS; assert_cols; ColR).
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; apply HPQ'S; assert_cols; ColR).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S S) by Col.
      assert (H5 : Col R' X S) by (assert_cols; Col).
      assert (H := l9_19 P S R' X S H3 H4 H5); rewrite H.
      spliter; split; try (intro; apply HPQ'S; assert_cols; ColR).
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }

    {
    assert (H : two_sides R R' P S).
      {
      apply l9_8_2 with X.

        {
        assert_diffs; split; Col.
        split; try (intro; apply HPRR'; assert_cols; ColR).
        split; try (intro; spliter; assert_cols; apply HPRR'; ColR).
        exists R'; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H3 : R <> R') by (assert_diffs; Col).
        assert (H4 : Col R R' R) by Col.
        assert (H5 : Col P X R) by (assert_cols; Col).
        assert (H := l9_19 R R' P X R H3 H4 H5); rewrite H.
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
          assert (HTS : two_sides R R' Q Q').
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
        apply BetSEq in HPTQ; apply BetSEq in HPT'Q';
        apply BetSEq in HRTS; apply BetSEq in HR'T'S;
        destruct (HE5 R S P Q T X) as [I1 [HQSI1 HRXI1]]; Col; Cong.
        destruct (HE5 R' S P Q' T' X) as [I2 [HQ'SI2 HR'XI2]]; Col; Cong.
        apply BetSEq in HPTQ; apply BetSEq in HPT'Q';
        apply BetSEq in HRTS; apply BetSEq in HR'T'S;
        apply BetSEq in HQSI1; apply BetSEq in HRXI1;
        apply BetSEq in HQ'SI2; apply BetSEq in HR'XI2;
        assert (HQRS : ~ Col Q R S).
          {
          intro; spliter; assert_cols; apply HPQS; ColR.
          }
        assert (HCol1 : Col Q I1 I2) by (spliter; assert_cols; ColR).
        assert (HCol2 : Col R I1 I2) by (spliter; assert_cols; ColR).
        assert (HCol3 : Col S I1 I2) by (spliter; assert_cols; ColR).
        assert (HDiff : I1 <> I2).
          {
          assert (H1 := l5_2 Q S Q' I1); assert (H2 := l5_2 Q' S Q I2).
          spliter; elim H1; clear H1; elim H2; clear H2; Between; intros H1 H2;
          assert (Bet I1 S I2) by (assert_diffs; eBetween); intro; treat_equalities; Col.
          }
        apply HQRS; ColR.
        }
      }
    }
  }
Qed.

Lemma euclid_5_both_sides_2_2 :
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
   Col P R X ->
   Bet R' X S ->
   False).
Proof.
intros HE5 P Q Q' R R' S T T' X Hcong1 HCong2 HCong3 HCong4 HCong5;
intros HPTQ HPT'Q' HRTS HR'T'S HQSQ' HPQS HPQ'S HPRR' H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HPT'Q'; apply BetSEq in HRTS;
apply BetSEq in HR'T'S; apply BetSEq in HQSQ'.
assert (H := l5_3 R' T' X S); elim H; clear H; try intro HR'T'X; Col.

  {
  assert (H := outer_pasch Q' S T' P X); destruct H as [I [HPXI HQ'SI]];
  spliter; eBetween.
  elim (eq_dec_points P X); intro HPX; treat_equalities.

    {
    apply HPQS; assert_cols; ColR.
    }

    {
    assert (HPar : Par_strict Q S P R).
      {
      apply par_not_col_strict with P; Col.
      assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; apply HFalse.
    exists I; assert_cols; split; ColR.
    }
  }

  {
  assert (H := outer_pasch Q' R' T' P X); destruct H as [U [HQR'U HPXU]];
  spliter; Between.
  assert (HPar : Par_strict Q S P R).
    {
    apply par_not_col_strict with P; Col.
    assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
    try (split); Cong; Col; try (spliter; Between).
    }
  elim (eq_dec_points P X); intro HPX; treat_equalities.

    {
    apply HPQS; assert_cols; ColR.
    }

    {
    destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; clear Hc1; clear Hc2; clear Hc3.
    assert (HQ'UR' : BetS Q' U R').
      {
      split; Col.
      split; try (intro; treat_equalities; apply HFalse; exists Q'; assert_cols; split; ColR).
      intro; treat_equalities; assert_cols; apply HPRR'; ColR.
      }
    destruct (HE5 P Q' R' S T' U) as [I [HQ'SI HPUI]]; Col; try split; Cong.
    apply HFalse; exists I; unfold BetS in *; spliter; assert_cols; split; ColR.
    }
  }

  {
  spliter; Col.
  }
Qed.


Lemma euclid_5_both_sides_2_3 :
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
   Col P R X ->
   Bet X S R' ->
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
    assert (HTS : two_sides Q S P X).
      {
      apply l9_8_2 with R'.

        {
        spliter; split; Col.
        split; try (intro; apply HPQ'S; assert_cols; ColR).
        split; try (intro; apply HPQS; assert_cols; ColR).
        exists S; split; Col; Between.
        }

        {
        apply l12_6; apply par_not_col_strict with P; Col.
        apply par_comm; apply par_symmetry; apply par_col_par with Q';
        spliter; assert_cols; Col.
        assert (HI := mid_plgs Q' S P R' T'); destruct HI as [Hc1 [Hc2 HCong6]];
        try (split); Cong; Col; try (spliter; Between); Par.
        }
      }
    assert (HPar : Par_strict Q S P R).
      {
      apply par_not_col_strict with P; Col.
      assert (HI := mid_plgs Q S P R T); destruct HI as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; clear Hc1; clear Hc2; clear Hc3.
    destruct HTS as [Hc1 [Hc2 [Hc3 [I [HQSI HPXI]]]]]; clear Hc1; clear Hc2; clear Hc3.
    apply HFalse; exists I; assert_cols; split; ColR.
    }
  }
Qed.

End Euclid_aux_2.