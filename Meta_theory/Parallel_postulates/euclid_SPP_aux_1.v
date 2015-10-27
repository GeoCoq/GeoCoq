Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section Euclid_aux_1.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma euclid_5_implies_strong_parallel_postulate_aux_1_1 :
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
   Bet P Q X ->
   Col R U X ->
   exists I : Tpoint, Col S Q I /\ Col P U I).
Proof.
intros HE5 P Q R S T U X HPTQ HRTS HNC HCong1 HCong2 HOS1 HOS2 HPQS H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HRTS.
elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

  {
  assert (H := inner_pasch P R X Q U H1 H2); destruct H as [I [HQRI HPUI]].
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
      exists I'; unfold BetS in *; spliter; assert_cols; split; ColR.
      }
    }
  }

  {
  elim (Col_dec Q S U); intro HQSU.

    {
    exists U; Col.
    }

    {
    assert (HQS : Q <> S) by (assert_diffs; Col).
    assert (HQU : Q <> U) by (assert_diffs; Col).
    elim (eq_dec_points R X); intro HRX; treat_equalities.

      {
      spliter; assert_cols; exists P; split; Col; ColR.
      }

      {
      assert (HTS : two_sides Q S P U).
        {
        assert (HOS : one_side Q S R P).
          {
          apply one_side_transitivity with T.

            {
            assert (H3 : Col Q S S) by Col.
            assert (H4 : Col R T S) by (spliter; assert_cols; Col).
            assert (H := l9_19 Q S R T S HQS H3 H4); rewrite H.
            spliter; assert_cols.
            split; try (intro; apply HNC; ColR).
            split; Between.
            }

            {
            apply one_side_symmetry.
            assert (H3 : Col Q S Q) by Col.
            assert (H4 : Col P T Q) by (spliter; assert_cols; Col).
            assert (H := l9_19 Q S P T Q HQS H3 H4); rewrite H.
            spliter; assert_cols.
            split; try (intro; apply HNC; ColR).
            split; Between.
            }
          }
        apply l9_8_2 with R; Col.
        elim (eq_dec_points Q X); intro HQX; treat_equalities.

          {
          spliter; assert_cols.
          split; Col.
          split; try (intro; apply HNC; ColR).
          split; try (intro; apply HNC; ColR).
          exists Q; split; Col; Between.
          }

          {
          assert (HTS : two_sides Q S R X).
            {
            apply l9_8_2 with P; try (apply one_side_symmetry); Col.
            spliter; assert_cols.
            split; Col.
            split; try (intro; apply HNC; ColR).
            split; try (intro; apply HNC; ColR).
            exists Q; Col.
            }
          spliter; assert_cols.
          split; Col.
          split; try (intro; apply HNC; ColR).
          split; Col.
          destruct HTS as [Hc1 [Hc2 [Hc3 [I [HCol1 HCol2]]]]].
          exists I; split; eBetween.
          }
        }
      destruct HTS as [Hc1 [Hc2 [Hc3 [I [H3 H4]]]]]; assert_cols.
      exists I; Col.
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

Lemma euclid_5_both_sides_1 :
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
   Col P S X ->
   Col R R' X ->
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
elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

  {
  apply l9_9 in HTS; apply HTS.
  assert (H3 : P <> S) by (assert_diffs; Col).
  assert (H4 : Col P S X) by Col.
  assert (H5 : Col R R' X) by (spliter; assert_cols; Col).
  assert (H := l9_19 P S R R' X H3 H4 H5); rewrite H.
  spliter; split; try (intro; apply HPQS; assert_cols; ColR).
  split; try (intro; treat_equalities; apply HPQS; assert_cols; ColR).
  split; try (intro; treat_equalities; apply HPQS; assert_cols; ColR).
  Between.
  }

  {
  clear HTS; elim H1; clear H1; intro H1; try (elim H1; clear H1; intro H1).

    {
    elim (eq_dec_points S X); intro HSX; treat_equalities.

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
      assert (HTS : two_sides R P R' S).
        {
        apply l9_31.

          {
          assert (H3 : R <> R') by (intro; subst; Col).
          assert (H4 : Col R R' X) by (assert_cols; Col).
          assert (H5 : Col P S X) by (assert_cols; Col).
          assert (H := l9_19 R R' P S X H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; subst; assert_cols; Col).
          Between.
          }

          {
          apply one_side_transitivity with T'.

            {
            apply l9_17 with Q'.

              {
              exists Q; split.

                {
                spliter; split; Col.
                split; try (intro; assert_cols; apply HPQS; ColR).
                split; try (intro; assert_cols; apply HPQS; ColR).
                exists T; assert_cols; Col.
                }

                {
                spliter; split; Col.
                split; try (intro; assert_cols; apply HPQS; ColR).
                split; try (intro; assert_cols; apply HPQS; ColR).
                exists S; split; Col; Between.
                }
              }

              {
              spliter; Col.
              }
            }

            {
            apply one_side_symmetry.
            assert (H3 : R <> S) by (spliter; Col).
            assert (H4 : Col R S S) by Col.
            assert (H5 : Col R' T' S) by (spliter; assert_cols; Col).
            assert (H := l9_19 R S R' T' S H3 H4 H5); rewrite H.
            show_distinct R R'; Col; spliter.
            split; try (intro; assert_cols; apply HPQS; ColR).
            split; Between.
            }
          }
        }
      apply l9_9 in HTS; apply HTS.
      apply one_side_transitivity with X.

        {
        assert (H3 : R <> P) by (assert_diffs; Col).
        assert (H4 : Col R P R) by Col.
        assert (H5 : Col R' X R) by (assert_cols; Col).
        assert (H := l9_19 R P R' X R H3 H4 H5); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; Between.
        intro; spliter; treat_equalities; apply HPQS; assert_cols; ColR.
        }

        {
        apply one_side_symmetry.
        assert (H3 : R <> P) by (assert_diffs; Col).
        assert (H4 : Col R P P) by Col.
        assert (H5 : Col S X P) by (assert_cols; Col).
        assert (H := l9_19 R P S X P H3 H4 H5); rewrite H.
        spliter; split; try (intro; assert_cols; apply HPQS; ColR).
        split; assert_diffs; Col.
        split; try (intro; treat_equalities); Between.
        }
      }
    }

    {
    elim (eq_dec_points S X); intro HSX; treat_equalities.

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
      apply BetSEq in HPTQ; apply BetSEq in HPT'Q'; apply BetSEq in HRTS;
      apply BetSEq in HR'T'S; apply BetSEq in HQSQ'.
      assert (H := HE5 R S P Q T X); destruct H as [I1 [HQSI1 HRXI1]]; Col; Cong.
      assert (H := HE5 R' S P Q' T' X); destruct H as [I2 [HQ'SI2 HR'XI2]]; Col; Cong.
      apply BetSEq in HPTQ; apply BetSEq in HPT'Q'; apply BetSEq in HRTS;
      apply BetSEq in HR'T'S; apply BetSEq in HQSQ'; apply BetSEq in HSXP;
      apply BetSEq in HQSI1; apply BetSEq in HRXI1; apply BetSEq in HQ'SI2;
      apply BetSEq in HR'XI2.
      assert (HQRS : ~ Col Q R S).
        {
        intro; spliter; assert_cols; apply HPQS; ColR.
        }
      assert (HCol1 : Col Q I1 I2) by (spliter; assert_cols; ColR).
      assert (HCol2 : Col R I1 I2) by (spliter; assert_cols; ColR).
      assert (HCol3 : Col S I1 I2) by (spliter; assert_cols; ColR).
      assert (HDiff : I1 <> I2).
        {
        clear H1; clear H2; assert (H1 := l5_2 Q S Q' I1); assert (H2 := l5_2 Q' S Q I2).
        spliter; elim H1; clear H1; elim H2; clear H2; Between; intros H1 H2;
        assert (Bet I1 S I2) by (assert_diffs; eBetween); intro; treat_equalities; Col.
        }
      apply HQRS; ColR.
      }
    }

    {
    assert (HPar : Par_strict Q S P R).
      {
      apply par_not_col_strict with P; Col.
      assert (H := mid_plgs Q S P R T); destruct H as [Hc1 [Hc2 HCong6]];
      try (split); Cong; Col; try (spliter; Between).
      }
    assert (HTS : two_sides R P R' S).
      {
      apply l9_31.

        {
        assert (H3 : R <> R') by (intro; subst; Col).
        assert (H4 : Col R R' X) by (assert_cols; Col).
        assert (H5 : Col P S X) by (assert_cols; Col).
        assert (H := l9_19 R R' P S X H3 H4 H5); rewrite H.
        split; Col.
        split; try (intro; subst; assert_cols; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        assert (HPRS : ~ Col P R S).
          {
          intro; spliter; assert_cols; apply HPQS; ColR.
          }
        apply one_side_transitivity with X.

          {
          assert (H3 : R <> S) by (assert_diffs; Col).
          assert (H4 : Col R S S) by Col.
          assert (H5 : Col P X S) by (assert_cols; Col).
          assert (H := l9_19 R S P X S H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; subst; assert_cols; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }

          {
          assert (H3 : R <> S) by (assert_diffs; Col).
          assert (H4 : Col R S R) by Col.
          assert (H5 : Col X R' R) by (assert_cols; Col).
          assert (H := l9_19 R S X R' R H3 H4 H5); rewrite H.
          split; try (intro; show_distinct S X; Col; assert_cols; apply HPRS; ColR).
          split; try (intro; treat_equalities; assert_cols; Col).
          split; try (intro; subst; Col).
          Between.
          }
        }
      }
    destruct HTS as [Hc1 [Hc2 [Hc3 [U [HPRU HR'SU]]]]]; clear Hc1; clear Hc2; clear Hc3.
    assert (HPU : P <> U).
      {
      assert (HPR'S : ~ Col P R' S).
        {
        intro; spliter; assert_cols; apply HPQ'S; ColR.
        }
      intro; treat_equalities; assert_cols; Col.
      }
    assert (H := l5_3 R' T' U S); elim H; clear H; try intro H; spliter; Col.

      {
      rename H into HR'T'U.
      assert (H := outer_pasch Q' S T' P U); destruct H as [I [HQSI HPUI]]; eBetween.
      destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; apply HFalse.
      exists I; assert_diffs; assert_cols;  split; ColR.
      }

      {
      rename H into HR'T'U.
      assert (H := outer_pasch Q' R' T' P U); destruct H as [V [HQ'R'V HPUV]]; Between.
      assert (HQ'VR' : BetS Q' V R').
        {
        split; Col.
        split.

          {
          destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; intro; treat_equalities; apply HFalse.
          exists Q'; assert_cols; split; Col; ColR.
          }

          {
          intro; treat_equalities; apply HPRR'; assert_cols; ColR.
          }
        }
      destruct (HE5 P Q' R' S T' V) as [I [HQ'SI HPVI]]; Col; try split; Col.
      destruct HPar as [Hc1 [Hc2 [Hc3 HFalse]]]; apply HFalse.
      unfold BetS in *; spliter; exists I; split; assert_cols; ColR.
      }
    }
  }

  {
  apply l9_9 in HTS; apply HTS.
  assert (H3 : P <> S) by (assert_diffs; Col).
  assert (H4 : Col P S X) by Col.
  assert (H5 : Col R R' X) by (spliter; assert_cols; Col).
  assert (H := l9_19 P S R R' X H3 H4 H5); rewrite H.
  spliter; split; try (intro; apply HPQS; assert_cols; ColR).
  split; try (intro; treat_equalities; apply HPQS; assert_cols; ColR).
  split; try (intro; treat_equalities; apply HPQS; assert_cols; ColR).
  Between.
  }
Qed.

End Euclid_aux_1.