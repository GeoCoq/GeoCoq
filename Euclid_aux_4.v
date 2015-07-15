Require Export Euclid_def.

Section Euclid_aux_4.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma euclid_5_implies_strong_parallel_postulate_aux_1_3 :
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
   Bet X P Q ->
   Col R U X ->
   exists I : Tpoint, Col S Q I /\ Col P U I).
Proof.
intros HE5 P Q R S T U X HPTQ HRTS HNC HCong1 HCong2 HOS1 HOS2 HPQS H1 H2.
apply BetSEq in HPTQ; apply BetSEq in HRTS.
elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

  {
  apply l9_9_bis in HOS1; exfalso; apply HOS1.
  apply l9_8_2 with Q.

    {
    apply l9_2; apply l9_8_2 with X.

      {
      assert_diffs; unfold BetS in *; spliter; split; Col.
      show_distinct P X; assert_cols; Col; split; try (intro; apply HPQS; ColR).
      split; try (intro; apply HPQS; ColR).
      exists P; Col.
      }

      {
      apply one_side_symmetry.
      assert (H3 : P <> R) by (assert_diffs; Col).
      assert (H4 : Col P R R) by Col.
      assert (H5 : Col U X R) by (assert_cols; Col).
      assert (H := l9_19 P R U X R H3 H4 H5); rewrite H.
      assert_diffs; spliter; split; Col.
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

  {
  apply l9_9_bis in HOS1; exfalso; apply HOS1.
  apply l9_8_2 with Q.

    {
    apply l9_2; apply l9_8_2 with X.

      {
      assert_diffs; spliter; split; Col.
      show_distinct P X; assert_cols; Col; split; try (intro; apply HPQS; ColR).
      split; try (intro; apply HPQS; ColR).
      exists P; Col.
      }

      {
      apply one_side_symmetry.
      assert (H3 : P <> R) by (assert_diffs; Col).
      assert (H4 : Col P R R) by Col.
      assert (H5 : Col U X R) by (assert_cols; Col).
      assert (H := l9_19 P R U X R H3 H4 H5); rewrite H.
      assert_diffs; spliter; split; Col.
      split; Col.
      split; try (intro; treat_equalities; apply HPQS; assert_cols; ColR).
      Between.
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
  assert (H := inner_pasch Q U X P R); destruct H as [I [HPUI HQRI]]; Between.
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
      unfold BetS in *.
      destruct (HE5 P Q R S T I) as [I' [HQSI' HPII']]; try split; spliter; Col.
      unfold BetS in *; exists I'; spliter; assert_cols; split; ColR.
      }
    }
  }
Qed.

Lemma coplanar_side_dec : forall O Ip Im Jp P P',
  coplanar O Ip Jp P ->
  is_midpoint O Ip Im ->
  is_midpoint O P P' ->
  ~ Col O Ip Jp ->
  ~ Col P Ip Im ->
  ~ Col P O Jp ->
  (one_side O Ip Jp P /\ one_side O Jp Ip P) \/
  (one_side O Im Jp P /\ one_side O Jp Im P) \/
  (one_side O Ip Jp P' /\ one_side O Jp Ip P') \/
  (one_side O Im Jp P' /\ one_side O Jp Im P').
Proof.
intros O Ip Im Jp P P' HCop HMid1 HMid2 HNC1 HNC2 HNC3.
destruct HCop as [X H].
elim H; clear H; try (intro H; elim H; clear H);
try intros H1 H2; try intro H; try destruct H as [H1 H2].

  {
  elim H1; clear H1; intro H1; try (elim H1; clear H1; intro H1).

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      left; split.

        {
        assert (H3 : O <> Ip) by (assert_diffs; Col).
        assert (H4 : Col O Ip X) by (assert_cols; Col).
        assert (H5 : Col Jp P X) by (assert_cols; Col).
        assert (H := l9_19 O Ip Jp P X H3 H4 H5); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; assert_diffs; assert_cols; apply HNC2; ColR).
        Between.
        }

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp O) by (assert_cols; Col).
          assert (H5 : Col Ip X O) by (assert_cols; Col).
          assert (H := l9_19 O Jp Ip X O H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp Jp) by (assert_cols; Col).
          assert (H5 : Col P X Jp) by (assert_cols; Col).
          assert (H := l9_19 O Jp P X Jp H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }
      }

      {
      right; right; right; split.

        {
        exists P; split.

          {
          assert_diffs; split; Col.
          split; try (intro; assert_cols; apply HNC1; ColR).
          split; try (intro; assert_cols; apply HNC2; ColR).
          exists X; assert_cols; split; Between; ColR.
          }

          {
          assert_diffs; split; Col.
          split; try (intro; assert_cols; apply HNC2; ColR).
          split; try (intro; assert_cols; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; Col.
            split; try (intro; assert_cols; apply HNC1; ColR).
            split; try (intro; assert_cols; apply HNC1; ColR).
            exists O; unfold is_midpoint in *; spliter; split; Col; eBetween.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp Jp) by (assert_cols; Col).
            assert (H5 : Col P X Jp) by (assert_cols; Col).
            assert (H := l9_19 O Jp P X Jp H3 H4 H5); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          split; try (intro; assert_cols; apply HNC3; ColR).
          split; try (intro; assert_cols; apply HNC3; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }

      {
      right; left; split.

        {
        assert (H3 : O <> Im) by (assert_diffs; Col).
        assert (H4 : Col O Im X) by (assert_diffs; assert_cols; ColR).
        assert (H5 : Col Jp P X) by (assert_cols; Col).
        assert (H := l9_19 O Im Jp P X H3 H4 H5); rewrite H.
        assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HNC2; ColR).
        Between.
        }

        {
        exists Ip; split.

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC1; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; eBetween.
          }

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; Col.
            assert_cols; split; try (intro; apply HNC1; ColR).
            split; Col.
            exists Jp; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp O) by (assert_cols; Col).
            assert (H5 : Col Ip X O) by (assert_cols; Col).
            assert (H := l9_19 O Jp Ip X O H3 H4 H5); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }
        }
      }
    }

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      left; split.

        {
        assert (H3 : O <> Ip) by (assert_diffs; Col).
        assert (H4 : Col O Ip X) by (assert_cols; Col).
        assert (H5 : Col Jp P X) by (assert_cols; Col).
        assert (H := l9_19 O Ip Jp P X H3 H4 H5); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; assert_diffs; assert_cols; apply HNC2; ColR).
        Between.
        }

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp O) by (assert_cols; Col).
          assert (H5 : Col Ip X O) by (assert_cols; Col).
          assert (H := l9_19 O Jp Ip X O H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp Jp) by (assert_cols; Col).
          assert (H5 : Col P X Jp) by (assert_cols; Col).
          assert (H := l9_19 O Jp P X Jp H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }
      }

      {
      right; right; right; split.

        {
        exists P; split.

          {
          assert_diffs; split; Col.
          split; try (intro; assert_cols; apply HNC1; ColR).
          split; try (intro; assert_cols; apply HNC2; ColR).
          exists X; assert_cols; split; Between; ColR.
          }

          {
          assert_diffs; split; Col.
          split; try (intro; assert_cols; apply HNC2; ColR).
          split; try (intro; assert_cols; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; Col.
            split; try (intro; assert_cols; apply HNC1; ColR).
            split; try (intro; assert_cols; apply HNC1; ColR).
            exists O; unfold is_midpoint in *; spliter; split; Col; eBetween.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp Jp) by (assert_cols; Col).
            assert (H5 : Col P X Jp) by (assert_cols; Col).
            assert (H := l9_19 O Jp P X Jp H3 H4 H5); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; assert_cols; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          split; try (intro; assert_cols; apply HNC3; ColR).
          split; try (intro; assert_cols; apply HNC3; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }

      {
      right; left; split.

        {
        assert (H3 : O <> Im) by (assert_diffs; Col).
        assert (H4 : Col O Im X) by (assert_diffs; assert_cols; ColR).
        assert (H5 : Col Jp P X) by (assert_cols; Col).
        assert (H := l9_19 O Im Jp P X H3 H4 H5); rewrite H.
        assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HNC2; ColR).
        Between.
        }

        {
        exists Ip; split.

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC1; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; eBetween.
          }

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; assert_cols; Col.
            assert_cols; split; try (intro; apply HNC1; ColR).
            split; Col.
            exists Jp; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp O) by (assert_cols; Col).
            assert (H5 : Col Ip X O) by (assert_cols; Col).
            assert (H := l9_19 O Jp Ip X O H3 H4 H5); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; assert_cols; Col).
            Between.
            }
          }
        }
      }
    }

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      right; left; split.

        {
        assert (H3 : O <> Im) by (assert_diffs; Col).
        assert (H4 : Col O Im X) by (assert_diffs; assert_cols; ColR).
        assert (H5 : Col Jp P X) by (assert_cols; Col).
        assert (H := l9_19 O Im Jp P X H3 H4 H5); rewrite H.
        assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HNC2; ColR).
        Between.
        }

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp O) by Col.
          assert (H5 : Col Im X O) by (assert_diffs; assert_cols; ColR).
          assert (H := l9_19 O Jp Im X O H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; assert_cols; Col).
          assert (H' := l5_2 Ip O Im X); elim H'; Between.
          unfold is_midpoint in *; spliter; eBetween.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp Jp) by Col.
          assert (H5 : Col P X Jp) by (assert_cols; Col).
          assert (H := l9_19 O Jp P X Jp H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }
      }

      {
      right; right; left; split.

        {
        exists P; split.

          {
          assert_diffs; split; Col.
          split; Col.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          exists X; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; Col.
            assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
            split; Col.
            exists O; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp Jp) by Col.
            assert (H5 : Col P X Jp) by (assert_cols; Col).
            assert (H := l9_19 O Jp P X Jp H3 H4 H5); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; assert_cols; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_diffs; assert_cols; split; try (intro; apply HNC3; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }

      {
      left; split.

        {
        assert (H3 : O <> Ip) by (assert_diffs; Col).
        assert (H4 : Col O Ip X) by (assert_diffs; assert_cols; ColR).
        assert (H5 : Col Jp P X) by (assert_cols; Col).
        assert (H := l9_19 O Ip Jp P X H3 H4 H5); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        exists X; split.

          {
          assert_diffs; split; Col.
          split; Col.
          show_distinct O X; assert_cols; Col.
          split; try (intro; apply HNC1; ColR).
          exists O; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          split; Col.
          show_distinct O X; assert_cols; Col.
          split; try (intro; apply HNC1; ColR).
          exists Jp; split; Col; Between.
          }
        }
      }
    }
  }

  {
  elim H1; clear H1; intro H1; try (elim H1; clear H1; intro H1).

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      left; split.

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Ip) by (assert_diffs; Col).
          assert (H4 : Col O Ip O) by (assert_cols; Col).
          assert (H5 : Col Jp X O) by (assert_cols; Col).
          assert (H := l9_19 O Ip Jp X O H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Ip) by (assert_diffs; Col).
          assert (H4 : Col O Ip Ip) by (assert_cols; Col).
          assert (H5 : Col P X Ip) by (assert_cols; Col).
          assert (H := l9_19 O Ip P X Ip H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        assert (H3 : O <> Jp) by (assert_diffs; Col).
        assert (H4 : Col O Jp X) by (assert_cols; Col).
        assert (H5 : Col Ip P X) by (assert_cols; Col).
        assert (H := l9_19 O Jp Ip P X H3 H4 H5); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }

      {
      right; left; split.

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Im) by (assert_diffs; Col).
          assert (H4 : Col O Im O) by (assert_cols; Col).
          assert (H5 : Col Jp X O) by (assert_cols; Col).
          assert (H := l9_19 O Im Jp X O H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Im) by (assert_diffs; Col).
          assert (H4 : Col O Im Ip) by (assert_cols; Col).
          assert (H5 : Col P X Ip) by (assert_cols; Col).
          assert (H := l9_19 O Im P X Ip H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        exists Ip; split.

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC1; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          split; Col.
          split; Col.
          exists X; assert_cols; Col.
          }
        }
      }

      {
      right; right; right; split.

        {
        exists P; split.

          {
          apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; Col.
            assert_cols; split; try (intro; apply HNC1; ColR).
            split; try (intro; apply HNC1; ColR).
            exists Ip; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Im) by (assert_diffs; Col).
            assert (H4 : Col O Im O) by (assert_cols; Col).
            assert (H5 : Col Jp X O) by (assert_cols; Col).
            assert (H := l9_19 O Im Jp X O H3 H4 H5); rewrite H.
            assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with Ip.

            {
            assert_diffs; split; Col.
            split; Col.
            assert_cols; split; try (intro; apply HNC1; ColR).
            exists O; unfold is_midpoint in *; spliter; split; Col; Between.
            }

            {
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp X) by Col.
            assert (H5 : Col Ip P X) by (assert_cols; Col).
            assert (H := l9_19 O Jp Ip P X H3 H4 H5); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; assert_cols; Col).
            split; try (intro; treat_equalities; assert_cols; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }
    }

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      left; split.

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Ip) by (assert_diffs; Col).
          assert (H4 : Col O Ip O) by (assert_cols; Col).
          assert (H5 : Col Jp X O) by (assert_cols; Col).
          assert (H := l9_19 O Ip Jp X O H3 H4 H5); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; assert_cols; apply HNC2; ColR).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Ip) by (assert_diffs; Col).
          assert (H4 : Col O Ip Ip) by (assert_cols; Col).
          assert (H5 : Col P X Ip) by (assert_cols; Col).
          assert (H := l9_19 O Ip P X Ip H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        assert (H3 : O <> Jp) by (assert_diffs; Col).
        assert (H4 : Col O Jp X) by (assert_cols; Col).
        assert (H5 : Col Ip P X) by (assert_cols; Col).
        assert (H := l9_19 O Jp Ip P X H3 H4 H5); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }

      {
      right; left; split.

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Im) by (assert_diffs; Col).
          assert (H4 : Col O Im O) by (assert_cols; Col).
          assert (H5 : Col Jp X O) by (assert_cols; Col).
          assert (H := l9_19 O Im Jp X O H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; apply HNC2; ColR).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Im) by (assert_diffs; Col).
          assert (H4 : Col O Im Ip) by (assert_cols; Col).
          assert (H5 : Col P X Ip) by (assert_cols; Col).
          assert (H := l9_19 O Im P X Ip H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        exists Ip; split.

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC1; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          split; Col.
          split; Col.
          exists X; assert_cols; Col.
          }
        }
      }

      {
      right; right; right; split.

        {
        exists P; split.

          {
          apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; assert_cols; try (apply HNC2; ColR).
            assert_cols; split; try (intro; apply HNC1; ColR).
            split; try (intro; apply HNC1; ColR).
            exists Ip; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Im) by (assert_diffs; Col).
            assert (H4 : Col O Im O) by (assert_cols; Col).
            assert (H5 : Col Jp X O) by (assert_cols; Col).
            assert (H := l9_19 O Im Jp X O H3 H4 H5); rewrite H.
            assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; apply HNC2; ColR).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with Ip.

            {
            assert_diffs; split; Col.
            split; Col.
            assert_cols; split; try (intro; apply HNC1; ColR).
            exists O; unfold is_midpoint in *; spliter; split; Col; Between.
            }

            {
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp X) by Col.
            assert (H5 : Col Ip P X) by (assert_cols; Col).
            assert (H := l9_19 O Jp Ip P X H3 H4 H5); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; assert_cols; Col).
            split; try (intro; treat_equalities; assert_cols; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }
    }

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      right; right; right; split.

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; assert_cols; try (apply HNC2; ColR).
            split; try (intro; apply HNC1; ColR).
            split; try (intro; apply HNC1; ColR).
            exists O; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Im) by (assert_diffs; Col).
            assert (H4 : Col O Im Ip) by (assert_cols; Col).
            assert (H5 : Col P X Ip) by (assert_cols; Col).
            assert (H := l9_19 O Im P X Ip H3 H4 H5); rewrite H.
            assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with Ip.

            {
            assert_diffs; split; Col.
            assert_cols; split; Col.
            split; try (intro; apply HNC1; ColR).
            exists O; unfold is_midpoint in *; spliter; split; Col; Between.
            }

            {
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp X) by (assert_cols; Col).
            assert (H5 : Col Ip P X) by (assert_cols; Col).
            assert (H := l9_19 O Jp Ip P X H3 H4 H5); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }

      {
      right; right; left; split.

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; assert_cols; try (apply HNC2; ColR).
            split; try (intro; apply HNC1; ColR).
            split; try (intro; apply HNC1; ColR).
            exists O; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Ip) by (assert_diffs; Col).
            assert (H4 : Col O Ip Ip) by (assert_cols; Col).
            assert (H5 : Col P X Ip) by (assert_cols; Col).
            assert (H := l9_19 O Ip P X Ip H3 H4 H5); rewrite H.
            assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          assert_diffs; split; Col.
          assert_cols; split; Col.
          split; Col.
          exists X; unfold is_midpoint in *; spliter; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }

      {
      left; split.

        {
        exists X; split.

          {
          assert_diffs; split; Col.
          split; Col.
          show_distinct O X; assert_cols; try (apply HNC2; ColR).
          split; try (intro; apply HNC1; ColR).
          exists O; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          show_distinct O X; assert_cols; try (apply HNC2; ColR).
          split; try (intro; apply HNC1; ColR).
          exists Ip; split; Col; Between.
          }
        }

        {
        assert (H3 : O <> Jp) by (assert_diffs; Col).
        assert (H4 : Col O Jp X) by (assert_cols; Col).
        assert (H5 : Col Ip P X) by (assert_cols; Col).
        assert (H := l9_19 O Jp Ip P X H3 H4 H5); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }
      }
    }
  }

  {
  elim H1; clear H1; intro H1; try (elim H1; clear H1; intro H1).

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      right; left; split.

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Im) by (assert_diffs; Col).
          assert (H4 : Col O Im Ip) by (assert_cols; Col).
          assert (H5 : Col Jp X Ip) by (assert_cols; Col).
          assert (H := l9_19 O Im Jp X Ip H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
          split; try Col.
          split; try (intro; treat_equalities; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Im) by (assert_diffs; Col).
          assert (H4 : Col O Im O) by (assert_cols; Col).
          assert (H5 : Col P X O) by (assert_cols; Col).
          assert (H := l9_19 O Im P X O H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try Col.
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        exists Ip; split.

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC1; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }

          {
          apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; Col.
            assert_cols; split; try (intro; apply HNC3; ColR).
            split; Col.
            exists Jp; split; Col; Between.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp O) by (assert_cols; Col).
            assert (H5 : Col P X O) by (assert_cols; Col).
            assert (H := l9_19 O Jp P X O H3 H4 H5); rewrite H.
            split; Col.
            assert_diffs; split; Col.
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }
        }
      }

      {
      left; split.

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Ip) by (assert_diffs; Col).
          assert (H4 : Col O Ip Ip) by (assert_cols; Col).
          assert (H5 : Col Jp X Ip) by (assert_cols; Col).
          assert (H := l9_19 O Ip Jp X Ip H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
          split; try Col.
          show_distinct O X; Col.
          split; try (intro; treat_equalities; apply HNC2; ColR).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Ip) by (assert_diffs; Col).
          assert (H4 : Col O Ip O) by (assert_cols; Col).
          assert (H5 : Col P X O) by (assert_cols; Col).
          assert (H := l9_19 O Ip P X O H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try Col.
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp Jp) by (assert_cols; Col).
          assert (H5 : Col Ip X Jp) by (assert_cols; Col).
          assert (H := l9_19 O Jp Ip X Jp H3 H4 H5); rewrite H.
          split; Col.
          assert_diffs; split; try Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp O) by (assert_cols; Col).
          assert (H5 : Col P X O) by (assert_cols; Col).
          assert (H := l9_19 O Jp P X O H3 H4 H5); rewrite H.
          split; Col.
          assert_diffs; split; try Col.
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }
      }

      {
      right; right; right; split.

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; Col.
            assert_cols; split; try (intro; apply HNC2; ColR).
            split; try (intro; apply HNC1; ColR).
            exists Ip; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Im) by (assert_diffs; Col).
            assert (H4 : Col O Im O) by (assert_cols; Col).
            assert (H5 : Col P X O) by (assert_cols; Col).
            assert (H := l9_19 O Im P X O H3 H4 H5); rewrite H.
            assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
            split; try Col.
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            apply l9_8_2 with Ip.

              {
              assert_diffs; split; Col.
              show_distinct O X; Col.
              assert_cols; split; try (intro; apply HNC2; ColR).
              split; try (intro; apply HNC1; ColR).
              exists O; unfold is_midpoint in *; spliter; split; Col; Between.
              }

              {
              assert (H3 : O <> Jp) by (assert_diffs; Col).
              assert (H4 : Col O Jp Jp) by (assert_cols; Col).
              assert (H5 : Col Ip X Jp) by (assert_cols; Col).
              assert (H := l9_19 O Jp Ip X Jp H3 H4 H5); rewrite H.
              split; Col.
              assert_diffs; split; try Col.
              split; try (intro; treat_equalities; Col).
              Between.
              }
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp O) by (assert_cols; Col).
            assert (H5 : Col P X O) by (assert_cols; Col).
            assert (H := l9_19 O Jp P X O H3 H4 H5); rewrite H.
            split; Col.
            assert_diffs; split; try Col.
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          split; try (intro; apply HNC3; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }
    }

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      right; left; split.

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Im) by (assert_diffs; Col).
          assert (H4 : Col O Im Ip) by (assert_cols; Col).
          assert (H5 : Col Jp X Ip) by (assert_cols; Col).
          assert (H := l9_19 O Im Jp X Ip H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
          split; try Col.
          split; try (intro; treat_equalities; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Im) by (assert_diffs; Col).
          assert (H4 : Col O Im O) by (assert_cols; Col).
          assert (H5 : Col P X O) by (assert_cols; Col).
          assert (H := l9_19 O Im P X O H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try Col.
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        exists Ip; split.

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC1; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }

          {
          apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; assert_cols; Col.
            split; try (intro; apply HNC3; ColR).
            split; Col.
            exists Jp; split; Col; Between.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp O) by (assert_cols; Col).
            assert (H5 : Col P X O) by (assert_cols; Col).
            assert (H := l9_19 O Jp P X O H3 H4 H5); rewrite H.
            split; Col.
            assert_diffs; split; Col.
            split; try (intro; treat_equalities; assert_cols; Col).
            Between.
            }
          }
        }
      }

      {
      left; split.

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Ip) by (assert_diffs; Col).
          assert (H4 : Col O Ip Ip) by (assert_cols; Col).
          assert (H5 : Col Jp X Ip) by (assert_cols; Col).
          assert (H := l9_19 O Ip Jp X Ip H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
          split; try Col.
          show_distinct O X; Col.
          split; try (intro; treat_equalities; apply HNC2; ColR).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Ip) by (assert_diffs; Col).
          assert (H4 : Col O Ip O) by (assert_cols; Col).
          assert (H5 : Col P X O) by (assert_cols; Col).
          assert (H := l9_19 O Ip P X O H3 H4 H5); rewrite H.
          assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
          split; try Col.
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        apply one_side_transitivity with X.

          {
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp Jp) by (assert_cols; Col).
          assert (H5 : Col Ip X Jp) by (assert_cols; Col).
          assert (H := l9_19 O Jp Ip X Jp H3 H4 H5); rewrite H.
          split; Col.
          assert_diffs; split; try Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H3 : O <> Jp) by (assert_diffs; Col).
          assert (H4 : Col O Jp O) by (assert_cols; Col).
          assert (H5 : Col P X O) by (assert_cols; Col).
          assert (H := l9_19 O Jp P X O H3 H4 H5); rewrite H.
          split; Col.
          assert_diffs; split; try Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }
        }
      }

      {
      right; right; right; split.

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; Col.
            assert_cols; split; try (intro; apply HNC2; ColR).
            split; try (intro; apply HNC1; ColR).
            exists Ip; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Im) by (assert_diffs; Col).
            assert (H4 : Col O Im O) by (assert_cols; Col).
            assert (H5 : Col P X O) by (assert_cols; Col).
            assert (H := l9_19 O Im P X O H3 H4 H5); rewrite H.
            assert_diffs; assert_cols; split; try (intro; apply HNC2; ColR).
            split; try Col.
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with X.

            {
            apply l9_8_2 with Ip.

              {
              assert_diffs; split; Col.
              show_distinct O X; Col.
              assert_cols; split; try (intro; apply HNC2; ColR).
              split; try (intro; apply HNC1; ColR).
              exists O; unfold is_midpoint in *; spliter; split; Col; Between.
              }

              {
              assert (H3 : O <> Jp) by (assert_diffs; Col).
              assert (H4 : Col O Jp Jp) by (assert_cols; Col).
              assert (H5 : Col Ip X Jp) by (assert_cols; Col).
              assert (H := l9_19 O Jp Ip X Jp H3 H4 H5); rewrite H.
              split; Col.
              assert_diffs; split; try Col.
              split; try (intro; treat_equalities; Col).
              Between.
              }
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp O) by (assert_cols; Col).
            assert (H5 : Col P X O) by (assert_cols; Col).
            assert (H := l9_19 O Jp P X O H3 H4 H5); rewrite H.
            split; Col.
            assert_diffs; split; try Col.
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          split; try (intro; apply HNC3; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }
    }

    {
    elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

      {
      right; right; right; split.

        {
        exists P; split.

          {
          apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; assert_cols; Col.
            split; try (intro; apply HNC2; ColR).
            split; try (intro; apply HNC2; ColR).
            exists O; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Im) by (assert_diffs; Col).
            assert (H4 : Col O Im Ip) by (assert_cols; Col).
            assert (H5 : Col Jp X Ip) by (assert_cols; Col).
            assert (H := l9_19 O Im Jp X Ip H3 H4 H5); rewrite H.
            assert_diffs; assert_cols; split; try (intro; apply HNC1; ColR).
            split; try Col.
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_2; apply l9_8_2 with Ip.

            {
            assert_diffs; split; Col.
            assert_cols; split; try (intro; apply HNC1; ColR).
            split; try (intro; apply HNC1; ColR).
            exists O; unfold is_midpoint in *; spliter; split; Col; Between.
            }

            {
            exists X; split.

              {
              assert_diffs; split; Col.
              split; Col.
              show_distinct O X; assert_cols; Col.
              split; try (intro; apply HNC3; ColR).
              exists Jp; Col.
              }

              {
              assert_diffs; split; Col.
              split; Col.
              show_distinct O X; assert_cols; Col.
              split; try (intro; apply HNC3; ColR).
              exists O; split; Col; Between.
              }
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          split; Col.
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }

      {
      right; right; left; split.

        {
        exists P; split.

          {
          apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; assert_cols; Col.
            assert_cols; split; try (intro; apply HNC2; ColR).
            split; try (intro; apply HNC2; ColR).
            exists O; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Ip) by (assert_diffs; Col).
            assert (H4 : Col O Ip Ip) by (assert_cols; Col).
            assert (H5 : Col Jp X Ip) by (assert_cols; Col).
            assert (H := l9_19 O Ip Jp X Ip H3 H4 H5); rewrite H.
            split; Col.
            assert_diffs; split; try Col.
            show_distinct O X; assert_cols; Col.
            split; try (intro; treat_equalities; apply HNC2; ColR).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          split; try (intro; apply HNC2; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }

        {
        exists P; split.

          {
          apply l9_8_2 with X.

            {
            assert_diffs; split; Col.
            show_distinct O X; assert_cols; Col.
            assert_cols; split; try (intro; apply HNC3; ColR).
            split; Col.
            exists O; Col.
            }

            {
            apply one_side_symmetry.
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp Jp) by (assert_cols; Col).
            assert (H5 : Col Ip X Jp) by (assert_cols; Col).
            assert (H := l9_19 O Jp Ip X Jp H3 H4 H5); rewrite H.
            split; Col.
            assert_diffs; split; Col.
            assert_cols; split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          split; try (intro; apply HNC3; ColR).
          exists O; unfold is_midpoint in *; spliter; split; Col; Between.
          }
        }
      }

      {
      right; left; split.

        {
        exists X; split.

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC1; ColR).
          show_distinct O X; Col.
          split; try (intro; apply HNC2; ColR).
          exists Ip; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          assert_cols; split; try (intro; apply HNC2; ColR).
          show_distinct O X; Col.
          split; try (intro; apply HNC2; ColR).
          exists O; split; Col; Between.
          }
        }

        {
        exists X; split.

          {
          apply l9_2; apply l9_8_2 with Ip.

            {
            assert_diffs; split; Col.
            split; Col.
            assert_cols; split; try (intro; apply HNC1; ColR).
            exists O; unfold is_midpoint in *; spliter; split; Col; Between.
            }

            {
            assert (H3 : O <> Jp) by (assert_diffs; Col).
            assert (H4 : Col O Jp Jp) by (assert_cols; Col).
            assert (H5 : Col Ip X Jp) by (assert_cols; Col).
            assert (H := l9_19 O Jp Ip X Jp H3 H4 H5); rewrite H.
            split; Col.
            assert_diffs; split; Col.
            assert_cols; split; try (intro; treat_equalities; Col).
            Between.
            }
          }

          {
          assert_diffs; split; Col.
          split; Col.
          show_distinct O X; Col.
          assert_cols; split; try (intro; apply HNC3; ColR).
          exists O; split; Col; Between.
          }
        }
      }
    }
  }
Qed.

Lemma impossible_case_8 : forall P Q R S T U I,
  BetS P T Q ->
  BetS R T S ->
  BetS Q U R ->
  ~ Col P Q S ->
  ~ Col P R U ->
  Par P R Q S ->
  Par P S Q R ->
  Col P U I ->
  Bet I S Q ->
  False.
Proof.
intros P Q R S T U I HPTQ HRTS HQUR HNC HNC' HPar1 HPar2 HPUI HSQI.
apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR.
elim HPUI; clear HPUI; intro HPUI.

  {
  assert (H : Par_strict P S Q R) by (apply par_not_col_strict with Q; Col; Par; unfold BetS in *;
                                      spliter; assert_cols; intro; apply HNC'; ColR); apply H.
  apply between_symmetry in HSQI.
  destruct (inner_pasch P Q I U S HPUI HSQI) as [J [HQJU HPJS]]; exists J.
  spliter; assert_diffs; assert_cols; split; Col; ColR.
  }

  {
  elim HPUI; clear HPUI; intro HPUI.

    {
    assert (H : Par_strict P S Q R) by (apply par_not_col_strict with Q; Col; Par; unfold BetS in *;
                                        spliter; assert_cols; intro; apply HNC'; ColR); apply H.
    apply between_symmetry in HSQI.
    destruct (outer_pasch U Q I P S HPUI HSQI) as [J [HQJU HPSJ]]; exists J.
    spliter; assert_diffs; assert_cols; split; Col; ColR.
    }

    {
    assert (H : Par_strict P R Q S) by (apply par_not_col_strict with Q; Col; Par; unfold BetS in *;
                                        spliter; assert_cols; intro; apply HNC'; ColR); apply H.
    destruct HQUR as [HQUR HDiff].
    destruct (outer_pasch Q I U R P HQUR HPUI) as [J [HQJI HRPJ]]; exists J.
    spliter; assert_diffs; assert_cols; split; Col.
    elim (eq_dec_points Q I); intro HQI; treat_equalities; Col; ColR.
    }
  }
Qed.

End Euclid_aux_4.