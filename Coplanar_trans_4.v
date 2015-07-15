Require Import Coplanar_perm.

Section Coplanar_trans_4.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma coplanar_trans_1_aux_4_2_1_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet P B X2 ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X2); intro HRX2; treat_equalities.

  {
  assert (HTS : two_sides R A B Q).
    {
    apply l9_8_2 with P.

      {
      split; assert_diffs; Col.
      split; try (intro; apply HABR; assert_cols; ColR).
      split; Col.
      exists X1; assert_cols; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by Col.
      assert (H3 : Col B P R) by (assert_cols; Col).
      assert (H := l9_19 R A B P R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; assert_diffs; Between.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
  exists I; right; right; split; Col.
  }

  {
  assert (HTS : two_sides R A B Q).
    {
    assert (HTS : two_sides R A X2 Q).
      {
      split; assert_diffs; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists R; split; Col; Between.
      }
    apply l9_8_2 with X2; Col.
    elim (eq_dec_points P X1); intro HPX1; treat_equalities.

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A P) by (assert_cols; Col).
      assert (H3 : Col B X2 P) by (assert_cols; Col).
      assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }

      {
      apply l9_17 with P; Between.
      exists Q; split; Col.
      split; assert_diffs; Col.
      split; try (intro; apply HNC; assert_cols; ColR).
      split; Col.
      exists X1; assert_cols; split; Col; Between.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
  exists I; right; right; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_1_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet P B X2 ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q A B R).
  {
  elim (eq_dec_points A X1); intro HAX1; treat_equalities.

    {
    apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
      show_distinct Q X2; try (apply HABQ; assert_cols; ColR).
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists Q; Col.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A P) by (assert_cols; Col).
      assert (H3 : Col B X2 P) by (assert_cols; Col).
      assert (H := l9_19 Q A B X2 P H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }

    {
    elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

      {
      apply l9_8_2 with X1.

        {
        split; assert_diffs; Col.
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists A; split; Col; Between.
        }

        {
        apply one_side_transitivity with P.

          {
          apply one_side_symmetry.
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A Q) by Col.
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 Q A P X1 Q H1 H2 H3); rewrite H.
          split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }

          {
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A Q) by Col.
          assert (H3 : Col P B Q) by (assert_cols; Col).
          assert (H := l9_19 Q A P B Q H1 H2 H3); rewrite H.
          split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }
        }
      }

      {
      assert (HOS : one_side Q A X1 P).
        {
        apply one_side_symmetry.
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by Col.
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 Q A P X1 Q H1 H2 H3); rewrite H.
        split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      assert (HTS : two_sides Q A X1 R).
        {
        split; assert_diffs; Col.
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists A; split; Col; Between.
        }
      apply l9_8_2 with X1; Col.
      apply one_side_transitivity with P; Col.
      apply l9_17 with X2; Col.
      apply one_side_transitivity with X1; apply one_side_symmetry; Col.
      exists R; split; Col.
      split; assert_diffs; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists Q; split; Col.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_2_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet P B X2 ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R A B Q).
  {
  elim (eq_dec_points P X1); intro HPX1; treat_equalities.

    {
    apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
      show_distinct R X2; try (apply HABR; assert_cols; ColR).
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists R; assert_cols; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A P) by (assert_cols; Col).
      assert (H3 : Col B X2 P) by (assert_cols; Col).
      assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }

    {
    apply l9_8_2 with P.

      {
      split; assert_diffs; Col.
      split; try (intro; assert_cols; apply HAQR; ColR).
      split; Col.
      exists X1; split; Col; Between.
      }

      {
      elim (eq_dec_points R X2); intro HRX2; treat_equalities.

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; Col).
        assert (H3 : Col B P R) by (assert_cols; Col).
        assert (H := l9_19 R A B P R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; Between.
        }

        {
        apply l9_17 with X2; Col.
        exists Q; split.

          {
          split; assert_diffs; Col.
          split; try (intro; assert_cols; apply HAQR; ColR).
          split; Col.
          exists X1; split; Col; Between.
          }

          {
          split; assert_diffs; Col.
          split; try (intro; apply HAQR; assert_cols; ColR).
          split; Col.
          exists R; split; Col; Between.
          }
        }
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
exists I; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_2_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet P B X2 ->
  Bet R X2 Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q B A R).
  {
  elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

    {
    split; assert_diffs; Col.
    split; Col.
    split; Col.
    exists X1; split; Col.
    assert_cols; ColR.
    }

    {
    elim (eq_dec_points P B); intro HPB; treat_equalities.

      {
      split; assert_diffs; Col.
      split; Col.
      split; Col.
      exists X1; assert_cols; Col.
      }

      {
      assert (HTS : two_sides Q B X1 R).
        {
        apply l9_8_2 with P.

          {
          apply l9_2; apply l9_8_2 with X2.

            {
            split; assert_diffs; Col.
            split; try (intro; apply HBQR; assert_cols; ColR).
            split; try (intro; apply HBQR; assert_cols; ColR).
            exists B; split; Col; Between.
            }

            {
            apply one_side_symmetry.
            assert (H1 : Q <> B) by (assert_diffs; auto).
            assert (H2 : Col Q B Q) by (assert_cols; Col).
            assert (H3 : Col R X2 Q) by (assert_cols; Col).
            assert (H := l9_19 Q B R X2 Q H1 H2 H3); rewrite H.
            split; Col.
            split; assert_diffs; Col.
            split; Between.
            }
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B Q) by (assert_cols; Col).
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 Q B P X1 Q H1 H2 H3); rewrite H.
          split; try (intro; apply HNC; assert_cols; ColR).
          split; assert_diffs; Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }
        }
      apply l9_8_2 with X1; Col.
      destruct HTS as [H1 [H2 [H3 [I [HQBI HRX1I]]]]]; clear H1; clear H2; clear H3.
      assert (HRX1 : R <> X1) by (intro; treat_equalities; Col).
      apply one_side_symmetry.
      assert (H1 : Q <> B) by (assert_diffs; auto).
      assert (H2 : Col Q B I) by (assert_cols; Col).
      assert (H3 : Col A X1 I) by (assert_cols; ColR).
      assert (H := l9_19 Q B A X1 I H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      show_distinct Q X1; assert_cols; Col.
      split; try (intro; treat_equalities; apply HNC; ColR).
      eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQBI HARI]]]]]; clear H1; clear H2; clear H3.
exists I; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_2_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet P B X2 ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch X2 P Q R X1 HCol4 (between_symmetry Q X1 P HCol1));
destruct H as [I [HPX2I HRX1I]].
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
assert (H := l5_3 X2 B I P (between_symmetry P B X2 HCol3) HPX2I);
elim H; clear H; intro HBX2I.

  {
  assert (HTS : two_sides R B Q A).
    {
    apply l9_31.

      {
      apply one_side_transitivity with I.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X2) by (assert_cols; Col).
        assert (H3 : Col B I X2) by (assert_cols; ColR).
        assert (H := l9_19 R Q B I X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q R) by (assert_cols; Col).
        assert (H3 : Col A I R) by (assert_cols; ColR).
        assert (H := l9_19 R Q A I R H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        assert (HE := l5_2 R X1 A I HRX1 (between_symmetry A X1 R HCol2) HRX1I).
        elim HE; eBetween.
        }
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A I) by (assert_cols; ColR).
        assert (H3 : Col B X2 I) by (assert_cols; Col).
        assert (H := l9_19 R A B X2 I H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; ColR).
        assert (H3 : Col Q X2 R) by (assert_cols; Col).
        assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : two_sides R A Q B).
    {
    apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
      show_distinct R X2; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists I; assert_cols; split; Col; ColR.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by (assert_cols; ColR).
      assert (H3 : Col Q X2 R) by (assert_cols; Col).
      assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; right; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet P B X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_2_2_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_2_2_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_2_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet B X2 P ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : two_sides Q R A B).
  {
  apply l9_8_2 with P.

    {
    split; assert_diffs; Col.
    split; Col.
    split; Col.
    exists X2; assert_cols; split; Col; Between.
    }

    {
    apply one_side_transitivity with X1.

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by (assert_cols; ColR).
      assert (H3 : Col P X1 Q) by (assert_cols; Col).
      assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R R) by (assert_cols; ColR).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_2_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet X2 P B ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch Q B X2 R P HCol4 (between_symmetry X2 P B HCol3));
destruct H as [I [HRBI HPQI]].
assert (H := l5_3 P X1 I Q (between_symmetry Q X1 P HCol1) HPQI); elim H; clear H; intro PX1I.

  {
  assert (HTS : two_sides R B A Q).
    {
    apply l9_8_2 with X1.

      {
      assert_diffs; split; Col.
      show_distinct R X1; assert_cols; Col.
      split; try (intro; apply HABR; assert_cols; ColR).
      split; Col.
      exists I; assert_cols; split; Col; eBetween.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> B) by (assert_diffs; auto).
      assert (H2 : Col R B R) by (assert_cols; ColR).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : two_sides R A Q B).
    {
    apply l9_31.

      {
      apply one_side_transitivity with X1.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q R) by (assert_cols; ColR).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }

        {
        apply one_side_transitivity with P.

          {
          apply one_side_symmetry.
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q Q) by (assert_cols; ColR).
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
          split; Col.
          assert_diffs; split; Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q X2) by (assert_cols; ColR).
          assert (H3 : Col B P X2) by (assert_cols; Col).
          assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }
      }

      {
      apply one_side_transitivity with X1.

        {
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B R) by (assert_cols; ColR).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B I) by (assert_cols; ColR).
        assert (HPX1 : P <> X1).
          {
          intro; treat_equalities; assert_diffs; assert_cols; apply HABR; ColR.
          }
        assert (H3 : Col Q X1 I) by (assert_cols; ColR).
        assert (H := l9_19 R B Q X1 I H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        show_distinct R X1; assert_cols; Col.
        split; try (intro; treat_equalities; apply HABR; ColR).
        eBetween.
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; right; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_2_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet X2 P B ->
  Bet R X2 Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R A Q B).
  {
  elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      assert_diffs; split; Col.
      split; try (intro; apply HABR; assert_cols; ColR).
      split; Col.
      exists X1; assert_cols; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by (assert_cols; ColR).
      assert (H3 : Col B P R) by (assert_cols; Col).
      assert (H := l9_19 R A B P R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      }
    }

    {
    apply l9_8_2 with X2.

      {
      elim (eq_dec_points P X1); intro HPX1; treat_equalities.

        {
        assert_diffs; split; Col.
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists P; assert_cols; Col.
        }

        {
        assert_diffs; split; Col.
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        assert (H := inner_pasch P R Q X1 X2 (between_symmetry Q X1 P HCol1) HCol4);
        destruct H as [I [HRX1I HPX2I]].
        show_distinct R X1; assert_cols; Col.
        exists I; split; eBetween; ColR.
        }
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by (assert_cols; ColR).
      assert (H3 : Col Q X2 R) by (assert_cols; Col).
      assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
exists I; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_2_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet X2 P B ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R A Q B).
  {
  elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      assert_diffs; split; Col.
      split; try (intro; apply HABR; assert_cols; ColR).
      split; Col.
      exists X1; assert_cols; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by (assert_cols; ColR).
      assert (H3 : Col B P R) by (assert_cols; Col).
      assert (H := l9_19 R A B P R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      }
    }

    {
    apply l9_8_2 with X2.

      {
      elim (eq_dec_points P X1); intro HPX1; treat_equalities.

        {
        assert_diffs; split; Col.
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists P; assert_cols; Col.
        }

        {
        assert_diffs; split; Col.
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        assert (H := outer_pasch X2 P Q R X1 HCol4 (between_symmetry Q X1 P HCol1));
        destruct H as [I [HPX2I HRX1I]].
        show_distinct R X1; assert_cols; Col.
        exists I; split; eBetween; ColR.
        }
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by (assert_cols; ColR).
      assert (H3 : Col Q X2 R) by (assert_cols; Col).
      assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
exists I; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet A X1 R ->
  Bet X2 P B ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_2_2_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_2_2_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_2_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet A X1 R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_2_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_2_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet X1 R A ->
  Bet P B X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : two_sides Q R B A).
  {
  apply l9_8_2 with X1.

    {
    split; assert_diffs; Col.
    show_distinct R X1; assert_cols; Col.
    split; try (intro; apply HAQR; ColR).
    split; Col.
    exists R; Col.
    }

    {
    apply one_side_transitivity with P.

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by (assert_cols; ColR).
      assert (H3 : Col P X1 Q) by (assert_cols; Col).
      assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R X2) by (assert_cols; ColR).
      assert (H3 : Col B P X2) by (assert_cols; Col).
      assert (H := l9_19 Q R B P X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_3_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch P Q X2 B R (between_symmetry B X2 P HCol3) HCol4);
destruct H as [I [HPQI HRBI]].
assert (H := l5_3 P X1 I Q (between_symmetry Q X1 P HCol1) HPQI); elim H; clear H; intro PX1I.

  {
  assert (HTS : two_sides R A Q B).
    {
    apply l9_31.

      {
      exists X1; split.

        {
        assert_diffs; split; Col.
        split; Col.
        show_distinct R X1; assert_cols; Col.
        split; try (intro; apply HAQR; ColR).
        exists R; split; Col; Between.
        }

        {
        apply l9_2; apply l9_8_2 with P.

          {
          assert_diffs; split; Col.
          split; Col.
          split; Col.
          exists X2; assert_cols; split; Col; Between.
          }

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q Q) by (assert_cols; ColR).
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
          split; Col.
          assert_diffs; split; Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }
        }
      }

      {
      exists X1; split.

        {
        assert_diffs; split; Col.
        split; Col.
        show_distinct R X1; assert_cols; Col.
        split; try (intro; apply HABR; ColR).
        exists R; split; Col; Between.
        }

        {
        assert_diffs; split; Col.
        split; Col.
        show_distinct R X1; assert_cols; Col.
        split; try (intro; apply HABR; ColR).
        exists I; split; Col; eBetween.
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; right; split; Col.
  }

  {
  assert (HTS : two_sides R B Q A).
    {
    apply l9_8_2 with X1.

      {
      assert_diffs; split; Col.
      show_distinct R X1; assert_cols; Col.
      split; try (intro; apply HABR; ColR).
      split; Col.
      exists R; Col.
      }

      {
      apply one_side_symmetry.
      assert (HPX1 : P <> X1).
        {
        intro; treat_equalities; apply HABR; assert_diffs; assert_cols; ColR.
        }
      assert (H1 : R <> B) by (assert_diffs; auto).
      assert (H2 : Col R B I) by (assert_cols; ColR).
      assert (H3 : Col Q X1 I) by (assert_cols; ColR).
      assert (H := l9_19 R B Q X1 I H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      show_distinct R X1; assert_cols; Col.
      split; try (intro; treat_equalities; apply HABR; ColR).
      eBetween.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_3_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet R X2 Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
  apply l9_31.

    {
    exists X1; split.

      {
      apply l9_2; apply l9_8_2 with P.

        {
        assert_diffs; split; Col.
        split; Col.
        split; Col.
        exists X2; assert_cols; split; Col; Between.
        }

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q Q) by (assert_cols; ColR).
        assert (H3 : Col P X1 Q) by (assert_cols; ColR).
        assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }

      {
      assert_diffs; split; Col.
      split; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      exists R; split; Col; Between.
      }
    }

    {
    elim (eq_dec_points R X2); intro HRX2; treat_equalities.

      {
      exists P; split.

        {
        assert_diffs; split; Col.
        split; Col.
        split; try (intro; apply HABR; assert_cols; ColR).
        exists R; Col.
        }

        {
        assert_diffs; split; Col.
        split; Col.
        split; try (intro; apply HABR; assert_cols; ColR).
        exists X1; assert_cols; Col.
        }
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H := inner_pasch P R Q X1 X2 (between_symmetry Q X1 P HCol1) HCol4);
        destruct H as [I [HRX1I HPX2I]].
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A I) by (assert_cols; ColR).
        assert (HPX2 : P <> X2) by (intro; treat_equalities; assert_cols; Col).
        assert (H3 : Col B X2 I) by (assert_cols; ColR).
        assert (H := l9_19 R A B X2 I H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
        eBetween.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; ColR).
        assert (H3 : Col Q X2 R) by (assert_cols; ColR).
        assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        }
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_3_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
  apply l9_31.

    {
    exists X1; split.

      {
      apply l9_2; apply l9_8_2 with P.

        {
        assert_diffs; split; Col.
        split; Col.
        split; Col.
        exists X2; assert_cols; split; Col; Between.
        }

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q Q) by (assert_cols; ColR).
        assert (H3 : Col P X1 Q) by (assert_cols; ColR).
        assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }

      {
      assert_diffs; split; Col.
      split; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      exists R; split; Col; Between.
      }
    }

    {
    elim (eq_dec_points R X2); intro HRX2; treat_equalities.

      {
      exists P; split.

        {
        assert_diffs; split; Col.
        split; Col.
        split; try (intro; apply HABR; assert_cols; ColR).
        exists R; Col.
        }

        {
        assert_diffs; split; Col.
        split; Col.
        split; try (intro; apply HABR; assert_cols; ColR).
        exists X1; assert_cols; Col.
        }
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H := outer_pasch X2 P Q R X1 HCol4 (between_symmetry Q X1 P HCol1));
        destruct H as [I [HPX2I HRX1I]].
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A I) by (assert_cols; ColR).
        assert (HPX2 : P <> X2) by (intro; treat_equalities; assert_cols; Col).
        assert (H3 : Col B X2 I) by (assert_cols; ColR).
        assert (H := l9_19 R A B X2 I H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
        eBetween.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; ColR).
        assert (H3 : Col Q X2 R) by (assert_cols; ColR).
        assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Between.
        }
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet X1 R A ->
  Bet B X2 P ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_2_3_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_2_3_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_3_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet X1 R A ->
  Bet X2 P B ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : two_sides Q R B A).
  {
  apply l9_8_2 with X1.

    {
    split; assert_diffs; Col.
    show_distinct R X1; assert_cols; Col.
    split; try (intro; apply HAQR; ColR).
    split; Col.
    exists R; Col.
    }

    {
    apply one_side_transitivity with P.

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by (assert_cols; ColR).
      assert (H3 : Col P X1 Q) by (assert_cols; Col).
      assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R X2) by (assert_cols; ColR).
      assert (H3 : Col B P X2) by (assert_cols; Col).
      assert (H := l9_19 Q R B P X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet X1 R A ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_2_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_2_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_1_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet P B X2 ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch X1 X2 Q P R HCol1 (between_symmetry Q R X2 HCol4));
destruct H as [I [HPX2I HRX1I]].
assert (H := l5_3 P B I X2 HCol3 HPX2I); elim H; clear H; intro HPBI.

  {
  assert (HTS : two_sides R B Q A).
    {
    apply l9_31.

      {
      apply one_side_transitivity with X1.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q X2) by (assert_cols; ColR).
          assert (H3 : Col B P X2) by (assert_cols; Col).
          assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q Q) by (assert_cols; ColR).
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
          split; Col.
          assert_diffs; split; Col.
          split; try (intro; treat_equalities); Between.
          }
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q R) by (assert_cols; ColR).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities); Between.
        }
      }

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (HRX1 : R <> X1) by (intro; treat_equalities; Col).
        assert (H2 : Col R A I) by (assert_cols; ColR).
        assert (H3 : Col B P I) by (assert_cols; Col).
        assert (H := l9_19 R A B P I H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; ColR).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        show_distinct R X1; Col.
        show_distinct P I; try (apply HABR; assert_cols; ColR).
        split; try (intro; treat_equalities; apply HABR; assert_cols; ColR).
        Between.
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : two_sides R A Q B).
    {
    assert (HRX1 : R <> X1) by (intro; treat_equalities; Col).
    elim (eq_dec_points P I); intro HPI; treat_equalities.

      {
      apply l9_2; apply l9_8_2 with X2.

        {
        assert_diffs; split; Col.
        show_distinct R X2; try (apply HABR; assert_cols; ColR).
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists R; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A P) by (assert_cols; ColR).
        assert (H3 : Col B X2 P) by (assert_cols; Col).
        assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }

      {
      apply l9_8_2 with P.

        {
        assert_diffs; split; Col.
        show_distinct P X1; try (apply HABR; assert_cols; ColR).
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists I; assert_cols; split; Between; ColR.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; ColR).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        show_distinct R X1; Col.
        show_distinct P I; try (apply HABR; assert_cols; ColR).
        split; try (intro; treat_equalities; apply HABR; assert_cols; ColR).
        Between.
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; right; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_1_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet P B X2 ->
  Bet R X2 Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  apply l9_31.

    {
    apply one_side_transitivity with X1.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X2) by (assert_cols; ColR).
        assert (H3 : Col B P X2) by (assert_cols; Col).
        assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q Q) by (assert_cols; ColR).
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities); Between.
        }
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> Q) by (assert_diffs; auto).
      assert (H2 : Col R Q R) by (assert_cols; ColR).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities); Between.
      }
    }

    {
    elim (eq_dec_points R X2); intro HRX2; treat_equalities.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; Col).
        assert (H3 : Col B P R) by (assert_cols; Col).
        assert (H := l9_19 R A B P R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; try (intro; treat_equalities); Col; Between.
        }

        {
        apply one_side_symmetry; apply l9_17 with P; Between.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HABR; assert_diffs; assert_cols; ColR).
        Between.
        }
      }

      {
      assert (HOS : one_side R A X2 Q).
        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by Col.
        assert (H3 : Col Q X2 R) by (assert_cols; Col).
        assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        }
      apply one_side_transitivity with X2; Col.
      elim (eq_dec_points P X1); intro HPX1; treat_equalities.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A P) by (assert_cols; ColR).
        assert (H3 : Col B X2 P) by (assert_cols; Col).
        assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        apply one_side_symmetry; apply l9_17 with P; Between.
        apply one_side_transitivity with Q; Col.        
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; ColR).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        Between.
        }
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_1_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet P B X2 ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  apply l9_31.

    {
    apply one_side_transitivity with X1.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X2) by (assert_cols; ColR).
        assert (H3 : Col B P X2) by (assert_cols; Col).
        assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q Q) by (assert_cols; ColR).
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities); Between.
        }
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> Q) by (assert_diffs; auto).
      assert (H2 : Col R Q R) by (assert_cols; ColR).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities); Between.
      }
    }

    {
    assert (HOS : one_side R A X2 Q).
      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by Col.
      assert (H3 : Col Q X2 R) by (assert_cols; Col).
      assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; Col).
      Between.
      }
    apply one_side_transitivity with X2; Col.
    elim (eq_dec_points P X1); intro HPX1; treat_equalities.

      {
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A P) by (assert_cols; ColR).
      assert (H3 : Col B X2 P) by (assert_cols; Col).
      assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }

      {
      apply one_side_symmetry; apply l9_17 with P; Between.
      apply one_side_transitivity with Q; Col.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A X1) by (assert_cols; ColR).
      assert (H3 : Col Q P X1) by (assert_cols; Col).
      assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet P B X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_3_1_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_3_1_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_1_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet B X2 P ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q R A B).
  {
  apply l9_8_2 with P.

    {
    assert_diffs; split; Col.
    split; Col.
    split; Col.
    exists X2; assert_cols; split; Col; Between.
    }

    {
    apply one_side_transitivity with X1.

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by (assert_cols; ColR).
      assert (H3 : Col P X1 Q) by (assert_cols; Col).
      assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; Col).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R R) by (assert_cols; ColR).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_1_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet X2 P B ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  apply l9_31.

    {
    apply one_side_transitivity with X1.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X2) by (assert_cols; ColR).
        assert (H3 : Col B P X2) by (assert_cols; Col).
        assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q Q) by (assert_cols; ColR).
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities); Between.
        }
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> Q) by (assert_diffs; auto).
      assert (H2 : Col R Q R) by (assert_cols; ColR).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities); Between.
      }
    }

    {
    elim (eq_dec_points R X2); intro HRX2; treat_equalities.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by Col.
        assert (H3 : Col B P R) by (assert_cols; Col).
        assert (H := l9_19 R A B P R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HABR; assert_diffs; assert_cols; ColR).
        Between.
        }
      }

      {
      elim (eq_dec_points P X1); intro HPX1; treat_equalities.

        {
        exists X2; split.

          {
          assert_diffs; split; Col.
          split; Col.
          split; try (intro; assert_cols; apply HAQR; ColR).
          exists P; assert_cols; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          split; Col.
          split; try (intro; assert_cols; apply HAQR; ColR).
          exists R; Col.
          }
        }

        {
        assert (HTS : two_sides R A P X2).
          {
          apply l9_8_2 with Q.

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; assert_cols; apply HAQR; ColR).
            exists R; Col.
            }

            {
             assert (H1 : R <> A) by (assert_diffs; auto).
             assert (H2 : Col R A X1) by (assert_cols; Col).
             assert (H3 : Col Q P X1) by (assert_cols; Col).
             assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
             split; Col.
             split; try (intro; treat_equalities; Col).
             split; Between.
            }
          }
        exists X2; split.

          {
          apply l9_8_2 with P; Col.
          destruct HTS as [H1 [HAPR [HARX2 [I [HARI HPX2I]]]]].
          assert (HPX2 : P <> X2) by (intro; treat_equalities; Col).
          assert (H2 : Col R A I) by Col.
          assert (H3 : Col P B I) by (assert_cols; ColR).
          assert (H := l9_19 R A P B I H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          eBetween.
          }

          {
          assert_diffs; split; Col.
          split; Col.
          split; try (intro; apply HAQR; assert_cols; ColR).
          exists R; Col.
          }
        }
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_1_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet X2 P B ->
  Bet R X2 Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q A B R).
  {
  elim (eq_dec_points A X1); intro HAX1; treat_equalities.

    {
    apply l9_2; apply l9_8_2 with X2.

      {
      assert_diffs; split; Col.
      show_distinct Q X2; try (apply HABQ; assert_cols; ColR).
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists P; assert_cols; Col.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by (assert_cols; Col).
      assert (H3 : Col R X2 Q) by (assert_cols; Col).
      assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; apply HABQ; assert_cols; ColR).
      Between.
      }
    }

    {
    elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

      {
      apply l9_8_2 with P.

        {
        apply l9_8_2 with X1.

          {
          assert_diffs; split; Col.
          split; try (intro; apply HAQR; assert_cols; ColR).
          split; Col.
          exists A; split; Col; Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A Q) by (assert_cols; Col).
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 Q A P X1 Q H1 H2 H3); rewrite H.
          split; try (intro; apply HAQR; assert_diffs; assert_cols; ColR).
          assert_diffs; split; Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by (assert_cols; Col).
        assert (H3 : Col B P Q) by (assert_cols; Col).
        assert (H := l9_19 Q A B P Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        }
      }          

      {
      assert (HOS : one_side Q A R X2).
        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by (assert_cols; Col).
        assert (H3 : Col R X2 Q) by (assert_cols; Col).
        assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Between.
        }
      assert (HTS : two_sides Q A P X2).
        {
        apply l9_2; apply l9_8_2 with R; Col.
        assert_diffs; split; Col.
        split; Col.
        split; try (intro; apply HNC; assert_cols; ColR).
        assert (H := inner_pasch Q R X1 P A (between_symmetry X1 P Q HCol1) HCol2);
        destruct H as [I [HPRI HQAI]].
        exists I; assert_cols; split; Col; Between.
        }
      apply l9_2; apply l9_8_2 with X2; try (apply one_side_symmetry; Col).
      assert_diffs; split; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      destruct HTS as [Hc1 [Hc2 [Hc3 [I [HQAI HPX2I]]]]].
      exists I; eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_1_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet X2 P B ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch Q R X1 P A (between_symmetry X1 P Q HCol1) HCol2);
destruct H as [I1 [HPRI1 HQAI1]].
apply between_symmetry in HCol3; apply between_symmetry in HCol4.
assert (H := inner_pasch R B X2 Q P HCol4 HCol3); destruct H as [I2 [HQBI2 HPRI2]].
assert (H := l5_3 P I1 I2 R HPRI1 HPRI2); elim H; clear H; intro PI1I2.

  {
  assert (HTS : two_sides Q B A R).
    {
    apply l9_8_2 with I1.

      {
      assert_diffs; split; Col.
      show_distinct Q I1; assert_cols; Col.
      split; try (intro; apply HABQ; ColR).
      split; Col.
      exists I2; assert_cols; split; Col; eBetween.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> B) by (assert_diffs; auto).
      assert (H2 : Col Q B Q) by (assert_cols; Col).
      assert (H3 : Col A I1 Q) by (assert_cols; Col).
      assert (H := l9_19 Q B A I1 Q H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I [HQBI HRAI]]]]]; clear H1; clear H2; clear H3.
  exists I; right; right; split; Col.
  }

  {
  assert (HTS : two_sides Q A B R).
    {
    apply l9_8_2 with I2.

      {
      assert_diffs; split; Col.
      show_distinct Q I2; assert_cols; Col.
      split; try (intro; apply HABQ; ColR).
      split; Col.
      exists I1; assert_cols; split; Col; eBetween.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by (assert_cols; Col).
      assert (H3 : Col B I2 Q) by (assert_cols; Col).
      assert (H := l9_19 Q A B I2 Q H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
  exists I; right; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet R A X1 ->
  Bet X2 P B ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_3_1_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_3_1_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_1_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet R A X1 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_3_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_3_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_2_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet P B X2 ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HOS : one_side R Q A B).
  {
  apply one_side_transitivity with X1.

    {
    assert (H1 : R <> Q) by (assert_diffs; auto).
    assert (H2 : Col R Q R) by (assert_cols; Col).
    assert (H3 : Col A X1 R) by (assert_cols; Col).
    assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
    split; Col.
    assert_diffs; split; Col.
    split; try (intro; treat_equalities; assert_cols; Col).
    Between.
    }

    {
    apply one_side_transitivity with P.

      {
      apply one_side_symmetry.
      assert (H1 : R <> Q) by (assert_diffs; auto).
      assert (H2 : Col R Q Q) by (assert_cols; Col).
      assert (H3 : Col P X1 Q) by (assert_cols; Col).
      assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities); Between.
      }

      {
      assert (H1 : R <> Q) by (assert_diffs; auto).
      assert (H2 : Col R Q X2) by (assert_cols; Col).
      assert (H3 : Col P B X2) by (assert_cols; Col).
      assert (H := l9_19 R Q P B X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  }
assert (H := inner_pasch X1 X2 Q P R HCol1 (between_symmetry Q R X2 HCol4));
destruct H as [I [HPX2I HRX1I]].
assert (H := l5_3 P B I X2 HCol3 HPX2I); elim H; clear H; intro HPBI.

  {
  assert (HTS : two_sides R B Q A).
    {
    assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
    apply l9_31; try (apply one_side_symmetry; Col).
    apply one_side_transitivity with P.

      {
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A X1) by (assert_cols; Col).
      assert (H3 : Col Q P X1) by (assert_cols; Col).
      assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      show_distinct P X2; assert_cols; Col.
      show_distinct P I; try (apply HABR; ColR).
      split; try (intro; treat_equalities; apply HABR; assert_diffs; ColR).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A I) by (assert_cols; ColR).
      assert (H3 : Col B P I) by (assert_cols; Col).
      assert (H := l9_19 R A B P I H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; apply HABR; assert_cols; ColR).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : two_sides R A Q B).
    {
    assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
    elim (eq_dec_points P X1); intro HPX1; treat_equalities.

      {
      apply l9_2; apply l9_8_2 with X2.

        {
        assert_diffs; split; Col.
        show_distinct R X2; try (apply HABR; assert_cols; ColR).
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists R; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A P) by (assert_cols; ColR).
        assert (H3 : Col B X2 P) by (assert_cols; Col).
        assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }

      {
      apply l9_8_2 with P.

        {
        assert_diffs; split; Col.
        split; try (intro; apply HNC; assert_cols; ColR).
        split; Col.
        exists I; assert_cols; split; Col; ColR.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        Between.
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; right; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_2_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet P B X2 ->
  Bet R X2 Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  apply l9_31.

    {
    apply one_side_transitivity with P.

      {
      assert (H1 : R <> Q) by (assert_diffs; auto).
      assert (H2 : Col R Q X2) by (assert_cols; Col).
      assert (H3 : Col B P X2) by (assert_cols; Col).
      assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }

      {
      apply one_side_transitivity with X1.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q Q) by (assert_cols; Col).
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities); Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q R) by (assert_cols; Col).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }
    }

    {
    elim (eq_dec_points R X2); intro HRX2; treat_equalities.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; Col).
        assert (H3 : Col B P R) by (assert_cols; Col).
        assert (H := l9_19 R A B P R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HABR; assert_diffs; assert_cols; ColR).
        Between.
        }
      }

      {
      assert (HOS : one_side R A X2 Q).
        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; Col).
        assert (H3 : Col Q X2 R) by (assert_cols; Col).
        assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        }
      apply one_side_transitivity with X2; Col.
      elim (eq_dec_points P X1); intro HPX1; treat_equalities.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A P) by (assert_cols; Col).
        assert (H3 : Col B X2 P) by (assert_cols; Col).
        assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        apply one_side_symmetry; apply l9_17 with P; Between.
        apply one_side_transitivity with Q; Col.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities); Between.
        }
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_2_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet P B X2 ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  apply l9_31.

    {
    apply one_side_transitivity with P.

      {
      assert (H1 : R <> Q) by (assert_diffs; auto).
      assert (H2 : Col R Q X2) by (assert_cols; Col).
      assert (H3 : Col B P X2) by (assert_cols; Col).
      assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }

      {
      apply one_side_transitivity with X1.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q Q) by (assert_cols; Col).
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities); Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q R) by (assert_cols; Col).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }
    }

    {
    assert (HOS : one_side R A X2 Q).
      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by (assert_cols; Col).
      assert (H3 : Col Q X2 R) by (assert_cols; Col).
      assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities); Between.
      }
    apply one_side_transitivity with X2; Col.
    elim (eq_dec_points P X1); intro HPX1; treat_equalities.

      {
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A P) by (assert_cols; Col).
      assert (H3 : Col B X2 P) by (assert_cols; Col).
      assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }

      {
      apply one_side_symmetry; apply l9_17 with P; Between.
      apply one_side_transitivity with Q; Col.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A X1) by (assert_cols; Col).
      assert (H3 : Col Q P X1) by (assert_cols; Col).
      assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities); Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet P B X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_3_2_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_3_2_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_2_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet B X2 P ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q R A B).
  {
  apply l9_8_2 with P.

    {
    assert_diffs; split; Col.
    split; Col.
    split; Col.
    exists X2; assert_cols; split; Col; Between.
    }

    {
    apply one_side_transitivity with X1.

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by (assert_cols; Col).
      assert (H3 : Col P X1 Q) by (assert_cols; Col).
      assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R R) by (assert_cols; Col).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_2_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet X2 P B ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  apply l9_31.

    {
    apply one_side_transitivity with X1.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X2) by (assert_cols; Col).
        assert (H3 : Col B P X2) by (assert_cols; Col).
        assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q Q) by (assert_cols; Col).
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities; Col).
        Between.
        }
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> Q) by (assert_diffs; auto).
      assert (H2 : Col R Q R) by (assert_cols; Col).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    }

    {
    elim (eq_dec_points R X2); intro HRX2; treat_equalities.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; Col).
        assert (H3 : Col B P R) by (assert_cols; Col).
        assert (H := l9_19 R A B P R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; apply HABR; assert_diffs; assert_cols; ColR).
        Between.
        }
      }

      {
      elim (eq_dec_points P X1); intro HPX1; treat_equalities.

        {
        exists X2; split.

          {
          assert_diffs; split; Col.
          split; Col.
          split; try (intro; apply HAQR; assert_cols; ColR).
          exists P; assert_cols; split; Col; Between.
          }

          {
          assert_diffs; split; Col.
          split; Col.
          split; try (intro; apply HAQR; assert_cols; ColR).
          exists R; Col.
          }
        }

        {
        assert (HTS : two_sides R A P X2).
          {
          apply l9_8_2 with Q.

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; Col.
            }

            {
            assert (H1 : R <> A) by (assert_diffs; auto).
            assert (H2 : Col R A X1) by (assert_cols; Col).
            assert (H3 : Col Q P X1) by (assert_cols; Col).
            assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities); Between.
            }
          }
        exists X2; split.

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            destruct HTS as [Hc1 [Hc2 [Hc3 [I [HRAI HPX2I]]]]].
            exists I; split; Col; eBetween.
            }

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; Col.
            }
        }
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_2_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet X2 P B ->
  Bet R X2 Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch R B X2 Q P HCol4 (between_symmetry X2 P B HCol3));
destruct H as [I [HRBI HPQI]].
assert (HQP : Q <> P) by (assert_diffs; Col).
assert (H := l5_2 Q P X1 I HQP (between_symmetry X1 P Q HCol1) HPQI); elim H; clear H; intro HPX1I.

  {
  assert (HTS : two_sides R A Q B).
    {
    apply l9_31.

      {
      apply one_side_symmetry.
      apply one_side_transitivity with X1.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q X2) by (assert_cols; Col).
          assert (H3 : Col B P X2) by (assert_cols; Col).
          assert (H := l9_19 R Q B P X2 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q Q) by (assert_cols; Col).
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
          split; Col.
          assert_diffs; split; Col.
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q R) by (assert_cols; Col).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      }

      {
      elim (eq_dec_points P X1); intro HPX1; treat_equalities.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B R) by (assert_cols; Col).
          assert (H3 : Col A P R) by (assert_cols; Col).
          assert (H := l9_19 R B A P R H1 H2 H3); rewrite H.
          split; Col.
          assert_diffs; split; Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B I) by (assert_cols; Col).
          assert (H3 : Col Q P I) by (assert_cols; Col).
          assert (H := l9_19 R B Q P I H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; assert_diffs; assert_cols; apply HABR; ColR).
          Between.
          }
        }

        {
        apply one_side_transitivity with X1.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B R) by (assert_cols; Col).
          assert (H3 : Col A X1 R) by (assert_cols; Col).
          assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
          split; Col.
          assert_diffs; split; Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B I) by (assert_cols; Col).
          assert (H3 : Col Q X1 I) by (assert_cols; ColR).
          assert (H := l9_19 R B Q X1 I H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          show_distinct R X1; assert_cols; Col.
          split; try (intro; treat_equalities; apply HABR; ColR).
          eBetween.
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; right; split; Col.
  }

  {
  assert (HTS : two_sides R B A Q).
    {
    apply l9_8_2 with X1.

      {
      assert_diffs; split; Col.
      show_distinct R X1; assert_cols; Col.
      split; try (intro; apply HABR; ColR).
      split; Col.
      exists I; assert_cols; split; Col; eBetween.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> B) by (assert_diffs; auto).
      assert (H2 : Col R B R) by (assert_cols; Col).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_2_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet X2 P B ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch R B X2 Q P); destruct H as [I [HQBI HPRI]]; Between.
assert (HTS : two_sides Q B R A).
  {
  elim (eq_dec_points P B); intro HPB; treat_equalities.

    {
    assert_diffs; split; Col.
    split; Col.
    split; Col.
    exists X1; assert_cols; split; Col; Between.
    }

    {
    elim (eq_dec_points P I); intro HPI; treat_equalities.

      {
      assert_diffs; split; Col.
      split; Col.
      split; Col.
      exists X1; assert_cols; split; Between; ColR.
      }

      {
      assert (HTS : two_sides Q B R X1).
        {
        assert (HQX2 : Q <> X2).
          {
          intro; treat_equalities; assert_diffs; assert_cols; apply HNC; ColR.
          }
        apply l9_2; apply l9_8_2 with P.

          {
          assert_diffs; split; Col.
          split; try (intro; assert_cols; apply HNC; ColR).
          split; Col.
          exists I; assert_cols; Col.
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B Q) by (assert_cols; Col).
          assert (H3 : Col P X1 Q) by (assert_cols; ColR).
          assert (H := l9_19 Q B P X1 Q H1 H2 H3); rewrite H.
          split; try (intro; assert_cols; apply HNC; ColR).
          assert_diffs; split; Col.
          split; try (intro; treat_equalities); Between.
          }
        }
      assert_diffs; split; Col.
      split; Col.
      split; Col.
      destruct HTS as [Hc1 [Hc2 [Hc3 [I' [HQBI' HRX1I']]]]].
      exists I'; assert_cols; split; Col; eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I' [HQBI' HQRI']]]]]; clear H1; clear H2; clear H3.
exists I'; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet A X1 R ->
  Bet X2 P B ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_3_2_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_3_2_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_2_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet A X1 R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_3_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_3_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet X1 R A ->
  Bet P B X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : two_sides Q R A B).
  {
  apply l9_2; apply l9_8_2 with P.

    {
    apply l9_8_2 with X1.

      {
      assert_diffs; split; Col.
      show_distinct Q X1; Col.
      split; try (intro; apply HNC; assert_cols; ColR).
      split; Col.
      exists R; Col.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by (assert_cols; Col).
      assert (H3 : Col P X1 Q) by (assert_cols; ColR).
      assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities); Between.
      }
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X2) by (assert_cols; Col).
    assert (H3 : Col P B X2) by (assert_cols; ColR).
    assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; Col).
    split; try (intro; treat_equalities; Col).
    Between.
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_3_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet Q R X2 ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R A Q B).
  {
  elim (eq_dec_points P X1); intro HPX2; treat_equalities.

    {
    apply l9_2; apply l9_8_2 with X2.

      {
      assert_diffs; split; Col.
      show_distinct R X2; assert_cols; try (apply HABR; ColR).
      split; try (intro; apply HAQR; ColR).
      split; Col.
      exists R; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A P) by (assert_cols; Col).
      assert (H3 : Col B X2 P) by (assert_cols; Col).
      assert (H := l9_19 R A B X2 P H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      show_distinct R X2; assert_diffs; assert_cols; try (apply HABR; ColR).
      split; try (intro; treat_equalities; apply HAQR; ColR).
      Between.
      }
    }

    {
    elim (eq_dec_points R X2); intro HRX2; treat_equalities.

      {
      apply l9_8_2 with P.

        {
        assert_diffs; split; Col.
        split; try (intro; assert_cols; apply HABR; ColR).
        split; Col.
        exists R; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        Between.
        }
      }

      {
      assert (HTS1 : two_sides R A X2 Q).
        {
        assert_diffs; split; Col.
        split; try (intro; assert_cols; apply HAQR; ColR).
        split; Col.
        exists R; split; Col; Between.
        }
      apply l9_2; apply l9_8_2 with X2; Col.
      assert (HTS2 : two_sides R A P X2).
        {
        apply l9_8_2 with Q; try (apply l9_2; Col).
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col Q P X1) by (assert_cols; Col).
        assert (H := l9_19 R A Q P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        Between.
        }
      exists P; split; apply l9_2; Col.
      assert_diffs; split; Col.
      split; try (intro; assert_cols; apply HAQR; ColR).
      split; Col.
      destruct HTS2 as [Hc1 [Hc2 [Hc3 [I [HRAI HPX2I]]]]].
      exists I; assert_cols; split; Col; eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
exists I; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_3_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet R X2 Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch A Q R X1 X2); destruct H as [I1 [HQAI1 HX1X2I1]]; Between.
assert (H := outer_pasch Q B P X1 X2); destruct H as [I2 [HQBI2 HX1X2I2]]; Between.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
assert (HX1X2 : X1 <> X2) by (intro; treat_equalities; apply HAQR; assert_cols; ColR).
elim (eq_dec_points I1 I2); intro HI1I2; treat_equalities.

  {
  elim (eq_dec_points Q I1); intro HQI1; treat_equalities.

    {
    elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

      {
      assert (HTS : two_sides Q A R B).
        {
        apply l9_31.

          {
          exists X1; split.

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; split; Col; Between.
            }

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists Q; split; Col; eBetween.
            }
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B X1) by (assert_diffs; assert_cols; ColR).
          assert (H3 : Col A R X1) by (assert_cols; Col).
          assert (H := l9_19 Q B A R X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }
      destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
      exists I; right; left; split; Col.
      }

      {
      exfalso; apply HAQR; assert_cols; ColR.
      }
    }

    {
    exfalso; apply HABQ; assert_cols; ColR.
    }
  }

  {
  elim (eq_dec_points Q I1); intro HQI1; elim (eq_dec_points Q I2); intro HQI2; treat_equalities.

    {
    intuition.
    }

    {
    elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

      {
      assert (HTS : two_sides Q A R B).
        {
        apply l9_31.

          {
          exists X1; split.

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; split; Col; Between.
            }

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists Q; split; Col; eBetween.
            }
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B X1) by (assert_diffs; assert_cols; ColR).
          assert (H3 : Col A R X1) by (assert_cols; Col).
          assert (H := l9_19 Q B A R X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }
      destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
      exists I; right; left; split; Col.
      }

      {
      exfalso; apply HAQR; assert_cols; ColR.
      }
    }

    {
    elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

      {
      assert (HTS : two_sides Q A R B).
        {
        apply l9_31.

          {
          exists X1; split.

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; split; Col; Between.
            }

            {
            assert_diffs; split; Col.
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists Q; split; Col; eBetween.
            }
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B X1) by (assert_diffs; assert_cols; ColR).
          assert (H3 : Col A R X1) by (assert_cols; Col).
          assert (H := l9_19 Q B A R X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          Between.
          }
        }
      destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
      exists I; right; left; split; Col.
      }

      {
      exfalso; apply HAQR; assert_cols; ColR.
      }
    }

    {
    assert (H := l5_2 X1 X2 I1 I2 HX1X2 HX1X2I1 HX1X2I2); elim H; clear H; intro HX2I1I2.

      {
      assert (HTS : two_sides Q A R B).
        {
        apply l9_2; apply l9_8_2 with I2.

          {
          apply l9_2; apply l9_8_2 with X2.

            {
            assert_diffs; split; Col.
            show_distinct Q X2; assert_cols; try (apply HABQ; ColR).
            split; try (intro; apply HABQ; ColR).
            split; try (intro; apply HABQ; ColR).
            exists I1; Col.
            }

            {
            apply one_side_symmetry.
            assert (H1 : Q <> A) by (assert_diffs; auto).
            assert (H2 : Col Q A Q) by (assert_cols; Col).
            assert (H3 : Col R X2 Q) by (assert_cols; Col).
            assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
            split; Col.
            assert_diffs; split; Col.
            show_distinct Q X2; assert_cols; try (apply HABQ; ColR).
            Between.
            }
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A Q) by (assert_cols; Col).
          assert (H3 : Col B I2 Q) by (assert_cols; Col).
          assert (H := l9_19 Q A B I2 Q H1 H2 H3); rewrite H.
          split; Col.
          assert_diffs; split; Col.
          }
        }
      destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
      exists I; right; left; split; Col.
      }

      {
      assert (HTS : two_sides Q B R A).
        {
        apply l9_2; apply l9_8_2 with I1.

          {
          apply l9_2; apply l9_8_2 with X2.

            {
            assert_diffs; split; Col.
            show_distinct Q X2; assert_cols; try (apply HABQ; ColR).
            split; try (intro; apply HBQR; ColR).
            split; try (intro; apply HABQ; ColR).
            exists I2; Col.
            }

            {
            apply one_side_symmetry.
            assert (H1 : Q <> B) by (assert_diffs; auto).
            assert (H2 : Col Q B Q) by (assert_cols; Col).
            assert (H3 : Col R X2 Q) by (assert_cols; Col).
            assert (H := l9_19 Q B R X2 Q H1 H2 H3); rewrite H.
            split; Col.
            assert_diffs; split; Col.
            show_distinct Q X2; assert_cols; try (apply HABQ; ColR).
            Between.
            }
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B Q) by (assert_cols; Col).
          assert (H3 : Col A I1 Q) by (assert_cols; Col).
          assert (H := l9_19 Q B A I1 Q H1 H2 H3); rewrite H.
          split; Col.
          assert_diffs; split; Between.
          }
        }
      destruct HTS as [H1 [H2 [H3 [I [HQBI HRQI]]]]]; clear H1; clear H2; clear H3.
      exists I; right; right; split; Col.
      }
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_3_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet X2 Q R ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R B Q A).
  {
  apply l9_8_2 with X1.

    {
    assert_diffs; split; Col.
    show_distinct R X1; assert_cols; Col.
    split; try (intro; apply HABR; ColR).
    split; Col.
    exists R; Col.
    }

    {
    assert (H := outer_pasch B R X2 P Q); destruct H as [I [HBRI HPQI]]; Between.
    apply one_side_symmetry.
    assert (H1 : R <> B) by (assert_diffs; auto).
    assert (H2 : Col R B I) by (assert_cols; Col).
    assert (H3 : Col Q X1 I) by (assert_diffs; assert_cols; ColR).
    assert (H := l9_19 R B Q X1 I H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; Col).
    show_distinct R X1; assert_cols; Col.
    split; try (intro; apply HABR; ColR).
    assert_diffs; eBetween.
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HRBI HQAI]]]]]; clear H1; clear H2; clear H3.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet X1 R A ->
  Bet B X2 P ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_3_3_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_3_3_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_3_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet X1 R A ->
  Bet X2 P B ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : two_sides Q R A B).
  {
  apply l9_2; apply l9_8_2 with P.

    {
    apply l9_8_2 with X1.

      {
      assert_diffs; split; Col.
      show_distinct Q X1; Col.
      split; try (intro; apply HNC; assert_cols; ColR).
      split; Col.
      exists R; Col.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by (assert_cols; Col).
      assert (H3 : Col P X1 Q) by (assert_cols; ColR).
      assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
      split; Col.
      assert_diffs; split; Col.
      split; try (intro; treat_equalities); Between.
      }
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X2) by (assert_cols; Col).
    assert (H3 : Col P B X2) by (assert_cols; ColR).
    assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; Col).
    split; try (intro; treat_equalities; Col).
    Between.
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet X1 P Q ->
  Bet X1 R A ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_3_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_3_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet X1 P Q ->
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol2 HCol3 HCol4 HCol1.
elim HCol2; clear HCol2; intro HCol2.

  {
  apply coplanar_trans_1_aux_4_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol2; clear HCol2; intro HCol2.

    {
    apply coplanar_trans_1_aux_4_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3_3 with P X1 X2; assumption.
    }
  }
Qed.

End Coplanar_trans_4.