Require Export GeoCoq.Tarski_dev.Coplanar_perm.

Section Coplanar_trans.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma coplanar_trans_1_aux_1_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col P Q X2 ->
  Bet R A X1 ->
  Bet R B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : TS A R B Q).
    {
    apply l9_8_2 with X2.

      {
      assert (R <> X2) by (intro; assert_cols; apply HABR; ColR).
      split; try (intro; assert_cols; apply HABR; ColR).
      split; Col.
      exists X1; assert_cols; Col; Between.
      }

      {
      assert (H1 : A <> R) by (assert_diffs; auto).
      assert (H2 : Col A R R) by Col.
      assert (H3 : Col X2 B R) by (assert_cols; Col).
      assert (H := l9_19 A R X2 B R H1 H2 H3); rewrite H.
      assert (R <> X2) by (intro; assert_cols; apply HABR; ColR).
      split; try (intro; assert_cols; apply HABR; ColR).
      split; try auto.
      split; try (intro; subst; apply HABR; Col).
      Between.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : TS B R A Q).
      {
      apply l9_8_2 with X1.

        {
        assert (R <> X1) by (intro; assert_cols; apply HABR; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; Col.
        exists X2; assert_cols; Col; Between.
        }

        {
        assert (H1 : B <> R) by (assert_diffs; auto).
        assert (H2 : Col B R R) by Col.
        assert (H3 : Col X1 A R) by (assert_cols; Col).
        assert (H := l9_19 B R X1 A R H1 H2 H3); rewrite H.
        assert (R <> X1) by (intro; assert_cols; apply HABR; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; try auto.
        split; try (intro; subst; apply HABR; Col).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (HTS1 : TS Q R X1 X2).
      {
      assert (R <> X1) by (intro; subst; apply HNC; ColR).
      split; try (intro; assert_cols; apply HAQR; ColR).
      assert (R <> X2) by (intro; subst; apply HNC; ColR).
      split; try (intro; assert_cols; apply HBQR; ColR).
      exists Q; Col; Between.
      }
    assert (HTS2 : TS Q R A X2).
      {
      apply l9_8_2 with X1; try assumption.
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R R) by Col.
      assert (H3 : Col X1 A R) by (assert_cols; Col).
      assert (H := l9_19 Q R X1 A R H1 H2 H3); rewrite H.
      assert (R <> X1) by (intro; subst; apply HNC; Col).
      split; try (intro; assert_cols; apply HAQR; ColR).
      split; try auto.
      split; try (intro; subst; apply HABR; Col).
      Between.
      }
    assert (H : TS Q R A B).
      {
      apply l9_2.
      apply l9_8_2 with X2; try (apply l9_2; assumption).
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R R) by Col.
      assert (H3 : Col X2 B R) by (assert_cols; Col).
      assert (H := l9_19 Q R X2 B R H1 H2 H3); rewrite H.
      assert (R <> X2) by (intro; subst; apply HNC; Col).
      split; try (intro; assert_cols; apply HBQR; ColR).
      split; try auto.
      split; try (intro; subst; apply HABR; Col).
      Between.
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_1_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col P Q X2 ->
  Bet R A X1 ->
  Bet B X2 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : TS A R B Q).
    {
    apply l9_8_2 with X2.

      {
      assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; assert_cols; apply HABR; ColR).
      split; Col.
      exists X1; assert_cols; Col; Between.
      }

      {
      assert (H1 : A <> R) by (assert_diffs; auto).
      assert (H2 : Col A R R) by Col.
      assert (H3 : Col X2 B R) by (assert_cols; Col).
      assert (H := l9_19 A R X2 B R H1 H2 H3); rewrite H.
      assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; assert_cols; apply HABR; ColR).
      split; try auto.
      split; try (intro; subst; apply HABR; Col).
      Between.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : TS B R A Q).
      {
      apply l9_8_2 with X1.

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; Col.
        exists X2; assert_cols; Col; Between.
        }

        {
        assert (H1 : B <> R) by (assert_diffs; auto).
        assert (H2 : Col B R R) by Col.
        assert (H3 : Col X1 A R) by (assert_cols; Col).
        assert (H := l9_19 B R X1 A R H1 H2 H3); rewrite H.
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; try auto.
        split; try (intro; subst; apply HABR; Col).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS R Q A B).
      {
      apply l9_31.

        {
        apply one_side_transitivity with X2.

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A X1) by (assert_cols; Col).
          assert (H3 : Col Q X2 X1) by (assert_cols; Col).
          assert (H := l9_19 R A Q X2 X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; subst; apply HAQR; Col).
          assert (R <> X1) by (intro; subst; treat_equalities; apply H1; reflexivity).
          split; try (intro; subst; apply HAQR; ColR).
          Between.
          }

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A R) by Col.
          assert (H3 : Col X2 B R) by (assert_cols; Col).
          assert (H := l9_19 R A X2 B R H1 H2 H3); rewrite H.
          assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
          split; try (intro; assert_cols; apply HABR; ColR).
          split; try auto.
          split; try (intro; subst; apply HABR; Col).
          Between.
          }
        }

        {
        apply one_side_transitivity with X1.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B X2) by (assert_cols; Col).
          assert (H3 : Col Q X1 X2) by (assert_cols; Col).
          assert (H := l9_19 R B Q X1 X2 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; subst; apply HBQR; Col).
          split; try (intro; treat_equalities; assert_cols; apply HAQR; Col).
          Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B R) by Col.
          assert (H3 : Col X1 A R) by (assert_cols; Col).
          assert (H := l9_19 R B X1 A R H1 H2 H3); rewrite H.
          assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
          split; try (intro; assert_cols; apply HABR; ColR).
          split; try auto.
          split; try (intro; subst; apply HABR; Col).
          Between.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_1_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col P Q X2 ->
  Bet R A X1 ->
  Bet X2 R B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : TS R Q A B).
    {
    apply l9_31.

      {
      exists X2; split.

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; Col.
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        exists X1; assert_cols; Col; Between.
        }

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; Col.
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        exists R; assert_cols; Col; Between.
        }
      }

      {
      apply one_side_transitivity with X1.

        {
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B X2) by (assert_cols; Col).
        assert (H3 : Col Q X1 X2) by (assert_cols; Col).
        assert (H := l9_19 R B Q X1 X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; subst; apply HBQR; Col).
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; treat_equalities; assert_cols; apply HABR; ColR).
        Between.
        }

        {
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B R) by Col.
        assert (H3 : Col X1 A R) by (assert_cols; Col).
        assert (H := l9_19 R B X1 A R H1 H2 H3); rewrite H.
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; try auto.
        split; try (intro; subst; apply HABR; Col).
        Between.
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : TS A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; assert_cols; apply HABR; ColR).
        split; Col.
        exists R; assert_cols; Col; Between.
        }

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        assert (H2 : Col A R X1) by (assert_cols; Col).
        assert (H3 : Col X2 Q X1) by (assert_cols; Col).
        assert (H := l9_19 A R X2 Q X1 H1 H2 H3); rewrite H.
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        assert (HX1X2 : X1 <> X2) by (intro; assert_cols; apply HABR; ColR).
        split; auto.
        split; try (intro; treat_equalities; apply HX1X2; reflexivity).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; assert_cols; apply HABR; ColR).
        split; Col.
        exists R; assert_cols; Col; Between.
        }

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        assert (H2 : Col A R X1) by (assert_cols; Col).
        assert (H3 : Col X2 Q X1) by (assert_cols; Col).
        assert (H := l9_19 A R X2 Q X1 H1 H2 H3); rewrite H.
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        assert (HX1X2 : X1 <> X2) by (intro; assert_cols; apply HABR; ColR).
        split; auto.
        split; try (intro; subst; apply HAQR; Col).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_1_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col P Q X2 ->
  Bet A X1 R ->
  Bet B X2 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : TS A R B Q).
    {
    apply l9_8_2 with X2.

      {
      assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; assert_cols; assert_cols; apply HABR; ColR).
      split; Col.
      exists X1; assert_cols; split; Col; Between.
      }

      {
      assert (H1 : A <> R) by (assert_diffs; auto).
      assert (H2 : Col A R R) by Col.
      assert (H3 : Col X2 B R) by (assert_cols; Col).
      assert (H := l9_19 A R X2 B R H1 H2 H3); rewrite H.
      assert (HRX2 : R <> X2) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; assert_cols; apply HABR; ColR).
      assert (HRX1 : R <> X1) by (intro; assert_cols; apply HNC; ColR).
      assert (HX1X2 : X1 <> X2) by (intro; assert_cols; apply HABR; ColR).
      split; auto.
      split; try (intro; treat_equalities; apply HRX2; reflexivity).
      Between.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : TS B R A Q).
      {
      apply l9_8_2 with X1.

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; assert_cols; apply HABR; ColR).
        split; Col.
        exists X2; assert_cols; split; Col; Between.
        }

        {
        assert (H1 : B <> R) by (assert_diffs; auto).
        assert (H2 : Col B R R) by Col.
        assert (H3 : Col X1 A R) by (assert_cols; Col).
        assert (H := l9_19 B R X1 A R H1 H2 H3); rewrite H.
        assert (HRX1 : R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        assert (HRX2 : R <> X2) by (intro; assert_cols; apply HNC; ColR).
        assert (HX1X2 : X1 <> X2) by (intro; assert_cols; apply HABR; ColR).
        split; auto.
        split; try (intro; treat_equalities; apply HRX1; reflexivity).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS R Q A B).
      {
      apply l9_31.

        {
        apply one_side_transitivity with X2.

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A X1) by (assert_cols; Col).
          assert (H3 : Col Q X2 X1) by (assert_cols; Col).
          assert (H := l9_19 R A Q X2 X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; subst; apply HAQR; Col).
          assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
          split; try (intro; treat_equalities; assert_cols; apply HABR; ColR).
          Between.
          }

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A R) by Col.
          assert (H3 : Col X2 B R) by (assert_cols; Col).
          assert (H := l9_19 R A X2 B R H1 H2 H3); rewrite H.
          assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
          split; try (intro; assert_cols; apply HABR; ColR).
          split; try auto.
          split; try (intro; subst; apply HABR; Col).
          Between.
          }
        }

        {
        apply one_side_transitivity with X1.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B X2) by (assert_cols; Col).
          assert (H3 : Col Q X1 X2) by (assert_cols; Col).
          assert (H := l9_19 R B Q X1 X2 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; subst; apply HBQR; Col).
          assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
          split; try (intro; treat_equalities; assert_cols; apply HABR; ColR).
          Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B R) by Col.
          assert (H3 : Col X1 A R) by (assert_cols; Col).
          assert (H := l9_19 R B X1 A R H1 H2 H3); rewrite H.
          assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
          split; try (intro; assert_cols; apply HABR; ColR).
          split; try auto.
          split; try (intro; subst; apply HABR; Col).
          Between.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_1_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col P Q X2 ->
  Bet A X1 R ->
  Bet X2 R B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : TS R Q A B).
    {
    apply l9_31.

      {
      exists X2; split.

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; Col.
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        exists X1; assert_cols; Col; Between.
        }

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
        split; Col.
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        try (intro; assert_cols; apply HABR; ColR).
        exists R; assert_cols; Col; Between.
        }
      }

      {
      apply one_side_transitivity with X1.

        {
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B X2) by (assert_cols; Col).
        assert (H3 : Col Q X1 X2) by (assert_cols; Col).
        assert (H := l9_19 R B Q X1 X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; subst; apply HBQR; Col).
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; treat_equalities; assert_cols; apply HABR; ColR).
        Between.
        }

        {
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B R) by Col.
        assert (H3 : Col X1 A R) by (assert_cols; Col).
        assert (H := l9_19 R B X1 A R H1 H2 H3); rewrite H.
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; try auto.
        split; try (intro; subst; apply HABR; Col).
        Between.
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : TS A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; assert_cols; apply HABR; ColR).
        split; Col.
        exists R; assert_cols; split; Col; Between.
        }

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        assert (H2 : Col A R X1) by Col.
        assert (H3 : Col X2 Q X1) by (assert_cols; Col).
        assert (H := l9_19 A R X2 Q X1 H1 H2 H3); rewrite H.
        assert (HRX2 : R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        assert (HRX1 : R <> X1) by (intro; assert_cols; apply HNC; ColR).
        assert (HX1X2 : X1 <> X2) by (intro; assert_cols; apply HABR; ColR).
        split; auto.
        split; try (intro; subst; assert_cols; apply HAQR; Col).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; assert_cols; apply HABR; ColR).
        split; Col.
        exists R; assert_cols; split; Col; Between.
        }

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        assert (H2 : Col A R X1) by Col.
        assert (H3 : Col X2 Q X1) by (assert_cols; Col).
        assert (H := l9_19 A R X2 Q X1 H1 H2 H3); rewrite H.
        assert (HRX2 : R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        assert (HRX1 : R <> X1) by (intro; assert_cols; apply HNC; ColR).
        assert (HX1X2 : X1 <> X2) by (intro; assert_cols; apply HABR; ColR).
        split; auto.
        split; try (intro; subst; assert_cols; apply HAQR; Col).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_1_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col P Q X2 ->
  Bet X1 R A ->
  Bet X2 R B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : TS B R Q A).
    {
    apply l9_8_2 with X1.

      {
      assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; assert_cols; apply HABR; ColR).
      split; Col.
      exists R; assert_cols; split; Col; Between.
      }

      {
      assert (H1 : B <> R) by (assert_diffs; auto).
      assert (H2 : Col B R X2) by (assert_cols; Col).
      assert (H3 : Col X1 Q X2) by (assert_cols; Col).
      assert (H := l9_19 B R X1 Q X2 H1 H2 H3); rewrite H.
      assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; assert_cols; apply HABR; ColR).
      split; try (intro; assert_cols; apply HABR; ColR).
      split; try (intro; subst; apply HBQR; Col).
      Between.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : TS A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; Col.
        exists R; assert_cols; split; Col; Between.
        }

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        assert (H2 : Col A R X1) by (assert_cols; Col).
        assert (H3 : Col X2 Q X1) by (assert_cols; Col).
        assert (H := l9_19 A R X2 Q X1 H1 H2 H3); rewrite H.
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; try (intro; subst; apply HAQR; Col).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; Col.
        exists R; assert_cols; split; Col; Between.
        }

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        assert (H2 : Col A R X1) by (assert_cols; Col).
        assert (H3 : Col X2 Q X1) by (assert_cols; Col).
        assert (H := l9_19 A R X2 Q X1 H1 H2 H3); rewrite H.
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; try (intro; assert_cols; apply HABR; ColR).
        split; try (intro; subst; apply HAQR; Col).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col R A X1 ->
  Col P Q X2 ->
  Col R B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim HCol2; clear HCol2; intro HCol2; elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_1_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_1_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_1_1_3 with P X1 X2; assumption.
    }
  }

  {
  elim HCol2; clear HCol2; intro HCol2.

    {
    assert (H : Coplanar Q R B A) by (apply coplanar_trans_1_aux_1_1_2 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (H : Coplanar Q R B A) by (apply coplanar_trans_1_aux_1_1_3 with P X2 X1; Col; Between); Cop.
    }
  }

  {
  elim HCol2; clear HCol2; intro HCol2; elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_1_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_1_2_3 with P X1 X2; assumption.
    }

    {
    assert (H : Coplanar Q R B A) by (apply coplanar_trans_1_aux_1_2_3 with P X2 X1; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_1_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_1_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet P B X2 ->
  Bet Q X1 X2 ->
  Bet R X1 X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HQX1X2.
apply between_symmetry in HRX1X2.
assert (H : X2 <> X1) by auto; assert (HQRX1 := l5_2 X2 X1 Q R H HQX1X2 HRX1X2); clear H.
elim HQRX1; clear HQRX1; intro HQRX1.

  {
  apply between_symmetry in HQX1X2.
  assert (H := inner_pasch P Q X2 B X1 HCol3 HQX1X2); destruct H as [U [HBUQ HPUX1]].
  apply between_symmetry in HPUX1.
  assert (H := l5_3 P A U X1 HCol1 HPUX1).
  elim H; clear H; intro HAPU.

    {
    assert (H : TS Q A R B).
      {
      apply l9_31.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R X1) by (assert_cols; Col).
          assert (H3 : Col A P X1) by (assert_cols; Col).
          assert (H := l9_19 Q R A P X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try assumption.
          split; try (intro; treat_equalities; intuition).
          Between.
          }

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R X2) by (assert_cols; Col).
          assert (H3 : Col P B X2) by (assert_cols; Col).
          assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
          assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; Between.
          }
        }

        {
        exists X2; split.

          {
          apply l9_8_2 with P.

            {
            assert (Q <> B) by (assert_diffs; auto).
            assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
            assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
            split; Col.
            split; try (intro; assert_cols; apply HBQR; ColR).
            exists B; split; Col; eBetween.
            }

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            assert (H2 : Col Q B U) by (assert_cols; Col).
            assert (H3 : Col P A U) by (assert_cols; Col).
            assert (H := l9_19 Q B P A U H1 H2 H3); rewrite H.
            assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
            assert (HBPQ : ~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
            split; Col.
            split; try (intro; treat_equalities; apply HBPQ; Col).
            split; try (intro; subst; apply HABQ; Col).
            Between.
            }
          }

          {
          assert (Q <> B) by (assert_diffs; auto).
          assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists Q; split; Col; eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS B Q R A).
      {
      apply l9_8_2 with P.

        {
        assert (H1 : B <> Q) by (assert_diffs; auto).
        assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
        assert (HBPQ : ~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
        split; Col.
        split; Col.
        exists U; split; Col; Between.
        }

        {
        exists X2; split.

          {
          assert (B <> Q) by (assert_diffs; auto).
          assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists B; split; Col; eBetween.
          }

          {
          assert (B <> Q) by (assert_diffs; auto).
          assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists Q; split; Col; eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  apply between_symmetry in HRX1X2.
  assert (H := inner_pasch P R X2 B X1 HCol3 HRX1X2); destruct H as [U [HBUR HPUX1]].
  apply between_symmetry in HPUX1.
  assert (H := l5_3 P A U X1 HCol1 HPUX1).
  elim H; clear H; intro HAPU.

    {
    assert (H : TS R A Q B).
      {
      apply l9_31.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q X1) by (assert_cols; Col).
          assert (H3 : Col A P X1) by (assert_cols; Col).
          assert (H := l9_19 R Q A P X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try assumption.
          split; try (intro; treat_equalities; intuition).
          Between.
          }

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q X2) by (assert_cols; Col).
          assert (H3 : Col P B X2) by (assert_cols; Col).
          assert (H := l9_19 R Q P B X2 H1 H2 H3); rewrite H.
          assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; Between.
          }
        }

        {
        exists X2; split.

          {
          apply l9_8_2 with P.

            {
            assert (R <> B) by (assert_diffs; auto).
            assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
            assert (~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
            split; Col.
            split; try (intro; assert_cols; apply HBQR; ColR).
            exists B; split; Col; eBetween.
            }

            {
            assert (H1 : R <> B) by (assert_diffs; auto).
            assert (H2 : Col R B U) by (assert_cols; Col).
            assert (H3 : Col P A U) by (assert_cols; Col).
            assert (H := l9_19 R B P A U H1 H2 H3); rewrite H.
            assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
            assert (HBPR : ~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
            split; Col.
            split; try (intro; treat_equalities; apply HABP; Col).
            split; try (intro; treat_equalities; apply HABR; Col).
            Between.
            }
          }

          {
          assert (R <> B) by (assert_diffs; auto).
          assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists R; split; Col; eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS B R Q A).
      {
      apply l9_8_2 with P.

        {
        assert (H1 : B <> R) by (assert_diffs; auto).
        assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
        assert (HBPR : ~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
        split; Col.
        split; Col.
        exists U; split; Col; Between.
        }

        {
        exists X2; split.

          {
          assert (B <> R) by (assert_diffs; auto).
          assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists B; split; Col; eBetween.
          }

          {
          assert (B <> R) by (assert_diffs; auto).
          assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists R; split; Col; eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_1_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet P B X2 ->
  Bet Q X1 X2 ->
  Bet X1 X2 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (H := outer_pasch X1 P X2 R B HRX1X2 HCol3); destruct H as [U [HPUX1 HRBU]].
apply between_symmetry in HPUX1.
assert (H := l5_3 P A U X1 HCol1 HPUX1).
elim H; clear H; intro HAPU.

  {
  assert (H : TS B R Q A).
    {
    apply l9_8_2 with X1.

      {
      assert (H1 : B <> R) by (assert_diffs; auto).
      assert (HRX1 : R <> X1) by (intro; treat_equalities; intuition).
      split; try (intro; apply HBQR; ColR).
      split; Col.
      exists U; split; Col; eBetween.
      }

      {
      assert (H1 : B <> R) by (assert_diffs; auto).
      assert (H2 : Col B R R) by Col.
      assert (H3 : Col X1 Q R) by (assert_cols; Col).
      assert (H := l9_19 B R X1 Q R H1 H2 H3); rewrite H.
      assert (HRX2 : R <> X1) by (intro; treat_equalities; intuition).
      split; try (intro; apply HBQR; ColR).
      split; try auto.
      split; assert_diffs; eBetween.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  assert (H : TS R A Q B).
    {
    apply l9_31.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X1) by (assert_cols; Col).
        assert (H3 : Col A P X1) by (assert_cols; Col).
        assert (H := l9_19 R Q A P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try assumption.
        split; try (intro; treat_equalities; intuition).
        Between.
        }

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X2) by (assert_cols; Col).
        assert (H3 : Col P B X2) by (assert_cols; Col).
        assert (H := l9_19 R Q P B X2 H1 H2 H3); rewrite H.
        assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
        assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
        split; Col.
        split; try (intro; treat_equalities; intuition).
        split; Between.
        }
      }

      {
      apply one_side_transitivity with X1.

        {
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B U) by (assert_cols; Col).
        assert (HBet : Bet U A X1) by eBetween.
        assert (H3 : Col A X1 U) by (assert_cols; Col).
        assert (H := l9_19 R B A X1 U H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        Between.
        }

        {
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B R) by Col.
        assert (H3 : Col X1 Q R) by (assert_cols; Col).
        assert (H := l9_19 R B X1 Q R H1 H2 H3); rewrite H.
        assert (HRX1 : R <> X1) by (intro; treat_equalities; intuition).
        split; try (intro; apply HBQR; ColR).
        split; try auto.
        split; assert_diffs; eBetween.
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_1_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet P B X2 ->
  Bet Q X1 X2 ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
elim (eq_dec_points R X1); intro HRX1; elim (eq_dec_points R X2); intro HRX2; treat_equalities.

  {
  subst; intuition.
  }

  {
  assert (H := inner_pasch P Q X2 B R HCol3 HQX1X2); destruct H as [U [HBUQ HPUR]].
  exists U; right; right.
  assert (P <> R) by (intro; treat_equalities; intuition).
  split; assert_cols; ColR.
  }

  {
  apply between_symmetry in HQX1X2.
  assert (H := outer_pasch R P X1 Q A HQX1X2 HCol1); destruct H as [U [HPUR HQAU]].
  exists U; right; left.
  assert (P <> R) by (intro; treat_equalities; intuition).
  split; assert_cols; ColR.
  }

  {
  assert (H : TS R A Q B).

    {
    apply l9_31.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X1) by (assert_cols; Col).
        assert (H3 : Col A P X1) by (assert_cols; Col).
        assert (H := l9_19 R Q A P X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try assumption.
        split; try (intro; treat_equalities; intuition).
        Between.
        }

        {
        assert (H1 : R <> Q) by (assert_diffs; auto).
        assert (H2 : Col R Q X2) by (assert_cols; Col).
        assert (H3 : Col P B X2) by (assert_cols; Col).
        assert (H := l9_19 R Q P B X2 H1 H2 H3); rewrite H.
        assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
        assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
        split; Col.
        split; try (intro; treat_equalities; intuition).
        split; Between.
        }
      }

      {
      apply one_side_transitivity with X1.

        {
        apply one_side_symmetry; apply l9_17 with P; Between.
        exists X2; split.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try (intro; apply HBQR; ColR).
          split; try (intro; apply HBQR; ColR).
          exists R; split; Col; Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; try (intro; apply HBQR; ColR).
          exists B; split; Col; Between.
          }
        }

        {
        exists X2; split.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try (intro; apply HBQR; ColR).
          split; try (intro; apply HBQR; ColR).
          exists R; split; Col; Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try (intro; apply HBQR; ColR).
          split; try (intro; apply HBQR; ColR).
          exists R; split; Col; eBetween.
          }
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_1_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet P B X2 ->
  Bet X2 Q X1 ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (H := l5_3 X2 Q R X1 HQX1X2 HRX1X2).
apply between_symmetry in HQX1X2.
apply between_symmetry in HRX1X2.
assert (H' := l5_3 X1 Q R X2 HQX1X2 HRX1X2).
elim H; clear H; intro HQRX2; elim H'; clear H'; intro HQRX1.

  {
  assert (H : Bet X1 R Q) by eBetween.
  apply between_symmetry in HQRX1.
  apply between_symmetry in H.
  assert (H' := between_equality R Q X1 HQRX1 H); treat_equalities; exfalso; apply HNC; Col.
  }

  {
  elim (eq_dec_points R X1); intro HRX1; elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    subst; intuition.
    }

    {
    apply between_symmetry in HCol1.
    apply between_symmetry in HCol3.
    assert (H := inner_pasch R X2 P A B HCol1 HCol3); destruct H as [U [HAUX2 HBUR]].
    apply between_symmetry in HQRX2.
    assert (H := inner_pasch A R X2 U Q HAUX2 HQRX2); destruct H as [V [RVU HAVQ]].
    exists V; right; left.
    assert (R <> U) by (intro; treat_equalities; assert_cols; apply HAQR; ColR).
    assert_cols; split; ColR.
    }

    {
    exfalso; apply HNC; Col.
    }

    {
    assert (H : TS R B Q A).

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
          split; try (intro; treat_equalities; intuition).
          split; Between.
          intro; treat_equalities; intuition.
          }

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q X1) by (assert_cols; Col).
          assert (H3 : Col P A X1) by (assert_cols; Col).
          assert (H := l9_19 R Q P A X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; Between.
          }
        }

        {
        exists X1; split.

          {
          apply l9_8_2 with P.

            {
            assert (H1 : R <> A) by (assert_diffs; auto).
            split; try (intro; apply HRX1; apply l6_21 with Q R P A; assert_diffs; Col).
            split; try (intro; apply HAQR; ColR).
            exists A; split; Col; Between.
            }

            {
            apply l9_17 with X2; Between.
            exists X1; split.

              {
              assert (H1 : R <> A) by (assert_diffs; auto).
              split; try (intro; apply HRX1; apply l6_21 with Q R P A; assert_diffs; Col).
              split; try (intro; apply HAQR; ColR).
              exists A; split; Col; Between.
              }

              {
              assert (H1 : R <> A) by (assert_diffs; auto).
              split; try (intro; apply HAQR; ColR).
              split; try (intro; apply HAQR; ColR).
              exists R; split; Col; Between.
              }
            }
          }

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          split; try (intro; apply HAQR; ColR).
          split; try (intro; apply HAQR; ColR).
          exists R; split; Col; eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  elim (eq_dec_points Q X1); intro HQX1; elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

    {
    subst; intuition.
    }

    {
    apply between_symmetry in HCol1.
    apply between_symmetry in HCol3.
    assert (H := inner_pasch X2 Q P B A HCol3 HCol1); destruct H as [U [HBUQ HAUX2]].
    apply between_symmetry in HQRX2.
    assert (H := inner_pasch A Q X2 U R HAUX2 HQRX2); destruct H as [V [QVU HAVR]].
    exists V; right; right.
    assert (Q <> U) by (intro; treat_equalities; assert_cols; apply HAQR; ColR).
    assert_cols; split; ColR.
    }

    {
    exfalso; apply HNC; Col.
    }

    {
    assert (H : TS Q B R A).

      {
      apply l9_31.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R X2) by (assert_cols; Col).
          assert (H3 : Col B P X2) by (assert_cols; Col).
          assert (H := l9_19 Q R B P X2 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; Between.
          intro; treat_equalities; intuition.
          }

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R X1) by (assert_cols; Col).
          assert (H3 : Col P A X1) by (assert_cols; Col).
          assert (H := l9_19 Q R P A X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; Between.
          }
        }

        {
        exists X1; split.

          {
          apply l9_8_2 with P.

            {
            assert (H1 : Q <> A) by (assert_diffs; auto).
            split; try (intro; apply HQX1; apply l6_21 with Q R P A; assert_diffs; Col).
            split; try (intro; apply HAQR; ColR).
            exists A; split; Col; Between.
            }

            {
            apply l9_17 with X2; Between.
            exists X1; split.

              {
              assert (H1 : Q <> A) by (assert_diffs; auto).
              split; try (intro; apply HQX1; apply l6_21 with Q R P A; assert_diffs; Col).
              split; try (intro; apply HAQR; ColR).
              exists A; split; Col; Between.
              }

              {
              assert (H1 : Q <> A) by (assert_diffs; auto).
              split; try (intro; apply HAQR; ColR).
              split; try (intro; apply HAQR; ColR).
              exists Q; split; Col; Between.
              }
            }
          }

          {
          assert (H1 : Q <> A) by (assert_diffs; auto).
          split; try (intro; apply HAQR; ColR).
          split; try (intro; apply HAQR; ColR).
          exists Q; split; Col; Between.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  assert (H : Bet X1 Q R) by eBetween.
  apply between_symmetry in HQRX1.
  apply between_symmetry in H.
  assert (H' := between_equality R Q X1 H HQRX1); treat_equalities; exfalso; apply HNC; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet P B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2 HCol2 HCol4 HCol1 HCol3.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
assert (HRX1X2 : Col R X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

  {
  apply coplanar_trans_1_aux_2_1_1_1_1 with P X1 X2; assumption.
  }

  {
  elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    apply coplanar_trans_1_aux_2_1_1_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_2_1_1_1_3 with P X1 X2; assumption.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_1_1_2 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar R Q A B) by (apply coplanar_trans_1_aux_2_1_1_1_3 with P X1 X2; Col; Between); Cop.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_1_1_1 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_1_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar R Q B A) by (apply coplanar_trans_1_aux_2_1_1_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_2_1_1_2_2 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet B X2 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2 HCol2 HCol4 HCol1 HCol3.
assert (H : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    split; Col.
    split; Col.
    exists X2; split; Col; Between.
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X1) by (assert_cols; Col).
    assert (H3 : Col P A X1) by (assert_cols; Col).
    assert (H := l9_19 Q R P A X1 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; Between.
    }
  }
destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
exists I; assert_cols; Col5.
Qed.

Lemma coplanar_trans_1_aux_2_1_3_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet X2 P B ->
  Bet Q X1 X2 ->
  Bet R X1 X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HOS : OS Q R A B).
  {
  apply one_side_transitivity with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X1) by (assert_cols; Col).
    assert (H3 : Col A P X1) by (assert_cols; Col).
    assert (H := l9_19 Q R A P X1 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; try (intro; treat_equalities; apply HAX1; reflexivity).
    Between.
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X2) by (assert_cols; Col).
    assert (H3 : Col P B X2) by (assert_cols; Col).
    assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; Between.
    }
  }
apply between_symmetry in HQX1X2.
apply between_symmetry in HRX1X2.
assert (H : X2 <> X1) by auto; assert (HQRX1 := l5_2 X2 X1 Q R H HQX1X2 HRX1X2); clear H.
elim HQRX1; clear HQRX1; intro HQRX1.

  {
  assert (H : TS Q B R A).
    {
    apply l9_31; apply one_side_symmetry; try assumption.
    exists X2; split.

      {
      assert (H1 : Q <> A) by (assert_diffs; auto).
      split; Col.
      assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      exists Q; split; Col; eBetween.
      }

      {
      assert (H := outer_pasch X2 P X1 Q A HQX1X2 HCol1); destruct H as [U [HPUX2 HQAU]].
      assert (H1 : Q <> A) by (assert_diffs; auto).
      split; Col.
      assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      exists U; split; Col; eBetween.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  assert (H : TS R B Q A).
    {
    apply l9_31; apply one_side_symmetry; apply invert_one_side; try assumption.
    exists X2; split.

      {
      assert (H1 : A <> R) by (assert_diffs; auto).
      split; Col.
      assert (R <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      exists R; split; Col; eBetween.
      }

      {
      assert (H := outer_pasch X2 P X1 R A HRX1X2 HCol1); destruct H as [U [HPUX2 HRAU]].
      assert (H1 : A <> R) by (assert_diffs; auto).
      split; Col.
      assert (R <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      exists U; split; Col; eBetween.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_3_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet X2 P B ->
  Bet Q X1 X2 ->
  Bet X1 X2 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (H : TS A Q R B).
  {
  apply l9_8_2 with X2.

    {
    apply between_symmetry in HQX1X2.
    assert (H := outer_pasch X2 P X1 Q A HQX1X2 HCol1); destruct H as [U [HPUX2 HQAU]].
    assert (H1 : A <> Q) by (assert_diffs; auto).
    assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
    split; try (intro; apply HAQR; ColR).
    split; Col.
    exists U; split; Col; eBetween.
    }

    {
    assert (H1 : A <> Q) by (assert_diffs; auto).
    assert (H2 : Col A Q Q) by (assert_cols; Col).
    assert (H3 : Col X2 R Q) by (assert_cols; Col).
    assert (H := l9_19 A Q X2 R Q H1 H2 H3); rewrite H.
    assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
    split; try (intro; apply HAQR; ColR).
    split; auto.
    split; try (intro; treat_equalities; intuition).
    eBetween.
    }
  }
destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
exists I; assert_cols; Col5.
Qed.

Lemma coplanar_trans_1_aux_2_1_3_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet X2 P B ->
  Bet Q X1 X2 ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (H : TS A Q R B).
  {
  apply l9_8_2 with X2.

    {
    apply between_symmetry in HQX1X2.
    assert (H := outer_pasch X2 P X1 Q A HQX1X2 HCol1); destruct H as [U [HPUX2 HQAU]].
    assert (H1 : A <> Q) by (assert_diffs; auto).
    assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
    split; try (intro; apply HAQR; ColR).
    split; Col.
    exists U; split; Col; eBetween.
    }

    {
    assert (H1 : A <> Q) by (assert_diffs; auto).
    assert (H2 : Col A Q Q) by (assert_cols; Col).
    assert (H3 : Col X2 R Q) by (assert_cols; Col).
    assert (H := l9_19 A Q X2 R Q H1 H2 H3); rewrite H.
    assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
    split; try (intro; apply HAQR; ColR).
    split; auto.
    split; try (intro; treat_equalities; intuition).
    eBetween.
    }
  }
destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
exists I; assert_cols; Col5.
Qed.

Lemma coplanar_trans_1_aux_2_1_3_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet X2 P B ->
  Bet X1 X2 Q ->
  Bet X1 X2 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HQRX2 := l5_2 X1 X2 Q R HX1X2 HQX1X2 HRX1X2).
assert (HOS : OS Q R A B).
  {
  apply one_side_transitivity with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X1) by (assert_cols; Col).
    assert (H3 : Col A P X1) by (assert_cols; Col).
    assert (H := l9_19 Q R A P X1 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; try (intro; treat_equalities; apply HAX1; reflexivity).
    Between.
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X2) by (assert_cols; Col).
    assert (H3 : Col P B X2) by (assert_cols; Col).
    assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; Between.
    }
  }
elim HQRX2; clear HQRX2; intro HQRX2.

  {
  elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

    {
    apply between_symmetry in HRX1X2.
    assert (H := inner_pasch P R X1 A Q HCol1 HRX1X2); destruct H as [U [HAUR HPUQ]].
    exists U; right; right.
    assert (P <> Q) by (assert_diffs; auto).
    assert_cols; split; ColR.
    }

    {
    assert (H : TS Q B R A).
      {
      apply l9_31; apply one_side_symmetry; try assumption.
      exists X2; split.

        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        split; Col.
        split; try (intro; apply HAQR; ColR).
        exists Q; split; Col; eBetween.
        }

        {
        apply between_symmetry in HQX1X2.
        assert (H := inner_pasch P Q X1 A X2 HCol1 HQX1X2); destruct H as [U [HAUQ HPUX2]].
        assert (H1 : Q <> A) by (assert_diffs; auto).
        split; Col.
        split; try (intro; apply HAQR; ColR).
        exists U; split; Col; eBetween.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    apply between_symmetry in HQX1X2.
    assert (H := inner_pasch P Q X1 A R HCol1 HQX1X2); destruct H as [U [HAUQ HPUR]].
    exists U; right; left.
    assert (P <> R) by (assert_diffs; auto).
    assert_cols; split; ColR.
    }

    {
    assert (H : TS R B Q A).
      {
      apply l9_31; apply one_side_symmetry; apply invert_one_side; try assumption.
      exists X2; split.

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        split; Col.
        split; try (intro; apply HAQR; ColR).
        exists R; split; Col; eBetween.
        }

        {
        apply between_symmetry in HRX1X2.
        assert (H := inner_pasch P R X1 A X2 HCol1 HRX1X2); destruct H as [U [HAUR HPUX2]].
        assert (H1 : A <> R) by (assert_diffs; auto).
        split; Col.
        split; try (intro; apply HAQR; ColR).
        exists U; split; Col; eBetween.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_3_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet X2 P B ->
  Bet X1 X2 Q ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HOS : OS Q R A B).
  {
  apply one_side_transitivity with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X1) by (assert_cols; Col).
    assert (H3 : Col A P X1) by (assert_cols; Col).
    assert (H := l9_19 Q R A P X1 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; try (intro; treat_equalities; apply HAX1; reflexivity).
    Between.
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X2) by (assert_cols; Col).
    assert (H3 : Col P B X2) by (assert_cols; Col).
    assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; Between.
    }
  }
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  assert (H := inner_pasch P Q X1 A R HCol1 HRX1X2); destruct H as [U [HAUQ HPUR]].
  apply between_symmetry in HCol3.
  assert (H := outer_pasch B R P Q U HCol3 HPUR); destruct H as [V [HBVR HQUV]].
  exists V; right; left.
  assert (Q <> U) by (intro; treat_equalities; assert_cols; apply HNC; Col).
  assert_cols; split; ColR.
  }

  {
  assert (H : TS Q A B R).
    {
    apply l9_31; try assumption.
    apply one_side_transitivity with P.

      {
      apply between_symmetry in HQX1X2.
      apply between_symmetry in HCol3.
      assert (H := outer_pasch Q B X2 X1 P HQX1X2 HCol3); destruct H as [U [HBUQ HUPX1]].
      assert (H1 : Q <> B) by (assert_diffs; auto).
      assert (H2 : Col Q B U) by (assert_cols; Col).
      assert (H' : P <> X1) by (intro; treat_equalities; apply HAX1; reflexivity).
      assert (H3 : Col A P U) by (assert_cols; ColR).
      assert (H := l9_19 Q B A P U H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; apply HABQ; Col).
      split; try (intro; treat_equalities; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
      eBetween.
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : Q <> B) by (assert_diffs; auto).
        assert (H2 : Col Q B B) by (assert_cols; Col).
        assert (H3 : Col P X2 B) by (assert_cols; Col).
        assert (H := l9_19 Q B P X2 B H1 H2 H3); rewrite H.
        split; try (intro; treat_equalities; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
        split; try (intro; treat_equalities; apply HABP; Col).
        split; Between.
        }

        {
        assert (H1 : Q <> B) by (assert_diffs; auto).
        assert (H2 : Col Q B Q) by (assert_cols; Col).
        assert (H3 : Col X2 R Q) by (assert_cols; Col).
        assert (H := l9_19 Q B X2 R Q H1 H2 H3); rewrite H.
        split; try (intro; apply HBQR; ColR).
        split; auto.
        split; try (intro; assert_diffs; intuition).
        eBetween.
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_3_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet X2 P B ->
  Bet X2 Q X1 ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HOS : OS Q R A B).
  {
  apply one_side_transitivity with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X1) by (assert_cols; Col).
    assert (H3 : Col A P X1) by (assert_cols; Col).
    assert (H := l9_19 Q R A P X1 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; try (intro; treat_equalities; apply HAX1; reflexivity).
    Between.
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X2) by (assert_cols; Col).
    assert (H3 : Col P B X2) by (assert_cols; Col).
    assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; Between.
    }
  }
assert (H := l5_3 X2 Q R X1 HQX1X2 HRX1X2).
apply between_symmetry in HQX1X2.
apply between_symmetry in HRX1X2.
assert (H' := l5_3 X1 Q R X2 HQX1X2 HRX1X2).
elim H'; clear H'; intro HQRX1; elim H; clear H; intro HQRX2.

  {
  assert (H : Bet X1 R Q) by eBetween.
  apply between_symmetry in HQRX1.
  apply between_symmetry in H.
  assert (H' := between_equality R Q X1 HQRX1 H); treat_equalities; exfalso; apply HNC; Col.
  }

  {
  apply between_symmetry in HCol3.
  assert (H := inner_pasch B X1 X2 P Q HCol3 HQX1X2); destruct H as [U [HPUX1 HBUQ]].
  assert (H := l5_3 P A U X1 HCol1 HPUX1).
  elim H; clear H; intro HAPU.

    {
    elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

      {
      exfalso; apply HNC; Col.
      }

      {
      assert (H : TS Q A B R).
        {
        apply l9_31; try assumption.
        apply one_side_transitivity with P.

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B U) by (assert_cols; Col).
          assert (H3 : Col A P U) by (assert_cols; Col).
          assert (H := l9_19 Q B A P U H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; apply HABQ; ColR).
          split; try (intro; treat_equalities; apply HABP; Col).
          Between.
          }

          {
          apply one_side_transitivity with X2.

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            assert (H2 : Col Q B B) by (assert_cols; Col).
            assert (H3 : Col P X2 B) by (assert_cols; Col).
            assert (H := l9_19 Q B P X2 B H1 H2 H3); rewrite H.
            split; try (intro; treat_equalities; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
            split; try (intro; treat_equalities; apply HABP; Col).
            split; Between.
            }

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            assert (H2 : Col Q B Q) by (assert_cols; Col).
            assert (H3 : Col X2 R Q) by (assert_cols; Col).
            assert (H := l9_19 Q B X2 R Q H1 H2 H3); rewrite H.
            split; try (intro; apply HBQR; ColR).
            split; try auto.
            split; try (intro; treat_equalities; intuition).
            Between.
            }
          }
        }
      destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
      exists I; assert_cols; Col5.
      }
    }

    {
    elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

      {
      apply between_symmetry in HQRX2.
      assert (H := inner_pasch B Q X2 P R HCol3 HQRX2); destruct H as [V [HPVQ HBVR]].
      exists V; right; left.
      assert_diffs; assert_cols; split; ColR.
      }

      {
      assert (H : TS Q B A R).
        {
        apply l9_8_2 with X1.

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          split; try (intro; apply HBQR; ColR).
          split; Col.
          exists Q; split; Col; Between.
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B U) by (assert_cols; Col).
          assert (H' : P <> X1) by (intro; treat_equalities; apply HAX1; reflexivity).
          assert (H3 : Col X1 A U) by (assert_cols; ColR).
          assert (H := l9_19 Q B X1 A U H1 H2 H3); rewrite H.
          split; try (intro; apply HBQR; ColR).
          split; try (intro; treat_equalities; apply HBQR; ColR).
          split; try (intro; treat_equalities; apply HABQ; Col).
          eBetween.
          }
        }
      destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
      exists I; assert_cols; Col5.
      }
    }
  }

  {
  apply between_symmetry in HCol3.
  assert (H := inner_pasch B X1 X2 P R HCol3 HRX1X2); destruct H as [U [HPUX1 HBUR]].
  assert (H := l5_3 P A U X1 HCol1 HPUX1).
  elim H; clear H; intro HAPU.

    {
    elim (eq_dec_points R X2); intro HRX2; treat_equalities; Cop.
    assert (H : TS R A B Q).
      {
      apply l9_31; apply invert_one_side; try assumption.
      apply one_side_transitivity with P.

        {
        assert (H1 : B <> R) by (assert_diffs; auto).
        assert (H2 : Col B R U) by (assert_cols; Col).
        assert (H3 : Col A P U) by (assert_cols; Col).
        assert (H := l9_19 B R A P U H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; apply HABR; Col).
        split; try (intro; treat_equalities; apply HABP; Col).
        Between.
        }

        {
        apply one_side_transitivity with X2.

          {
          assert (H1 : B <> R) by (assert_diffs; auto).
          assert (H2 : Col B R B) by (assert_cols; Col).
          assert (H3 : Col P X2 B) by (assert_cols; Col).
          assert (H := l9_19 B R P X2 B H1 H2 H3); rewrite H.
          split; try  (intro; treat_equalities; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; try (intro; treat_equalities; intuition).
          split; Between.
          }

          {
          assert (H1 : B <> R) by (assert_diffs; auto).
          assert (H2 : Col B R R) by (assert_cols; Col).
          assert (H3 : Col X2 Q R) by (assert_cols; Col).
          assert (H := l9_19 B R X2 Q R H1 H2 H3); rewrite H.
          split; try (intro; apply HBQR; ColR).
          split; try auto.
          split; try (intro; treat_equalities; intuition).
          Between.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    elim (eq_dec_points R X1); intro HRX1; treat_equalities.

      {
      apply between_symmetry in HCol1.
      apply between_symmetry in HCol3.
      assert (H := outer_pasch X2 R P B A HCol3 HCol1); destruct H as [V [HRVX2 HBAV]].
      exists V; left.
      assert_cols; split; ColR.
      }

      {
      assert (H : TS R B A Q).
        {
        apply l9_8_2 with X1.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try (intro; apply HBQR; ColR).
          split; Col.
          exists R; split; Col; Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B U) by (assert_cols; Col).
          assert (H' : P <> X1) by (intro; treat_equalities; apply HAX1; reflexivity).
          assert (H3 : Col X1 A U) by (assert_cols; ColR).
          assert (H := l9_19 R B X1 A U H1 H2 H3); rewrite H.
          split; try (intro; apply HBQR; ColR).
          split; try (intro; treat_equalities; apply HBQR; ColR).
          split; try (intro; treat_equalities; apply HABR; Col).
          eBetween.
          }
        }
      destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
      exists I; assert_cols; Col5.
      }
    }
  }

  {
  assert (H : Bet X1 Q R) by eBetween.
  apply between_symmetry in HQRX1.
  apply between_symmetry in H.
  assert (H' := between_equality R Q X1 H HQRX1); treat_equalities; exfalso; apply HNC; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_2_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet P A X1 ->
  Bet X2 P B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2 HCol2 HCol4 HCol1 HCol3.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
assert (HRX1X2 : Col R X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

  {
  apply coplanar_trans_1_aux_2_1_3_1_1 with P X1 X2; assumption.
  }

  {
  elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    apply coplanar_trans_1_aux_2_1_3_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_2_1_3_1_3 with P X1 X2; assumption.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (Coplanar R Q A B) by (apply coplanar_trans_1_aux_2_1_3_1_2 with P X1 X2; Col; Between); Cop.
    }

    {
    assert (Coplanar R Q A B) by (apply coplanar_trans_1_aux_2_1_3_1_3 with P X1 X2; Col; Between); Cop.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    apply coplanar_trans_1_aux_2_1_3_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_2_1_3_2_3 with P X1 X2; assumption.
    }

    {
    assert (Coplanar R Q A B) by (apply coplanar_trans_1_aux_2_1_3_2_3 with P X1 X2; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_2_1_3_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_2_2_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet A X1 P ->
  Bet B X2 P ->
  Bet Q X1 X2 ->
  Bet R X1 X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HQX1X2.
apply between_symmetry in HRX1X2.
assert (H : X2 <> X1) by auto; assert (HQRX1 := l5_2 X2 X1 Q R H HQX1X2 HRX1X2); clear H.
elim HQRX1; clear HQRX1; intro HQRX1.

  {
  apply between_symmetry in HQX1X2.
  assert (H := outer_pasch B Q X2 P X1 HCol3 HQX1X2); destruct H as [U [HBUQ HPX1U]].
  apply between_symmetry in HCol1.
  assert (HPX1 : P <> X1) by (intro; treat_equalities; assert_cols; apply HNC; Col).
  assert (H := l5_2 P X1 A U HPX1 HCol1 HPX1U).
  elim H; clear H; intro HAX1U.

    {
    elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

      {
      apply between_symmetry in HRX1X2.
      assert (H := outer_pasch B R X2 P Q HCol3 HRX1X2); destruct H as [V [HBVR HPQV]].
      exists V; right; left.
      assert_cols; split; ColR.
      }

      {
      assert (H : TS Q B A R).
        {
        apply l9_8_2 with X1.

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          split; try (intro; assert_cols; apply HABQ; ColR).
          split; Col.
          exists Q; split; Col; Between.
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B U) by (assert_cols; Col).
          assert (H3 : Col X1 A U) by (assert_cols; Col).
          assert (H := l9_19 Q B X1 A U H1 H2 H3); rewrite H.
          split; try (intro; assert_cols; apply HABQ; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try (intro; subst; apply HABQ; Col).
          Between.
          }
        }
      destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
      exists I; assert_cols; Col5.
      }
    }

    {
    elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

      {
      apply between_symmetry in HRX1X2.
      assert (H := outer_pasch B R X2 P Q HCol3 HRX1X2); destruct H as [V [HBVR HPQV]].
      exists V; right; left.
      assert_cols; split; ColR.
      }

      {
      assert (H : TS Q A R B).
        {
        apply l9_31.

          {
          exists P; split.

            {
            assert (H1 : Q <> R) by (assert_diffs; auto).
            split; Col.
            split; Col.
            exists X1; split; Col; Between.
            }

            {
            assert (H1 : Q <> R) by (assert_diffs; auto).
            split; Col.
            split; Col.
            exists X2; split; Col; Between.
            }
          }

          {
          exists X1; split.

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            split; Col.
            split; try (intro; assert_cols; apply HABQ; ColR).
            exists U; split; Col; Between.
            }

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            split; Col.
            split; try (intro; assert_cols; apply HABQ; ColR).
            exists Q; split; Col; Between.
            }
          }
        }
      destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
      exists I; assert_cols; Col5.
      }
    }
  }

  {
  apply between_symmetry in HRX1X2.
  assert (H := outer_pasch B R X2 P X1 HCol3 HRX1X2); destruct H as [U [HBUR HPX1U]].
  apply between_symmetry in HCol1.
  assert (HPX1 : P <> X1) by (intro; treat_equalities; assert_cols; apply HNC; Col).
  assert (H := l5_2 P X1 A U HPX1 HCol1 HPX1U).
  elim H; clear H; intro HAX1U.

    {
    elim (eq_dec_points R X1); intro HRX1; treat_equalities.

      {
      apply between_symmetry in HQX1X2.
      assert (H := outer_pasch B Q X2 P R HCol3 HQX1X2); destruct H as [V [HBVQ HPRV]].
      exists V; right; right.
      assert_cols; split; ColR.
      }

      {
      assert (H : TS R B A Q).
        {
        apply l9_8_2 with X1.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try (intro; assert_cols; apply HABR; ColR).
          split; Col.
          exists R; split; Col; Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B U) by (assert_cols; Col).
          assert (H3 : Col X1 A U) by (assert_cols; Col).
          assert (H := l9_19 R B X1 A U H1 H2 H3); rewrite H.
          split; try (intro; assert_cols; apply HABR; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try (intro; subst; apply HABR; Col).
          Between.
          }
        }
      destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
      exists I; assert_cols; Col5.
      }
    }

    {
    elim (eq_dec_points R X1); intro HRX1; treat_equalities.

      {
      apply between_symmetry in HQX1X2.
      assert (H := outer_pasch B Q X2 P R HCol3 HQX1X2); destruct H as [V [HBVQ HPRV]].
      exists V; right; right.
      assert_cols; split; ColR.
      }

      {
      assert (H : TS R A Q B).
        {
        apply l9_31.

          {
          exists P; split.

            {
            assert (H1 : R <> Q) by (assert_diffs; auto).
            split; Col.
            split; Col.
            exists X1; split; Col; Between.
            }

            {
            assert (H1 : R <> Q) by (assert_diffs; auto).
            split; Col.
            split; Col.
            exists X2; split; Col; Between.
            }
          }

          {
          exists X1; split.

            {
            assert (H1 : R <> B) by (assert_diffs; auto).
            split; Col.
            split; try (intro; assert_cols; apply HABR; ColR).
            exists U; split; Col; Between.
            }

            {
            assert (H1 : R <> B) by (assert_diffs; auto).
            split; Col.
            split; try (intro; assert_cols; apply HABR; ColR).
            exists R; split; Col; Between.
            }
          }
        }
      destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
      exists I; assert_cols; Col5.
      }
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_2_2_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet A X1 P ->
  Bet B X2 P ->
  Bet Q X1 X2 ->
  Bet X1 X2 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  assert (H : TS B Q R A).
    {
    apply l9_8_2 with P.

      {
      assert (B <> Q) by (assert_diffs; auto).
      split; try (intro; assert_diffs; assert_cols; apply HABQ; ColR).
      split; Col.
      exists Q; split; Col; Between.
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : B <> Q) by (assert_diffs; auto).
        assert (H2 : Col B Q B) by (assert_cols; Col).
        assert (H3 : Col P X2 B) by (assert_cols; Col).
        assert (H := l9_19 B Q P X2 B H1 H2 H3); rewrite H.
        split; try (intro; assert_diffs; assert_cols; apply HABQ; ColR).
        split; try (intro; treat_equalities; intuition).
        split; Between.
        }

        {
        assert (H1 : B <> Q) by (assert_diffs; auto).
        assert (H2 : Col B Q Q) by (assert_cols; Col).
        assert (H3 : Col X2 R Q) by (assert_cols; Col).
        assert (H := l9_19 B Q X2 R Q H1 H2 H3); rewrite H.
        assert (Q <> X2) by (intro; treat_equalities; intuition).
        split; try (intro; assert_diffs; assert_cols; apply HABQ; ColR).
        split; try auto.
        split; try (intro; treat_equalities; intuition).
        Between.
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }
    
  {
  assert (H := outer_pasch B Q X2 P X1 HCol3 HQX1X2); destruct H as [U [HBUQ HPX1U]].
  apply between_symmetry in HCol1.
  assert (HPX1 : P <> X1) by (intro; treat_equalities; assert_cols; apply HNC; Col).
  assert (H := l5_2 P X1 A U HPX1 HCol1 HPX1U).
  elim H; clear H; intro HAX1U.

    {
    assert (H : TS Q A R B).
      {
      apply l9_31.

        {
        exists P; split.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          split; Col.
          split; Col.
          exists X1; split; Col; Between.
          }

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          split; Col.
          split; Col.
          exists X2; split; Col; Between.
          }
        }

        {
        apply one_side_transitivity with X1.

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B U) by (assert_cols; Col).
          assert (H3 : Col A X1 U) by (assert_cols; Col).
          assert (H := l9_19 Q B A X1 U H1 H2 H3); rewrite H.
          split; try (intro; assert_cols; apply HABQ; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try (intro; treat_equalities; intuition).
          Between.
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B Q) by (assert_cols; Col).
          assert (H3 : Col X1 R Q) by (assert_cols; Col).
          assert (H := l9_19 Q B X1 R Q H1 H2 H3); rewrite H.
          split; try (intro; assert_cols; apply HABQ; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try (intro; treat_equalities; intuition).
          eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS B Q R A).
      {
      apply l9_8_2 with X1.

        {
        assert (B <> Q) by (assert_diffs; auto).
        split; try (intro; assert_cols; apply HABQ; ColR).
        split; Col.
        exists U; split; Col; Between.
        }

        {
        assert (H1 : B <> Q) by (assert_diffs; auto).
        assert (H2 : Col B Q Q) by (assert_cols; Col).
        assert (H3 : Col X1 R Q) by (assert_cols; Col).
        assert (H := l9_19 B Q X1 R Q H1 H2 H3); rewrite H.
        split; try (intro; assert_cols; apply HABQ; ColR).
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; apply HNC; Col).
        eBetween.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_2_2_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet A X1 P ->
  Bet B X2 P ->
  Bet Q X1 X2 ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  assert (H : TS B Q R A).
    {
    apply l9_8_2 with P.

      {
      assert (B <> Q) by (assert_diffs; auto).
      split; try (intro; assert_diffs; assert_cols; apply HABQ; ColR).
      split; Col.
      exists Q; split; Col; Between.
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : B <> Q) by (assert_diffs; auto).
        assert (H2 : Col B Q B) by (assert_cols; Col).
        assert (H3 : Col P X2 B) by (assert_cols; Col).
        assert (H := l9_19 B Q P X2 B H1 H2 H3); rewrite H.
        split; try (intro; assert_diffs; assert_cols; apply HABQ; ColR).
        split; try (intro; treat_equalities; intuition).
        split; Between.
        }

        {
        assert (H1 : B <> Q) by (assert_diffs; auto).
        assert (H2 : Col B Q Q) by (assert_cols; Col).
        assert (H3 : Col X2 R Q) by (assert_cols; Col).
        assert (H := l9_19 B Q X2 R Q H1 H2 H3); rewrite H.
        assert (Q <> X2) by (intro; treat_equalities; intuition).
        split; try (intro; assert_diffs; assert_cols; apply HABQ; ColR).
        split; try auto.
        split; try (intro; treat_equalities; intuition).
        Between.
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }
    
  {
  assert (H := outer_pasch B Q X2 P X1 HCol3 HQX1X2); destruct H as [U [HBUQ HPX1U]].
  apply between_symmetry in HCol1.
  assert (HPX1 : P <> X1) by (intro; treat_equalities; assert_cols; apply HNC; Col).
  assert (H := l5_2 P X1 A U HPX1 HCol1 HPX1U).
  elim H; clear H; intro HAX1U.

    {
    assert (H : TS Q A R B).
      {
      apply l9_31.

        {
        exists P; split.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          split; Col.
          split; Col.
          exists X1; split; Col; Between.
          }

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          split; Col.
          split; Col.
          exists X2; split; Col; Between.
          }
        }

        {
        apply one_side_transitivity with X1.

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B U) by (assert_cols; Col).
          assert (H3 : Col A X1 U) by (assert_cols; Col).
          assert (H := l9_19 Q B A X1 U H1 H2 H3); rewrite H.
          split; try (intro; assert_cols; apply HABQ; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try (intro; treat_equalities; intuition).
          Between.
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B Q) by (assert_cols; Col).
          assert (H3 : Col X1 R Q) by (assert_cols; Col).
          assert (H := l9_19 Q B X1 R Q H1 H2 H3); rewrite H.
          split; try (intro; assert_cols; apply HABQ; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try (intro; treat_equalities; intuition).
          eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS B Q R A).
      {
      apply l9_8_2 with X1.

        {
        assert (B <> Q) by (assert_diffs; auto).
        split; try (intro; assert_cols; apply HABQ; ColR).
        split; Col.
        exists U; split; Col; Between.
        }

        {
        assert (H1 : B <> Q) by (assert_diffs; auto).
        assert (H2 : Col B Q Q) by (assert_cols; Col).
        assert (H3 : Col X1 R Q) by (assert_cols; Col).
        assert (H := l9_19 B Q X1 R Q H1 H2 H3); rewrite H.
        split; try (intro; assert_cols; apply HABQ; ColR).
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; apply HNC; Col).
        eBetween.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_2_2_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet A X1 P ->
  Bet B X2 P ->
  Bet X2 Q X1 ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HQRX2 := l5_3 X2 Q R X1 HQX1X2 HRX1X2).
elim HQRX2; clear HQRX2; intro HQRX2.

  {
  elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

    {
    apply between_symmetry in HCol1.
    assert (H := outer_pasch P Q X1 A R HCol1 HRX1X2); destruct H as [U [HPUQ HARU]].
    exists U; right; right.
    assert_diffs; assert_cols; split; ColR.
    }

    {
    assert (H : TS A Q B R).
      {
      apply l9_8_2 with X2.

        {
        assert (A <> Q) by (assert_diffs; auto).
        split; try (intro; assert_cols; apply HAQR; ColR).
        split; Col.
        exists Q; split; Col; Between.
        }

        {
        apply between_symmetry in HCol1.
        assert (H := outer_pasch P X2 X1 A Q HCol1 HQX1X2); destruct H as [U [HPUX2 HAQU]].
        assert (H1 : A <> Q) by (assert_diffs; auto).
        assert (H2 : Col A Q U) by (assert_cols; Col).
        assert (HPX2 : P <> X2) by (intro; treat_equalities; apply HNC; Col).
        assert (H3 : Col X2 B U) by (assert_cols; ColR).
        assert (H := l9_19 A Q X2 B U H1 H2 H3); rewrite H.
        split; try (intro; assert_cols; apply HAQR; ColR).
        split; try (intro; treat_equalities; assert_cols; apply HAQR; ColR).
        split; try (intro; treat_equalities; apply HABQ; Col).
        eBetween.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    apply between_symmetry in HCol1.
    assert (H := outer_pasch P R X1 A Q HCol1 HQX1X2); destruct H as [U [HPUR HAQU]].
    exists U; right; left.
    assert_diffs; assert_cols; split; ColR.
    }

    {
    assert (H : TS A R B Q).
      {
      apply l9_8_2 with X2.

        {
        assert (A <> R) by (assert_diffs; auto).
        split; try (intro; assert_cols; apply HAQR; ColR).
        split; Col.
        exists R; split; Col; Between.
        }

        {
        apply between_symmetry in HCol1.
        assert (H := outer_pasch P X2 X1 A R HCol1 HRX1X2); destruct H as [U [HPUX2 HARU]].
        assert (H1 : A <> R) by (assert_diffs; auto).
        assert (H2 : Col A R U) by (assert_cols; Col).
        assert (HPX2 : P <> X2) by (intro; treat_equalities; apply HNC; Col).
        assert (H3 : Col X2 B U) by (assert_cols; ColR).
        assert (H := l9_19 A R X2 B U H1 H2 H3); rewrite H.
        split; try (intro; assert_cols; apply HAQR; ColR).
        split; try (intro; treat_equalities; assert_cols; apply HAQR; ColR).
        split; try (intro; treat_equalities; apply HABR; Col).
        eBetween.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet A X1 P ->
  Bet B X2 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2 HCol2 HCol4 HCol1 HCol3.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
assert (HRX1X2 : Col R X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

  {
  apply coplanar_trans_1_aux_2_2_2_1_1 with P X1 X2; assumption.
  }

  {
  elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    apply coplanar_trans_1_aux_2_2_2_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_2_2_2_1_3 with P X1 X2; assumption.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_2_2_1_2 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar R Q A B) by (apply coplanar_trans_1_aux_2_2_2_1_3 with P X1 X2; Col; Between); Cop.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_2_2_1_1 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_2_2_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar R Q B A) by (apply coplanar_trans_1_aux_2_2_2_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_2_2_2_2_2 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet A X1 P ->
  Bet X2 P B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2 HCol2 HCol4 HCol1 HCol3.
assert (H : TS Q R B A).
  {
  apply l9_8_2 with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    split; Col.
    split; Col.
    exists X1; split; Col; Between.
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X2) by (assert_cols; Col).
    assert (H3 : Col P B X2) by (assert_cols; Col).
    assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; Between.
    }
  }
destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
exists I; assert_cols; Col5.
Qed.

Lemma coplanar_trans_1_aux_2_3_3_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet X1 P A ->
  Bet X2 P B ->
  Bet Q X1 X2 ->
  Bet R X1 X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HQX1X2.
apply between_symmetry in HRX1X2.
assert (H : X2 <> X1) by auto; assert (HQRX1 := l5_2 X2 X1 Q R H HQX1X2 HRX1X2); clear H.
elim HQRX1; clear HQRX1; intro HQRX1.

  {
  apply between_symmetry in HCol1.
  apply between_symmetry in HRX1X2.
  assert (H := outer_pasch R A X1 X2 P HRX1X2 HCol1); destruct H as [U [HAUR HX2PU]].
  assert (HPX2 : X2 <> P) by (intro; treat_equalities; apply HNC; Col).
  assert (H := l5_2 X2 P B U HPX2 HCol3 HX2PU).
  elim H; clear H; intro HBPU.

    {
    assert (H : TS R B Q A).
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
          split; try assumption.
          split; try (intro; treat_equalities; intuition).
          Between.
          }

          {
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q X1) by (assert_cols; Col).
          assert (H3 : Col P A X1) by (assert_cols; Col).
          assert (H := l9_19 R Q P A X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; try assumption.
          Between.
          }
        }

        {
        apply one_side_transitivity with X2.

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A U) by (assert_cols; Col).
          assert (H3 : Col B X2 U) by (assert_cols; ColR).
          assert (H := l9_19 R A B X2 U H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; try (intro; treat_equalities; intuition).
          eBetween.
          }

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A R) by (assert_cols; Col).
          assert (H3 : Col X2 Q R) by (assert_cols; Col).
          assert (H := l9_19 R A X2 Q R H1 H2 H3); rewrite H.
          assert (R <> X2) by (intro; treat_equalities; apply HNC; Col).
          split; try (intro; apply HAQR; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try (intro; treat_equalities; intuition).
          eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (A <> R) by (assert_diffs; auto).
        assert (R <> X2) by (intro; treat_equalities; apply HNC; Col).
        split; try (intro; apply HAQR; ColR).
        split; Col.
        exists U; split; Col; eBetween.
        }

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        assert (H2 : Col A R R) by (assert_cols; Col).
        assert (H3 : Col X2 Q R) by (assert_cols; Col).
        assert (H := l9_19 A R X2 Q R H1 H2 H3); rewrite H.
        assert (R <> X2) by (intro; treat_equalities; apply HNC; Col).
        split; try (intro; apply HAQR; ColR).
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        eBetween.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  apply between_symmetry in HCol1.
  apply between_symmetry in HQX1X2.
  assert (H := outer_pasch Q A X1 X2 P HQX1X2 HCol1); destruct H as [U [HAUQ HX2PU]].
  assert (HPX2 : X2 <> P) by (intro; treat_equalities; apply HNC; Col).
  assert (H := l5_2 X2 P B U HPX2 HCol3 HX2PU).
  elim H; clear H; intro HBPU.

    {
    assert (H : TS Q B R A).
      {
      apply l9_31.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R X2) by (assert_cols; Col).
          assert (H3 : Col B P X2) by (assert_cols; Col).
          assert (H := l9_19 Q R B P X2 H1 H2 H3); rewrite H.
          split; Col.
          split; try assumption.
          split; try (intro; treat_equalities; intuition).
          Between.
          }

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R X1) by (assert_cols; Col).
          assert (H3 : Col P A X1) by (assert_cols; Col).
          assert (H := l9_19 Q R P A X1 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; try assumption.
          Between.
          }
        }

        {
        apply one_side_transitivity with X2.

          {
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A U) by (assert_cols; Col).
          assert (H3 : Col B X2 U) by (assert_cols; ColR).
          assert (H := l9_19 Q A B X2 U H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; intuition).
          split; try (intro; treat_equalities; intuition).
          eBetween.
          }

          {
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A Q) by (assert_cols; Col).
          assert (H3 : Col X2 R Q) by (assert_cols; Col).
          assert (H := l9_19 Q A X2 R Q H1 H2 H3); rewrite H.
          assert (Q <> X2) by (intro; treat_equalities; apply HNC; Col).
          split; try (intro; apply HAQR; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try (intro; treat_equalities; intuition).
          eBetween.
          }
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS A Q R B).
      {
      apply l9_8_2 with X2.

        {
        assert (A <> Q) by (assert_diffs; auto).
        assert (Q <> X2) by (intro; treat_equalities; apply HNC; Col).
        split; try (intro; apply HAQR; ColR).
        split; Col.
        exists U; split; Col; eBetween.
        }

        {
        assert (H1 : A <> Q) by (assert_diffs; auto).
        assert (H2 : Col A Q Q) by (assert_cols; Col).
        assert (H3 : Col X2 R Q) by (assert_cols; Col).
        assert (H := l9_19 A Q X2 R Q H1 H2 H3); rewrite H.
        assert (Q <> X2) by (intro; treat_equalities; apply HNC; Col).
        split; try (intro; apply HAQR; ColR).
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        eBetween.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_3_3_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet X1 P A ->
  Bet X2 P B ->
  Bet Q X1 X2 ->
  Bet X1 X2 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HCol1.
assert (H := outer_pasch Q A X1 X2 P HQX1X2 HCol1); destruct H as [U [HAUQ HX2PU]].
assert (HPX2 : X2 <> P) by (intro; treat_equalities; apply HNC; Col).
assert (H := l5_2 X2 P B U HPX2 HCol3 HX2PU).
elim H; clear H; intro HBPU.

  {
  assert (H : TS Q B R A).
    {
    apply l9_31.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R X2) by (assert_cols; Col).
        assert (H3 : Col B P X2) by (assert_cols; Col).
        assert (H := l9_19 Q R B P X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try assumption.
        split; try (intro; treat_equalities; intuition).
        Between.
        }

        {
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R X1) by (assert_cols; Col).
        assert (H3 : Col P A X1) by (assert_cols; Col).
        assert (H := l9_19 Q R P A X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; intuition).
        split; try assumption.
        Between.
        }
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A U) by (assert_cols; Col).
        assert (H3 : Col B X2 U) by (assert_cols; ColR).
        assert (H := l9_19 Q A B X2 U H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        eBetween.
        }

        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by (assert_cols; Col).
        assert (H3 : Col X2 R Q) by (assert_cols; Col).
        assert (H := l9_19 Q A X2 R Q H1 H2 H3); rewrite H.
        assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
        split; try (intro; apply HAQR; ColR).
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        eBetween.
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  assert (H : TS A Q R B).
    {
    apply l9_8_2 with X2.

      {
      assert (A <> Q) by (assert_diffs; auto).
      assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      split; Col.
      exists U; split; Col; eBetween.
      }

      {
      assert (H1 : A <> Q) by (assert_diffs; auto).
      assert (H2 : Col A Q Q) by (assert_cols; Col).
      assert (H3 : Col X2 R Q) by (assert_cols; Col).
      assert (H := l9_19 A Q X2 R Q H1 H2 H3); rewrite H.
      assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      split; try (intro; treat_equalities; intuition).
      split; try (intro; treat_equalities; intuition).
      eBetween.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }
Qed.

Lemma coplanar_trans_1_aux_2_3_3_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet X1 P A ->
  Bet X2 P B ->
  Bet Q X1 X2 ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HCol1.
assert (H := outer_pasch Q A X1 X2 P HQX1X2 HCol1); destruct H as [U [HAUQ HX2PU]].
assert (HPX2 : X2 <> P) by (intro; treat_equalities; apply HNC; Col).
assert (H := l5_2 X2 P B U HPX2 HCol3 HX2PU).
elim H; clear H; intro HBPU.

  {
  assert (H : TS Q B R A).
    {
    apply l9_31.

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R X2) by (assert_cols; Col).
        assert (H3 : Col B P X2) by (assert_cols; Col).
        assert (H := l9_19 Q R B P X2 H1 H2 H3); rewrite H.
        split; Col.
        split; try assumption.
        split; try (intro; treat_equalities; intuition).
        Between.
        }

        {
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R X1) by (assert_cols; Col).
        assert (H3 : Col P A X1) by (assert_cols; Col).
        assert (H := l9_19 Q R P A X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; intuition).
        split; try assumption.
        Between.
        }
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A U) by (assert_cols; Col).
        assert (H3 : Col B X2 U) by (assert_cols; ColR).
        assert (H := l9_19 Q A B X2 U H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        eBetween.
        }

        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by (assert_cols; Col).
        assert (H3 : Col X2 R Q) by (assert_cols; Col).
        assert (H := l9_19 Q A X2 R Q H1 H2 H3); rewrite H.
        assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
        split; try (intro; apply HAQR; ColR).
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        eBetween.
        }
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }

  {
  assert (H : TS A Q R B).
    {
    apply l9_8_2 with X2.

      {
      assert (A <> Q) by (assert_diffs; auto).
      assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      split; Col.
      exists U; split; Col; eBetween.
      }

      {
      assert (H1 : A <> Q) by (assert_diffs; auto).
      assert (H2 : Col A Q Q) by (assert_cols; Col).
      assert (H3 : Col X2 R Q) by (assert_cols; Col).
      assert (H := l9_19 A Q X2 R Q H1 H2 H3); rewrite H.
      assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      split; try (intro; treat_equalities; intuition).
      split; try (intro; treat_equalities; intuition).
      eBetween.
      }
    }
  destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
  exists I; assert_cols; Col5.
  }
Qed.

Lemma coplanar_trans_1_aux_2_3_3_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet X1 P A ->
  Bet X2 P B ->
  Bet X2 Q X1 ->
  Bet X2 R X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HQX1X2.
apply between_symmetry in HRX1X2.
assert (HOS : OS Q R A B).
  {
  apply one_side_transitivity with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X1) by (assert_cols; Col).
    assert (H3 : Col A P X1) by (assert_cols; Col).
    assert (H := l9_19 Q R A P X1 H1 H2 H3); rewrite H.
    split; Col.
    split; try assumption.
    split; try (intro; treat_equalities; intuition).
    Between.
    }

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R X2) by (assert_cols; Col).
    assert (H3 : Col P B X2) by (assert_cols; Col).
    assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; treat_equalities; intuition).
    split; try assumption.
    Between.
    }
  }
assert (H := l5_3 X1 Q R X2 HQX1X2 HRX1X2).
elim H; clear H; intro HQRX1.

  {
  elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

    {
    assert (H : TS Q A R B).
      {
      apply l9_31; try assumption.
      apply one_side_transitivity with X2.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B Q) by (assert_cols; Col).
          assert (H3 : Col A P Q) by (assert_cols; ColR).
          assert (H := l9_19 Q B A P Q H1 H2 H3); rewrite H.
          split; Col.
          split; try assumption.
          split; try (intro; treat_equalities; intuition).
          Between.
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B B) by (assert_cols; Col).
          assert (H3 : Col P X2 B) by (assert_cols; ColR).
          assert (H := l9_19 Q B P X2 B H1 H2 H3); rewrite H.
          split; try (intro; assert_diffs; assert_cols; apply HABQ; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try auto.
          Between.
          }
        }

        {
        assert (H1 : Q <> B) by (assert_diffs; auto).
        assert (H2 : Col Q B Q) by (assert_cols; Col).
        assert (H3 : Col X2 R Q) by (assert_cols; ColR).
        assert (H := l9_19 Q B X2 R Q H1 H2 H3); rewrite H.
        assert (B <> X2) by (intro; treat_equalities; intuition).
        split; try (intro; apply HBQR; ColR).
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS Q A R B).
      {
      apply l9_31; try assumption.
      exists X1; split.

        {
        apply between_symmetry in HCol3.
        assert (H := inner_pasch B X1 X2 P Q HCol3 HQX1X2); destruct H as [U [HPUX1 HBUQ]].
        assert (Q <> B) by (assert_diffs; auto).
        split; Col.
        split; try (intro; apply HBQR; ColR).
        exists U; assert_cols; split; Col; eBetween.
        }

        {
        assert (Q <> B) by (assert_diffs; auto).
        split; Col.
        split; try (intro; apply HBQR; ColR).
        exists Q; split; Col; Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  elim (eq_dec_points R X1); intro HRX1; treat_equalities.

    {
    assert (H : TS R A Q B).
      {
      apply l9_31; try (apply invert_one_side; assumption).
      apply one_side_transitivity with X2.

        {
        apply one_side_transitivity with P.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B R) by (assert_cols; Col).
          assert (H3 : Col A P R) by (assert_cols; ColR).
          assert (H := l9_19 R B A P R H1 H2 H3); rewrite H.
          split; Col.
          split; try assumption.
          split; try (intro; treat_equalities; intuition).
          Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B B) by (assert_cols; Col).
          assert (H3 : Col P X2 B) by (assert_cols; ColR).
          assert (H := l9_19 R B P X2 B H1 H2 H3); rewrite H.
          split; try (intro; assert_diffs; assert_cols; apply HABR; ColR).
          split; try (intro; treat_equalities; intuition).
          split; try auto.
          Between.
          }
        }

        {
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B R) by (assert_cols; Col).
        assert (H3 : Col X2 Q R) by (assert_cols; ColR).
        assert (H := l9_19 R B X2 Q R H1 H2 H3); rewrite H.
        assert (B <> X2) by (intro; treat_equalities; intuition).
        split; try (intro; apply HBQR; ColR).
        split; try (intro; treat_equalities; intuition).
        split; try (intro; treat_equalities; intuition).
        Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : TS R A Q B).
      {
      apply l9_31; try (apply invert_one_side; assumption).
      exists X1; split.

        {
        apply between_symmetry in HCol3.
        assert (H := inner_pasch B X1 X2 P R HCol3 HRX1X2); destruct H as [U [HPUX1 HBUR]].
        assert (R <> B) by (assert_diffs; auto).
        split; Col.
        split; try (intro; apply HBQR; ColR).
        exists U; assert_cols; split; Col; eBetween.
        }

        {
        assert (R <> B) by (assert_diffs; auto).
        split; Col.
        split; try (intro; apply HBQR; ColR).
        exists R; split; Col; Between.
        }
      }
    destruct H as [HCol5 [HCol6 [I [HCol7 HCol8]]]].
    exists I; assert_cols; Col5.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B P ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  A <> X1 ->
  B <> X2 ->
  X1 <> X2 ->
  Col Q R X1 ->
  Col Q R X2 ->
  Bet X1 P A ->
  Bet X2 P B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2 HCol2 HCol4 HCol1 HCol3.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
assert (HRX1X2 : Col R X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

  {
  apply coplanar_trans_1_aux_2_3_3_1_1 with P X1 X2; assumption.
  }

  {
  elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    apply coplanar_trans_1_aux_2_3_3_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_2_3_3_1_3 with P X1 X2; assumption.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_3_3_1_2 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar R Q A B) by (apply coplanar_trans_1_aux_2_3_3_1_3 with P X1 X2; Col; Between); Cop.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_3_3_1_1 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_3_3_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (Coplanar R Q B A) by (apply coplanar_trans_1_aux_2_3_3_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_2_3_3_2_2 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P A X1 ->
  Col Q R X1 ->
  Col P B X2 ->
  Col Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points A X1); intro HAX1; subst; Cop.
elim (eq_dec_points B X2); intro HBX2; subst; Cop.
elim (eq_dec_points A P); intro HAP; elim (eq_dec_points B P); intro HBP; subst.

  {
  exfalso; apply HABQ; Col.
  }

  {
  exists X2; Col5.
  }

  {
  exists X1; Col5.
  }

  {
  elim (Col_dec A B P); intro HABP.

    {
    assert (HX1X2 : X1 = X2) by (apply l6_21 with Q R P A; Col; ColR); subst.
    exists X2; assert_diffs; left; split; Col; ColR.
    }

    {
    assert (HX1X2 : X1 <> X2).
      {
      intro; treat_equalities; elim (eq_dec_points P X1); intro; subst.

        {
        apply HNC; Col.
        }

        {
        apply HABP; ColR.
        }
      }
    elim HCol1; clear HCol1; intro HCol1; elim HCol3; clear HCol3; intro HCol3.

      {
      apply coplanar_trans_1_aux_2_1_1 with P X1 X2; assumption.
      }

      {
      elim HCol3; clear HCol3; intro HCol3.

        {
        apply coplanar_trans_1_aux_2_1_2 with P X1 X2; assumption.
        }

        {
        apply coplanar_trans_1_aux_2_1_3 with P X1 X2; assumption.
        }
      }

      {
      elim HCol1; clear HCol1; intro HCol1.

        {
        assert (H : Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_2 with P X2 X1; Col; Between); Cop.
        }

        {
        assert (H : Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_3 with P X2 X1; Col; Between); Cop.
        }
      }

      {
      elim HCol1; clear HCol1; intro HCol1; elim HCol3; clear HCol3; intro HCol3.

        {
        apply coplanar_trans_1_aux_2_2_2 with P X1 X2; assumption.
        }

        {
        apply coplanar_trans_1_aux_2_2_3 with P X1 X2; assumption.
        }

        {
        assert (H : Coplanar Q R B A) by (apply coplanar_trans_1_aux_2_2_3 with P X2 X1; Col; Between); Cop.
        }

        {
        apply coplanar_trans_1_aux_2_3_3 with P X1 X2; assumption.
        }
      }
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col Q B X2 ->
  Bet P Q X1 ->
  Bet P R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol3 HCol4 HCol1 HCol2.
elim (eq_dec_points R X2); intro HRX2; treat_equalities.
  {
  assert_cols; Cop.
  }

  {
  assert (HTS : TS R A Q X2).
    {
    apply l9_8_2 with P.

      {
      split; Col.
      split; try exists R; Col.
      intro; apply HRX2; assert_diffs; assert_cols; apply l6_21 with R P A R; Col.
      }

      {
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A X1) by (assert_cols; Col).
      assert (H3 : Col P Q X1) by (assert_cols; Col).
      assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; apply HNC); treat_equalities; Col.
      split; try (intro; apply HAQR); treat_equalities; Col.
      right; Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HRAI HQX2I]]]]; clear H1; clear H2.
  assert (H : Col Q B I).
    {
    assert (Q <> X2) by (intro; apply HNC; subst; Col).
    assert_cols; ColR.
    }
  exists I; right; right; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet R A X1 ->
  Bet Q B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with X1.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; Col.
      split; try (exists Q; Col).
      intro; assert (R = X1) by (assert_diffs; assert_cols; apply l6_21 with A R Q R; Col);
      treat_equalities; apply HABR; Col.
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by Col.
        assert (H3 : Col P X2 R) by (assert_cols; Col).
        assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; apply HNC); treat_equalities; Col.
        split; try (intro; apply HBQR); treat_equalities; Col.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R Q) by Col.
        assert (H3 : Col B X2 Q) by (assert_cols; Col).
        assert (H := l9_19 Q R B X2 Q H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; apply HABQ); treat_equalities; Col.
        split; try (intro; apply HBQR); treat_equalities; Col.
        }
      }
    }

    {
    apply one_side_symmetry.
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R R) by Col.
    assert (H3 : Col A X1 R) by (assert_cols; Col).
    assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; apply HABR); treat_equalities; Col.
    split; try (intro; apply HABR); treat_equalities; Col.
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; assert_cols; Col.
Qed.

Lemma coplanar_trans_1_aux_3_1_2_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet R A X1 ->
  Bet B X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with X1.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; Col.
      split; try (exists Q; Col).
      intro; assert (R = X1) by (assert_diffs; assert_cols; apply l6_21 with A R Q R; Col);
      treat_equalities; apply HABR; Col.
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by Col.
        assert (H3 : Col P X2 R) by (assert_cols; Col).
        assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; apply HNC); treat_equalities; Col.
        split; try (intro; apply HBQR); treat_equalities; Col.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R Q) by Col.
        assert (H3 : Col B X2 Q) by (assert_cols; Col).
        assert (H := l9_19 Q R B X2 Q H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; apply HABQ); treat_equalities; Col.
        split; Between.
        intro; subst; apply HNC; assert_cols; Col.
        }
      }
    }

    {
    apply one_side_symmetry.
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R R) by Col.
    assert (H3 : Col A X1 R) by (assert_cols; Col).
    assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; apply HABR); treat_equalities; Col.
    split; try (intro; apply HABR); treat_equalities; Col.
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; assert_cols; Col.
Qed.

Lemma coplanar_trans_1_aux_3_1_2_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet R A X1 ->
  Bet X2 Q B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
apply between_symmetry in HCol4.
assert (H := outer_pasch R B X2 P Q HCol2 HCol4); destruct H as [I [HRIB HPQI]].
assert (HElim : Bet Q I X1 \/ Bet Q X1 I) by (apply l5_2 with P; assert_diffs; Between).
elim HElim; clear HElim; intro HQX1I.

  {
  assert (HTS : TS R B A Q).
    {
    elim (eq_dec_points R X1); intro HRX1.

      {
      exfalso; apply HNC; subst; Col.
      }

      {
      apply l9_8_2 with X1.

        {
        split; try (intro; apply HABR; assert_cols; ColR).
        split; Col.
        exists I; assert_cols; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B R) by Col.
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        }
      }
    }
    destruct HTS as [H1 [H2 [I' [HRBI' HAQI']]]]; clear H1; clear H2.
    exists I'; right; left; assert_cols; Col.
  }

  {
  apply between_symmetry in HRIB.
  assert (H := outer_pasch B Q I R X1 HRIB HQX1I); destruct H as [I' [HQI'B HRX1I']].
  exists I'; right; right.
  assert (Col R A I').
    {
    assert (R <> X1) by (intro; subst; apply HNC; assert_cols; Col); assert_cols; ColR.
    }
  assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col Q B X2 ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet R A X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_3_1_2_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_3_1_2_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_3_1_2_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet A X1 R ->
  Bet Q B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with X1.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; Col.
      split; try (exists Q; Col).
      intro; assert (R = X1) by (assert_diffs; assert_cols; apply l6_21 with A R Q R; Col);
      treat_equalities; apply HNC; Col.
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by Col.
        assert (H3 : Col P X2 R) by (assert_cols; Col).
        assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; apply HNC); treat_equalities; Col.
        split; try (intro; apply HBQR); treat_equalities; Col.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R Q) by Col.
        assert (H3 : Col B X2 Q) by (assert_cols; Col).
        assert (H := l9_19 Q R B X2 Q H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; apply HABQ); treat_equalities; Col.
        split; Between.
        intro; subst; apply HNC; assert_cols; Col.
        }
      }
    }

    {
    apply one_side_symmetry.
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R R) by Col.
    assert (H3 : Col A X1 R) by (assert_cols; Col).
    assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; apply HABR); treat_equalities; Col.
    split; try (intro; apply HNC); treat_equalities; Col.
    Between.
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; assert_cols; Col.
Qed.

Lemma coplanar_trans_1_aux_3_1_2_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet A X1 R ->
  Bet B X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with X1.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; Col.
      split; try (exists Q; Col).
      intro; assert (R = X1) by (assert_diffs; assert_cols; apply l6_21 with A R Q R; Col);
      treat_equalities; apply HNC; Col.
      }

      {
      apply one_side_transitivity with X2.

        {
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by Col.
        assert (H3 : Col P X2 R) by (assert_cols; Col).
        assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; apply HNC); treat_equalities; Col.
        split; try (intro; apply HBQR); treat_equalities; Col.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R Q) by Col.
        assert (H3 : Col B X2 Q) by (assert_cols; Col).
        assert (H := l9_19 Q R B X2 Q H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; apply HABQ); treat_equalities; Col.
        split; Between.
        intro; subst; apply HNC; assert_cols; Col.
        }
      }
    }

    {
    apply one_side_symmetry.
    assert (H1 : Q <> R) by (assert_diffs; auto).
    assert (H2 : Col Q R R) by Col.
    assert (H3 : Col A X1 R) by (assert_cols; Col).
    assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
    split; Col.
    split; try (intro; apply HABR); treat_equalities; Col.
    split; try (intro; apply HNC); treat_equalities; Col.
    Between.
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; assert_cols; Col.
Qed.

Lemma coplanar_trans_1_aux_3_1_2_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet A X1 R ->
  Bet X2 Q B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
apply between_symmetry in HCol4.
assert (H := outer_pasch R B X2 P Q HCol2 HCol4); destruct H as [I [HRIB HPQI]].
assert (HElim : Bet Q I X1 \/ Bet Q X1 I) by (apply l5_2 with P; assert_diffs; Between).
elim HElim; clear HElim; intro HQX1I.

  {
  assert (HTS : TS R B A Q).
    {
    elim (eq_dec_points R X1); intro HRX1.

      {
      exfalso; apply HNC; subst; Col.
      }

      {
      apply l9_8_2 with X1.

        {
        split; try (intro; apply HABR; assert_cols; ColR).
        split; Col.
        exists I; assert_cols; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B R) by Col.
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; Between.
        }
      }
    }
    destruct HTS as [H1 [H2 [I' [HRBI' HAQI']]]]; clear H1; clear H2.
    exists I'; right; left; assert_cols; Col.
  }

  {
  apply between_symmetry in HRIB.
  assert (H := outer_pasch B Q I R X1 HRIB HQX1I); destruct H as [I' [HQI'B HRX1I']].
  exists I'; right; right.
  assert (Col R A I').
    {
    assert (R <> X1) by (intro; subst; apply HNC; assert_cols; Col); assert_cols; ColR.
    }
  assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col Q B X2 ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet A X1 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_3_1_2_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_3_1_2_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_3_1_2_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet X1 R A ->
  Bet Q B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1.

  {
  exfalso; apply HNC; subst; Col.
  }

  {
  assert (HTS : TS R B Q A).
    {
    apply l9_8_2 with X1.

      {
      split; try (intro; apply HABR; assert_cols; ColR).
      split; Col.
      exists R; Col.
      }

      {
      apply between_symmetry in HCol2.
      assert (H := outer_pasch P Q X2 R B HCol2 HCol4); destruct H as [I [HPIQ HRBI]].
      assert (HIQX1 : Bet I Q X1) by eBetween.
      assert (H1 : R <> B) by (assert_diffs; auto).
      assert (H2 : Col R B I) by (assert_cols; Col).
      assert (H3 : Col X1 Q I) by (assert_cols; Col).
      assert (H := l9_19 R B X1 Q I H1 H2 H3); rewrite H.
      split; try (intro; apply HABR; assert_cols; ColR).
      split; try (intro; apply HAQR; treat_equalities; assert_cols; Col).
      split; try (intro; apply HBQR; treat_equalities); Col.
      }
    }
  destruct HTS as [H1 [H2 [I [HRBI HAQI]]]]; clear H1; clear H2.
  exists I; right; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet X1 R A ->
  Bet B X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch P A X1 Q R HCol1 (between_symmetry X1 R A HCol3));
destruct H as [I [HQIA HRIP]]; assert (HElim := l5_3 _ _ _ _ HCol2 HRIP).
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  elim HElim; clear HElim; intro HRX2I.

    {
    assert (HTS : TS Q B R A).
      {
      apply l9_31.

        {
        apply one_side_transitivity with P.

          {
          apply one_side_transitivity with X2.

            {
            assert (H1 : Q <> R) by (assert_diffs; auto).
            assert (H2 : Col Q R Q) by (assert_cols; Col).
            assert (H3 : Col B X2 Q) by (assert_cols; Col).
            assert (H := l9_19 Q R B X2 Q H1 H2 H3); rewrite H.
            split; Col.
            split; try (assert_diffs; Col).
            split; try (intro; apply HNC; subst; Col).
            Between.
            }

            {
            apply one_side_symmetry.
            assert (H1 : Q <> R) by (assert_diffs; auto).
            assert (H2 : Col Q R R) by (assert_cols; Col).
            assert (H3 : Col P X2 R) by (assert_cols; Col).
            assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
            split; Col.
            split; try (assert_diffs; Col).
            split; try (intro; apply HBQR; subst; Col).
            Between.
            }
          }

          {
          elim (eq_dec_points R X1); intro HRX1; treat_equalities.

            {
            exfalso; apply HNC; assert_cols; Col.
            }

            {
            exists X1; split.

              {
              split; Col.
              split; try (intro; apply HAQR; assert_cols; ColR).
              exists Q; Col.
              }

              {
              split; Col.
              split; try (intro; apply HAQR; assert_cols; ColR).
              exists R; split; Col; Between.
              }
            }
          }
        }

        {
        apply one_side_transitivity with X2.

          {
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A Q) by (assert_cols; Col).
          assert (H3 : Col B X2 Q) by (assert_cols; Col).
          assert (H := l9_19 Q A B X2 Q H1 H2 H3); rewrite H.
          split; Col.
          split; try (assert_diffs; Col).
          split; try (intro; apply HNC; subst; Col).
          Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A I) by (assert_cols; Col).
          assert (H3 : Col R X2 I) by (assert_cols; Col).
          assert (H := l9_19 Q A R X2 I H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; Col).
          split; Between.
          intro; treat_equalities; apply HABQ; assert_cols; ColR.
          }
        }
      }
      destruct HTS as [H1 [H2 [I' [HQBI' HRAI']]]]; clear H1; clear H2.
      exists I'; right; right; assert_cols; Col.
    }

    {
    assert (HTS : TS Q A B R).
      {
      apply l9_8_2 with X2.

        {
        split; try (intro; apply HABQ; assert_cols; ColR).
        split; Col.
        exists I; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by (assert_cols; Col).
        assert (H3 : Col B X2 Q) by (assert_cols; Col).
        assert (H := l9_19 Q A B X2 Q H1 H2 H3); rewrite H.
        split; Col.
        split; try (assert_diffs; Col).
        split; Between.
        }
      }
    destruct HTS as [H1 [H2 [I' [HQAI' HRBI']]]]; clear H1; clear H2.
    exists I'; right; left; assert_cols; Col.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet X1 R A ->
  Bet X2 Q B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (HTS : TS Q R A B).
    {
    apply l9_8_2 with X2.

      {
      split; try (intro; apply HBQR; assert_cols; ColR).
      split; Col.
      exists Q; Col.
      }

      {
      apply one_side_transitivity with P.

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by (assert_cols; Col).
        assert (H3 : Col P X2 R) by (assert_cols; Col).
        assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; try (assert_diffs; Col).
        split; try (intro; subst; apply HBQR; assert_cols; Col).
        Between.
        }

        {
        elim (eq_dec_points R X1); intro HRX1; treat_equalities.

          {
          exfalso; apply HNC; assert_cols; Col.
          }

          {
          exists X1; split.

            {
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists Q; Col.
            }

            {
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; split; Col; Between.
            }
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col Q B X2 ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Bet X1 R A ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_3_1_2_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_3_1_2_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_3_1_2_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col Q B X2 ->
  Bet P Q X1 ->
  Bet R X2 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_3_1_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_3_1_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_3_1_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col Q B X2 ->
  Bet P Q X1 ->
  Bet X2 P R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol3 HCol4 HCol1 HCol2.
assert (H := outer_pasch R X1 P X2 Q (between_symmetry X2 P R HCol2) (between_symmetry P Q X1 HCol1));
destruct H as [I [HRX1I HQX2I]].
exists I; right; right.
elim (eq_dec_points X2 Q); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  elim (eq_dec_points R X1); intro HRX1; treat_equalities.

    {
    exfalso; apply HNC; assert_cols; Col.
    }

    {
    split; assert_cols; ColR.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col Q B X2 ->
  Bet Q X1 P ->
  Bet R X2 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol3 HCol4 HCol1 HCol2.
assert (H := inner_pasch Q R P X1 X2 HCol1 HCol2); destruct H as [I [HRX1I HQX2I]].
elim (eq_dec_points R X1); intro HRX1; elim (eq_dec_points Q X2); intro HQX2;
treat_equalities; Cop.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  exists I; right; right; assert_cols; split; ColR.
  }
Qed.

Lemma coplanar_trans_1_aux_3_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col Q B X2 ->
  Bet Q X1 P ->
  Bet X2 P R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol3 HCol4 HCol1 HCol2.
assert (H := outer_pasch X2 Q P R X1 HCol2 HCol1); destruct H as [I [HRX1I HQX2I]].
elim (eq_dec_points R X1); intro HRX1; elim (eq_dec_points Q X2); intro HQX2;
treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  exists I; right; right; assert_cols; split; ColR.
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet R A X1 ->
  Bet Q B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points B X2); intro HBX2; elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HABR; Col.
  }

  {
  assert (H := inner_pasch Q R X1 P A (between_symmetry X1 P Q HCol1) HCol3);
  destruct H as [I [HPRI HQAI]]; exists I; right; left; assert_diffs; assert_cols; split; ColR.
  }

  {
  Cop.
  }

  {
  assert (HTS : TS R B A Q).
    {
    apply l9_8_2 with X1.

      {
      apply l9_8_2 with X2.

        {
        split; try (intro; apply HBQR; assert_cols; ColR).
        split; Col.
        exists B; split; Col; Between.
        }

        {
        apply one_side_transitivity with P.

          {
          apply one_side_symmetry.
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B R) by (assert_cols; Col).
          assert (H3 : Col P X2 R) by (assert_cols; Col).
          assert (H := l9_19 R B P X2 R H1 H2 H3); rewrite H.
          split; try (intro;  apply HNC; assert_diffs; assert_cols; ColR).
          split; assert_diffs; Col.
          split; try (intro; treat_equalities); Between.
          }

          {
          assert (H := inner_pasch Q R X2 B P HCol4 (between_symmetry X2 P R HCol2)).
          destruct H as [I [HRBI HPQI]].
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B I) by (assert_cols; Col).
          assert (H3 : Col P X1 I) by (assert_diffs; assert_cols; ColR).
          assert (H := l9_19 R B P X1 I H1 H2 H3); rewrite H.
          split; try (intro;  apply HNC; assert_diffs; assert_cols; ColR).
          split; try (intro; treat_equalities; apply HNC; assert_diffs; assert_cols; ColR).
          split; try (intro; treat_equalities; apply HAPR; Col).
          left; eBetween.
          }
        }
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> B) by (assert_diffs; auto).
      assert (H2 : Col R B R) by (assert_cols; Col).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      }
    }
  destruct HTS as [H1 [H2 [I [HRBI HAQI]]]]; clear H1; clear H2.
  exists I; right; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet R A X1 ->
  Bet B X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : TS Q A B R).
    {
    apply l9_8_2 with X2.

      {
      split; try (intro; assert_cols; apply HABQ; ColR).
      split; Col.
      destruct (inner_pasch Q R X1 P A (between_symmetry X1 P Q HCol1) HCol3) as [I [HPRI HQAI]].
      exists I; split; Col.
      eBetween.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by (assert_cols; Col).
      assert (H3 : Col B X2 Q) by (assert_cols; Col).
      assert (H := l9_19 Q A B X2 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; Col.
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HRBI HAQI]]]]; clear H1; clear H2.
  exists I; right; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet R A X1 ->
  Bet X2 Q B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : TS Q R A B).
    {
    apply l9_8_2 with X2.

      {
      split; try (intro; apply HBQR; assert_cols; ColR).
      split; Col.
      exists Q; split; Col; Between.
      }

      {
      apply one_side_transitivity with P.

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by (assert_cols; Col).
        assert (H3 : Col P X2 R) by (assert_cols; Col).
        assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; try (intro; treat_equalities); Between.
        }

        {
        apply one_side_transitivity with X1.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R Q) by (assert_cols; Col).
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          split; try (intro; treat_equalities); Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R R) by (assert_cols; Col).
          assert (H3 : Col A X1 R) by (assert_cols; Col).
          assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col Q B X2 ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet R A X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_3_3_3_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_3_3_3_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_3_3_3_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet A X1 R ->
  Bet Q B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points B X2); intro HBX2; elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (H := outer_pasch A Q X1 R P HCol3 (between_symmetry X1 P Q HCol1));
  destruct H as [I [HQAI HPRI]]; exists I; right; left; assert_diffs; assert_cols; split; ColR.
  }

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (HTS : TS R B A Q).
    {
    apply l9_8_2 with X1.

      {
      apply l9_8_2 with X2.

        {
        split; try (intro; apply HBQR; assert_cols; ColR).
        split; Col.
        exists B; split; Col; Between.
        }

        {
        apply one_side_transitivity with P.

          {
          apply one_side_symmetry.
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B R) by (assert_cols; Col).
          assert (H3 : Col P X2 R) by (assert_cols; Col).
          assert (H := l9_19 R B P X2 R H1 H2 H3); rewrite H.
          split; try (intro;  apply HNC; assert_diffs; assert_cols; ColR).
          split; assert_diffs; Col.
          split; try (intro; treat_equalities); Between.
          }

          {
          assert (H := inner_pasch Q R X2 B P HCol4 (between_symmetry X2 P R HCol2)).
          destruct H as [I [HRBI HPQI]].
          assert (H1 : R <> B) by (assert_diffs; auto).
          assert (H2 : Col R B I) by (assert_cols; Col).
          assert (H3 : Col P X1 I) by (assert_diffs; assert_cols; ColR).
          assert (H := l9_19 R B P X1 I H1 H2 H3); rewrite H.
          split; try (intro;  apply HNC; assert_diffs; assert_cols; ColR).
          split; try (intro; treat_equalities; apply HNC; assert_diffs; assert_cols; ColR).
          split; try (intro; treat_equalities; apply HAPR; Col).
          left; eBetween.
          }
        }
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> B) by (assert_diffs; auto).
      assert (H2 : Col R B R) by (assert_cols; Col).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col; Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HRBI HAQI]]]]; clear H1; clear H2.
  exists I; right; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet A X1 R ->
  Bet B X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch B R X2 Q P HCol4 (between_symmetry X2 P R HCol2));
destruct H as [I [HRBI HPQI]]; assert (HPQ : Q <> P) by (assert_diffs; Col).
assert (H := l5_2 Q P X1 I HPQ (between_symmetry X1 P Q HCol1) HPQI); clear HPQ;
elim (eq_dec_points P I); intro HPI; treat_equalities.

  {
  elim (eq_dec_points B X2); intro; treat_equalities.

    {
    clear H; assert (H := outer_pasch A Q X1 R P HCol3 (between_symmetry X1 P Q HCol1));
    destruct H as [I [HQAI HPRI]].
    exists I; right; left; assert_diffs; assert_cols; split; ColR.
    }

    {
    exfalso; apply HNC; assert_diffs; assert_cols; ColR.
    }
  }

  {
  elim (eq_dec_points X1 I); intro HX1I; treat_equalities.

    {
    elim (eq_dec_points R X1); intro; treat_equalities.

      {
      exfalso; apply HNC; assert_cols; Col.
      }

      {
      exfalso; apply HABR; assert_cols; ColR.
      }
    }

    {
    elim H; clear H; intro HPX1I.

      {
      assert (HTS : TS R A Q B).
        {
        apply l9_31.

          {
          apply one_side_transitivity with P.

            {
            apply one_side_transitivity with X1.

              {
              assert (H1 : R <> Q) by (assert_diffs; auto).
              assert (H2 : Col R Q R) by (assert_cols; Col).
              assert (H3 : Col A X1 R) by (assert_cols; Col).
              assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              split; try (intro; treat_equalities); Between.
              apply HNC; assert_cols; ColR.
              }

              {
              apply one_side_symmetry.
              assert (H1 : R <> Q) by (assert_diffs; auto).
              assert (H2 : Col R Q Q) by (assert_cols; Col).
              assert (H3 : Col P X1 Q) by (assert_cols; Col).
              assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              split; try (intro; treat_equalities); Between.
              }
            }

            {
            apply one_side_transitivity with X2.

              {
              assert (H1 : R <> Q) by (assert_diffs; auto).
              assert (H2 : Col R Q R) by (assert_cols; Col).
              assert (H3 : Col P X2 R) by (assert_cols; Col).
              assert (H := l9_19 R Q P X2 R H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              split; try (intro; treat_equalities); Between.
              }

              {
              apply one_side_symmetry.
              assert (H1 : R <> Q) by (assert_diffs; auto).
              assert (H2 : Col R Q Q) by (assert_cols; Col).
              assert (H3 : Col B X2 Q) by (assert_cols; Col).
              assert (H := l9_19 R Q B X2 Q H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              split; try (intro; treat_equalities); Between.
              apply HNC; assert_cols; Col.
              }
            }
          }

          {
          apply one_side_transitivity with P.

            {
            apply one_side_transitivity with X1.

              {
              assert (H1 : R <> B) by (assert_diffs; auto).
              assert (H2 : Col R B R) by (assert_cols; Col).
              assert (H3 : Col A X1 R) by (assert_cols; Col).
              assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              split; try (intro; treat_equalities); Between.
              apply HNC; assert_cols; ColR.
              }

              {
              apply one_side_symmetry.
              assert (H1 : R <> B) by (assert_diffs; auto).
              assert (H2 : Col R B I) by (assert_cols; Col).
              assert (H3 : Col P X1 I) by (assert_cols; Col).
              assert (H := l9_19 R B P X1 I H1 H2 H3); rewrite H.
              split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
              split; Col.
              split; Between.
              }
            }

            {
            assert (H1 : R <> B) by (assert_diffs; auto).
            assert (H2 : Col R B I) by (assert_cols; Col).
            assert (H3 : Col P Q I) by (assert_cols; Col).
            assert (H := l9_19 R B P Q I H1 H2 H3); rewrite H.
            split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
            split; Col.
            split; try (intro; treat_equalities; apply HNC; Col).
            Between.
            }
          }
        }
      destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
      exists I'; right; right; assert_cols; Col.
      }

      {
      elim (eq_dec_points R X1); intro HRX1; treat_equalities.

        {
        exfalso; apply HNC; assert_cols; Col.
        }

        {
        assert (HTS : TS R B A Q).
          {
          apply l9_8_2 with X1.

            {
            split; try (intro; apply HABR; assert_cols; ColR).
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
            split; assert_diffs; Col.
            split; Between.
            }
          }
        destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
        exists I'; right; left; assert_cols; Col.
        }
      }
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet A X1 R ->
  Bet X2 Q B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : TS Q R A B).
    {
    apply l9_8_2 with X2.

      {
      split; try (intro; apply HBQR; assert_cols; ColR).
      split; Col.
      exists Q; split; Col; Between.
      }

      {
      apply one_side_transitivity with P.

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by (assert_cols; Col).
        assert (H3 : Col P X2 R) by (assert_cols; Col).
        assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; try (intro; treat_equalities); Between.
        }

        {
        apply one_side_transitivity with X1.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R Q) by (assert_cols; Col).
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          split; try (intro; treat_equalities); Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R R) by (assert_cols; Col).
          assert (H3 : Col A X1 R) by (assert_cols; Col).
          assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          split; Between.
          intro; subst; apply HNC; assert_cols; Col.
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col Q B X2 ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet A X1 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_3_3_3_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_3_3_3_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_3_3_3_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet X1 R A ->
  Bet Q B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : TS Q R B A).
    {
    apply l9_8_2 with X1.

      {
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists R; split; Col; Between.
      }

      {
      apply one_side_transitivity with P.

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R Q) by (assert_cols; Col).
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; try (intro; treat_equalities); Between.
        }

        {
        apply one_side_transitivity with X2.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R R) by (assert_cols; Col).
          assert (H3 : Col P X2 R) by (assert_cols; Col).
          assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          split; try (intro; treat_equalities); Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R Q) by (assert_cols; Col).
          assert (H3 : Col B X2 Q) by (assert_cols; Col).
          assert (H := l9_19 Q R B X2 Q H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet X1 R A ->
  Bet B X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : TS Q R B A).
    {
    apply l9_8_2 with X1.

      {
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists R; split; Col; Between.
      }

      {
      apply one_side_transitivity with P.

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R Q) by (assert_cols; Col).
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 Q R P X1 Q H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; try (intro; treat_equalities); Between.
        }

        {
        apply one_side_transitivity with X2.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R R) by (assert_cols; Col).
          assert (H3 : Col P X2 R) by (assert_cols; Col).
          assert (H := l9_19 Q R P X2 R H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          split; try (intro; treat_equalities); Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R Q) by (assert_cols; Col).
          assert (H3 : Col B X2 Q) by (assert_cols; Col).
          assert (H := l9_19 Q R B X2 Q H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          split; Between.
          intro; subst; apply HNC; assert_cols; Col.
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; assert_cols; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet X1 R A ->
  Bet X2 Q B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (H1 := inner_pasch Q A X1 P R); assert (H2 := inner_pasch R B X2 P Q);
assert (H1' := H1 (between_symmetry X1 P Q HCol1) (between_symmetry X1 R A HCol3));
assert (H2' := H2 (between_symmetry X2 P R HCol2) (between_symmetry X2 Q B HCol4));
destruct H1' as [I1 [HPAI1 HQRI1]]; clear H1;
destruct H2' as [I2 [HPBI2 HQRI2]]; clear H2.
assert (H := l5_3 Q I1 I2 R (between_symmetry R I1 Q HQRI1) HQRI2);
elim H; clear H; intro HQI1I2.

  {
  assert (H := outer_pasch B Q I2 P I1 (between_symmetry P I2 B HPBI2) HQI1I2);
  destruct H as [I [HQBI HPI1I]].
  elim (eq_dec_points P I1); intro HPI1; treat_equalities.

    {
    exfalso; apply HNC; assert_cols; Col.
    }

    {
    assert (H := l5_1 P I1 A I HPI1 HPAI1 HPI1I); elim H; clear H; intro HPAI.

      {
      assert (HTS : TS Q A B R).
        {
        apply l9_31.

          {
          apply one_side_transitivity with P.

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            assert (H2 : Col Q B I) by (assert_cols; Col).
            assert (H3 : Col A P I) by (assert_cols; Col).
            assert (H := l9_19 Q B A P I H1 H2 H3); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; apply HABQ; Col).
            split; try (intro; treat_equalities); Between.
            }

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            assert (H2 : Col Q B X2) by (assert_cols; Col).
            assert (H3 : Col P R X2) by (assert_cols; Col).
            assert (H := l9_19 Q B P R X2 H1 H2 H3); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; apply HBPQ; Col).
            split; try (intro; treat_equalities); Between.
            }
          }

          {
          exists P; split.

            {
            split; Col.
            split; Col.
            exists I1; assert_cols; split; Col; Between.
            }

            {
            split; Col.
            split; Col.
            exists I2; assert_cols; split; Col; Between.
            }
          }
        }
      destruct HTS as [H1 [H2 [I' [HQAI' HRBI']]]]; clear H1; clear H2.
      exists I'; right; left; assert_cols; Col.
      }

      {
      assert (HTS : TS Q B R A).
        {
        apply l9_8_2 with P.

          {
          split; Col.
          split; Col.
          exists I; assert_cols; split; Col; Between.
          }

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          assert (H2 : Col Q B X2) by (assert_cols; Col).
          assert (H3 : Col P R X2) by (assert_cols; Col).
          assert (H := l9_19 Q B P R X2 H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; apply HBPQ; Col).
          split; try (intro; treat_equalities); Between.
          }
        }
      destruct HTS as [H1 [H2 [I' [HQBI' HRAI']]]]; clear H1; clear H2.
      exists I'; right; right; assert_cols; Col.
      }
    }
  }

  {
  assert (H := outer_pasch A Q I1 P I2 (between_symmetry P I1 A HPAI1) HQI1I2);
  destruct H as [I [HQAI HPI2I]].
  elim (eq_dec_points P I2); intro HPI2; treat_equalities.

    {
    exfalso; apply HNC; assert_cols; Col.
    }

    {
    assert (H := l5_1 P I2 B I HPI2 HPBI2 HPI2I); elim H; clear H; intro HPBI.

      {
      assert (HTS : TS Q B A R).
        {
        apply l9_31.

          {
          apply one_side_transitivity with P.

            {
            assert (H1 : Q <> A) by (assert_diffs; auto).
            assert (H2 : Col Q A I) by (assert_cols; Col).
            assert (H3 : Col B P I) by (assert_cols; Col).
            assert (H := l9_19 Q A B P I H1 H2 H3); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; apply HABQ; Col).
            split; try (intro; treat_equalities); Between.
            }

            {
            apply one_side_transitivity with I1.

              {
              assert (H1 : Q <> A) by (assert_diffs; auto).
              assert (H2 : Col Q A A) by (assert_cols; Col).
              assert (H3 : Col P I1 A) by (assert_cols; Col).
              assert (H := l9_19 Q A P I1 A H1 H2 H3); rewrite H.
              elim (eq_dec_points A X1); intro HAX1; treat_equalities.

                {
                exfalso; apply HNC; assert_cols; Col.
                }

                {
                split; try (intro; assert_diffs; assert_cols; apply HNC; ColR).
                split; try (intro; treat_equalities; apply HNC; assert_cols; Col).
                split; try (intro; treat_equalities; apply HAQR; assert_cols; Col).
                Between.
                }
              }

              {
              apply one_side_symmetry.
              assert (H1 : Q <> A) by (assert_diffs; auto).
              assert (H2 : Col Q A Q) by (assert_cols; Col).
              assert (H3 : Col R I1 Q) by (assert_cols; Col).
              assert (H := l9_19 Q A R I1 Q H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              split; try (intro; treat_equalities; apply HBPQ; assert_cols; ColR).
              Between.
              }
            }
          }

          {
          exists P; split.

            {
            split; Col.
            split; Col.
            exists I2; assert_cols; split; Col; Between.
            }

            {
            split; Col.
            split; Col.
            exists I1; assert_cols; split; Col; Between.
            }
          }
        }
      destruct HTS as [H1 [H2 [I' [HQBI' HRAI']]]]; clear H1; clear H2.
      exists I'; right; right; assert_cols; Col.
      }

      {
      assert (HTS : TS Q A R B).
        {
        apply l9_8_2 with P.

          {
          assert_diffs.
          elim (eq_dec_points P I); intro HPI; treat_equalities.

            {
            intuition.
            }

            {
            split; try (intro; apply HABQ; assert_cols; ColR).
            split; Col.
            exists I; assert_cols; split; Col; Between.
            }
          }

          {
          apply one_side_transitivity with X1.

            {
            assert (H1 : Q <> A) by (assert_diffs; auto).
            assert (H2 : Col Q A Q) by (assert_cols; Col).
            assert (H3 : Col P X1 Q) by (assert_cols; Col).
            assert (H := l9_19 Q A P X1 Q H1 H2 H3); rewrite H.
            elim (eq_dec_points P I); intro HPI; treat_equalities.

              {
              intuition.
              }

              {
              split; try (intro; apply HABQ; assert_cols; ColR).
              split; assert_diffs; Col.
              split; try (intro; treat_equalities); Between.
              }
            }

            {
            apply one_side_symmetry.
            assert (H1 : Q <> A) by (assert_diffs; auto).
            assert (H2 : Col Q A A) by (assert_cols; Col).
            assert (H3 : Col R X1 A) by (assert_cols; Col).
            assert (H := l9_19 Q A R X1 A H1 H2 H3); rewrite H.
            split; Col.
            split; assert_diffs; Col.
            split; try (intro; treat_equalities); Between.
            }
          }
        }
      destruct HTS as [H1 [H2 [I' [HQAI' HRBI']]]]; clear H1; clear H2.
      exists I'; right; left; assert_cols; Col.
      }
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col Q B X2 ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Bet X1 R A ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_3_3_3_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_3_3_3_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_3_3_3_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A P R ->
  ~ Col A Q R ->
  ~ Col B P Q ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col Q B X2 ->
  Bet X1 P Q ->
  Bet X2 P R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_3_3_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_3_3_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_3_3_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col R A X1 ->
  Col P R X2 ->
  Col Q B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (Col_dec A P R); intro HAPR.

  {
  exists X2; right; right.
  assert_diffs; split; ColR.
  }

  {
  elim (Col_dec B P Q); intro HBPQ.

    {
    exists X1; right; right.
    assert_diffs; split; ColR.
    }

    {
    elim HCol1; clear HCol1; intro HCol1; elim HCol3; clear HCol3; intro HCol3.

      {
      apply coplanar_trans_1_aux_3_1_1 with P X1 X2; assumption.
      }

      {
      elim HCol3; clear HCol3; intro HCol3.

        {
        apply coplanar_trans_1_aux_3_1_2 with P X1 X2; assumption.
        }

        {
        apply coplanar_trans_1_aux_3_1_3 with P X1 X2; assumption.
        }
      }

      {
      elim HCol1; clear HCol1; intro HCol1.

        {
        assert (H : Coplanar R Q B A) by (apply coplanar_trans_1_aux_3_1_2 with P X2 X1; Col); Cop.
        }

        {
        assert (H : Coplanar R Q B A) by (apply coplanar_trans_1_aux_3_1_3 with P X2 X1; Col); Cop.
        }
      }

      {
      elim HCol1; clear HCol1; intro HCol1; elim HCol3; clear HCol3; intro HCol3.

        {
        apply coplanar_trans_1_aux_3_2_2 with P X1 X2; assumption.
        }

        {
        apply coplanar_trans_1_aux_3_2_3 with P X1 X2; assumption.
        }

        {
        assert (H : Coplanar R Q B A) by (apply coplanar_trans_1_aux_3_2_3 with P X2 X1; Col); Cop.
        }

        {
        apply coplanar_trans_1_aux_3_3_3 with P X1 X2; assumption.
        }
      }
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet R A X1 ->
  Bet P B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  exfalso; apply HAQR; assert_cols; Col.
  }

  {
  assert (HTS : TS Q R B A).
    {
    apply l9_8_2 with P.

      {
      apply l9_2; apply l9_8_2 with X1.

        {
        split; try (intro; apply HNC; assert_cols; ColR).
        split; Col.
        exists Q; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by (assert_cols; Col).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        }
      }

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R X2) by (assert_cols; Col).
      assert (H3 : Col P B X2) by (assert_cols; Col).
      assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; apply HNC; Col).
      split; try (intro; treat_equalities; apply HBQR; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_1_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R A X1 ->
  Bet B X2 P ->
  Bet Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (HTS : TS R A Q B).
    {
    apply l9_31.

      {
      exists P; split.

        {
        apply l9_8_2 with X1.

          {
          split; try (intro; apply HAQR; assert_cols; ColR).
          split; Col.
          exists Q; split; Col; Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q R) by (assert_cols; Col).
          assert (H3 : Col A X1 R) by (assert_cols; Col).
          assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          }
        }

        {
        split; Col.
        split; Col.
        exists X2; assert_cols; split; Col; Between.
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
        split; assert_diffs; Col.
        }

        {
        apply one_side_symmetry.
        assert (H := outer_pasch P Q X2 B R (between_symmetry B X2 P HCol3) HCol4);
        destruct H as [I [HPQI HRBI]].
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B I) by (assert_cols; Col).
        assert (H3 : Col Q X1 I) by (assert_diffs; assert_cols; ColR).
        assert (H := l9_19 R B Q X1 I H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; apply HBQR; Col).
        split; try (intro; treat_equalities; apply HABR; assert_cols; ColR).
        eBetween.
        }
      }
    }
  destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
  exists I; right; right; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_1_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R A X1 ->
  Bet B X2 P ->
  Bet R X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch X1 R Q P X2 (between_symmetry P Q X1 HCol1) HCol4);
destruct H as [I [HRX1I HPX2I]].
elim (eq_dec_points P X2); intro HPX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (H := l5_2 P X2 B I HPX2 (between_symmetry B X2 P HCol3) HPX2I);
  elim H; clear H; intro HX2BI.

    {
    assert (HTS : TS R B Q A).
      {
      apply l9_31.

        {
        exists P; split.

          {
          split; Col.
          split; Col.
          exists X2; assert_cols; split; Col; Between.
          }

          {
          split; Col.
          split; Col.
          destruct (inner_pasch P R X1 Q A HCol1 HCol2) as [I' [HQRI' HPAI']].
          exists I'; assert_cols; split; Col.
          }
        }

        {
        apply one_side_transitivity with P.

          {
          elim (eq_dec_points R X1); intro HRX1; treat_equalities.

            {
            exfalso; apply HABR; Col.
            }

            {
            assert (H1 : R <> A) by (assert_diffs; auto).
            assert (H2 : Col R A I) by (assert_cols; ColR).
            assert (H3 : Col B P I) by (assert_cols; ColR).
            assert (H := l9_19 R A B P I H1 H2 H3); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; apply HABR; Col).
            split; try (intro; treat_equalities; apply HNC; assert_cols; Col).
            eBetween.
            }
          }

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A X1) by (assert_cols; Col).
          assert (H3 : Col P Q X1) by (assert_cols; ColR).
          assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
          elim (eq_dec_points P X1); intro HPX1; treat_equalities.

            {
            exfalso; apply HNC; Col.
            }

            {
            split; try (intro; apply HNC; assert_cols; ColR).
            split; Col.
            split; try (intro; treat_equalities; apply HAQR; Col).
            Between.
            }
          }
        }
      }
    destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
    exists I'; right; left; split; Col.
    }

    {
    assert (HTS : TS R A Q B).
      {
      apply l9_8_2 with P.

        {
        assert_diffs.
        elim (eq_dec_points P X1); intro HPX1; treat_equalities.

          {
          exfalso; apply HNC; Col.
          }

          {
          split; try (intro; apply HNC; assert_cols; ColR).
          split; Col.
          elim (eq_dec_points R X1); intro HRX1; treat_equalities.

            {
            exfalso; apply HABR; Col.
            }

            {
            exists I; assert_cols; split; eBetween; ColR.
            }
          }
        }

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col P Q X1) by (assert_cols; ColR).
        assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
        elim (eq_dec_points P X1); intro HPX1; treat_equalities.

          {
          exfalso; apply HNC; Col.
          }

          {
          split; try (intro; apply HNC; assert_cols; ColR).
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; Col).
          Between.
          }
        }
      }
    destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
    exists I'; right; right; split; Col.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_1_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet R A X1 ->
  Bet B X2 P ->
  Bet X2 Q R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (HTS : TS Q A R B).
    {
    apply l9_31.

      {
      exists P; split.

        {
        apply l9_8_2 with X1.

          {
          split; try (intro; apply HAQR; assert_cols; ColR).
          split; Col.
          exists Q; split; Col; Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> R) by (assert_diffs; auto).
          assert (H2 : Col Q R R) by (assert_cols; Col).
          assert (H3 : Col A X1 R) by (assert_cols; Col).
          assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          }
        }

        {
        split; Col.
        split; Col.
        exists X2; assert_cols; split; Col; Between.
        }
      }

      {
      elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

        {
        assert (H1 : Q <> B) by (assert_diffs; auto).
        assert (H2 : Col Q B X1) by (assert_diffs; assert_cols; ColR).
        assert (H3 : Col A R X1) by (assert_cols; Col).
        assert (H := l9_19 Q B A R X1 H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; apply HABQ; assert_cols; Col).
        Between.
        }

        {
        apply one_side_symmetry; apply l9_17 with X1; Col.
        assert (HBPQ : ~ Col B P Q).
          {
          intro; apply HQX2; assert_cols; apply l6_21 with R Q P B; Col.
          intro; treat_equalities; apply HNC; Col.
          }
        exists P; split.

          {
          apply between_symmetry in HCol3; apply between_symmetry in HCol4.
          assert (H := outer_pasch P R X2 B Q HCol3 HCol4); destruct H as [I [HPRI HQBI]].
          split; Col.
          split; Col.
          exists I; assert_cols; split; Col; Between.
          }

          {
          elim (eq_dec_points Q X1); intro; treat_equalities.

            {
            exfalso; apply HAQR; assert_cols; Col.
            }

            {
            split; try (intro; apply HBPQ; assert_cols; ColR).
            split; Col.
            exists Q; split; Col; Between.
            }
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
  exists I; right; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet R A X1 ->
  Bet B X2 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_1_1_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_1_1_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_1_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet R A X1 ->
  Bet X2 P B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  exfalso; apply HAQR; assert_cols; Col.
  }

  {
  assert (HTS : TS Q R B A).
    {
    apply l9_8_2 with P.

      {
      apply l9_2; apply l9_8_2 with X1.

        {
        split; try (intro; apply HNC; assert_cols; ColR).
        split; Col.
        exists Q; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by (assert_cols; Col).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        }
      }

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R X2) by (assert_cols; Col).
      assert (H3 : Col P B X2) by (assert_cols; Col).
      assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; apply HNC; Col).
      split; try (intro; treat_equalities; apply HBQR; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet R A X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_1_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_1_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet A X1 R ->
  Bet P B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  exfalso; apply HAQR; assert_cols; Col.
  }

  {
  assert (HTS : TS Q R B A).
    {
    apply l9_8_2 with P.

      {
      apply l9_2; apply l9_8_2 with X1.

        {
        split; try (intro; apply HNC; assert_cols; ColR).
        split; Col.
        exists Q; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by (assert_cols; Col).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; try (intro; treat_equalities); Between.
        }
      }

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R X2) by (assert_cols; Col).
      assert (H3 : Col P B X2) by (assert_cols; Col).
      assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; apply HNC; Col).
      split; try (intro; treat_equalities; apply HBQR; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_2_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet A X1 R ->
  Bet B X2 P ->
  Bet Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R A Q B).
  {
  elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    elim (eq_dec_points P X1); intro HPX1; treat_equalities.

      {
      intuition.
      }

      {
      assert (HAPR : ~ Col A P R).
        {
        intro; apply HNC; assert_diffs; assert_cols; ColR.
        }
      apply l9_8_2 with P.

        {
        split; Col.
        split; Col.
        exists R; split; Col; Between.
        }

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col P Q X1) by (assert_cols; Col).
        assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
        split; Col.
        split; Col.
        split; try (intro; treat_equalities; apply HAQR; Col).
        Between.
        }
      }
    }

    {
    apply l9_2; apply l9_8_2 with X2.

      {
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists R; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H := outer_pasch P X2 Q X1 R HCol1 (between_symmetry Q R X2 HCol4)).
      destruct H as [I [HPX2I HRX1I]]; elim (eq_dec_points R X1); intro HRX1; treat_equalities.

        {
        exfalso; apply HNC; assert_cols; Col.
        }

        {
        elim (eq_dec_points P X2); intro HPX2; treat_equalities.

          {
          exfalso; apply HNC; assert_cols; Col.
          }

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A I) by (assert_diffs; assert_cols; ColR).
          assert (H3 : Col B X2 I) by (assert_cols; ColR).
          assert (H := l9_19 R A B X2 I H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; apply HABR; Col).
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          eBetween.
          }
        }
      }
    }
  }
destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
exists I; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_1_2_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet A X1 R ->
  Bet B X2 P ->
  Bet R X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points P X2); intro HPX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

    {
    exfalso; apply HAQR; assert_cols; Col.
    }

    {
    elim (eq_dec_points R X1); intro HRX1; treat_equalities.

      {
      exfalso; apply HNC; assert_cols; Col.
      }

      {
      assert (H := outer_pasch X1 R Q P X2 (between_symmetry P Q X1 HCol1) HCol4);
      destruct H as [I [HRX1I HPX2I]].
      elim (l5_2 P X2 B I HPX2 (between_symmetry B X2 P HCol3) HPX2I); intro HX2BI.

        {
        assert (HTS : TS R B Q A).
          {
          apply l9_31.

            {
            apply one_side_transitivity with X1.

              {
              exists P; split.

                {
                split; Col.
                split; Col.
                exists X2; assert_cols; split; Col.
                }

                {
                apply l9_2.
                split; Col.
                split; try (intro; apply HNC; assert_cols; ColR).
                exists Q; Col.
                }
              }

              {
              apply one_side_symmetry.
              assert (H1 : R <> Q) by (assert_diffs; auto).
              assert (H2 : Col R Q R) by Col.
              assert (H3 : Col A X1 R) by (assert_cols; ColR).
              assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              split; try (intro; treat_equalities; apply HNC; assert_cols; Col).
              Between.
              }
            }

            {
            apply one_side_transitivity with P.

              {
              assert (H1 : R <> A) by (assert_diffs; auto).
              assert (H2 : Col R A I) by (assert_cols; ColR).
              assert (H3 : Col B P I) by (assert_cols; ColR).
              assert (H := l9_19 R A B P I H1 H2 H3); rewrite H.
              split; Col.
              split; try (intro; treat_equalities; apply HABR; Col).
              split; try (intro; treat_equalities; apply HNC; assert_cols; Col).
              eBetween.
              }

              {
              assert (H1 : R <> A) by (assert_diffs; auto).
              assert (H2 : Col R A X1) by (assert_cols; Col).
              assert (H3 : Col P Q X1) by (assert_cols; Col).
              assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
              show_distinct P X1; try (apply HAQR; Col).
              split; try (intro; apply HAQR; assert_cols; ColR).
              split; Col.
              split; Between.
              }
            }
          }
        destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
        exists I'; right; left; split; Col.
        }

        {
        assert (HTS : TS R A Q B).
          {
          apply l9_8_2 with P.

            {
            show_distinct P X1; try (apply HAQR; Col).
            assert_diffs.
            split; try (intro; apply HAQR; assert_cols; ColR).
            split; Col.
            exists I; assert_cols; split; eBetween; ColR.
            }

            {
            assert (H1 : R <> A) by (assert_diffs; auto).
            assert (H2 : Col R A X1) by (assert_cols; Col).
            assert (H3 : Col P Q X1) by (assert_cols; Col).
            assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
            show_distinct P X1; try (apply HAQR; Col).
            split; try (intro; apply HAQR; assert_cols; ColR).
            split; Col.
            split; Between.
            }
          }
        destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
        exists I'; right; right; split; Col.
        }
      }
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_2_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet A X1 R ->
  Bet B X2 P ->
  Bet X2 Q R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch B R X2 P Q HCol3 (between_symmetry X2 Q R HCol4));
destruct H as [I [HRBI HPQI]].
assert (HPQ : P <> Q) by (assert_diffs; Col).
assert (H := l5_2 P Q X1 I HPQ HCol1 HPQI); elim H; clear HPQ; clear H; intro HQX1I.

  {
  assert (HTS : TS R A Q B).
    {
    apply l9_31.

      {
      exists P; split.

        {
        apply l9_8_2 with X1.

          {
          show_distinct Q X1; assert_cols; Col.
          split; try (intro; apply HNC; ColR).
          split; Col.
          exists Q; split; Col; Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : R <> Q) by (assert_diffs; auto).
          assert (H2 : Col R Q R) by (assert_cols; Col).
          assert (H3 : Col A X1 R) by (assert_cols; Col).
          assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
          split; Col.
          split; assert_diffs; Col.
          split; try (intro; treat_equalities; assert_cols); Between.
          }
        }

        {
        split; Col.
        split; Col.
        exists X2; assert_cols; split; Col.
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
        split; assert_diffs; Col.
        split; try (intro; treat_equalities; assert_cols); Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> B) by (assert_diffs; auto).
        assert (H2 : Col R B I) by (assert_cols; Col).
        assert (H3 : Col Q X1 I) by (assert_cols; Col).
        assert (H := l9_19 R B Q X1 I H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        show_distinct R X1; assert_cols; Col.
        split; try (intro; treat_equalities; apply HABR; ColR).
        Between.
        }
      }
    }
  destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
  exists I'; right; right; split; Col.
  }

  {
  assert (HTS : TS R B A Q).
    {
    apply l9_8_2 with X1.

      {
      show_distinct R X1; assert_cols; Col.
      split; try (intro; treat_equalities; apply HABR; ColR).
      split; Col.
      exists I; assert_cols; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> B) by (assert_diffs; auto).
      assert (H2 : Col R B R) by (assert_cols; Col).
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 R B A X1 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet A X1 R ->
  Bet B X2 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_1_2_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_1_2_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_2_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet A X1 R ->
  Bet X2 P B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  exfalso; apply HAQR; assert_cols; Col.
  }

  {
  assert (HTS : TS Q R B A).
    {
    apply l9_8_2 with P.

      {
      apply l9_2; apply l9_8_2 with X1.

        {
        split; try (intro; apply HNC; assert_cols; ColR).
        split; Col.
        exists Q; split; Col; Between.
        }

        {
        apply one_side_symmetry.
        assert (H1 : Q <> R) by (assert_diffs; auto).
        assert (H2 : Col Q R R) by (assert_cols; Col).
        assert (H3 : Col A X1 R) by (assert_cols; Col).
        assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; try (intro; treat_equalities); Between.
        }
      }

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R X2) by (assert_cols; Col).
      assert (H3 : Col P B X2) by (assert_cols; Col).
      assert (H := l9_19 Q R P B X2 H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; apply HNC; Col).
      split; try (intro; treat_equalities; apply HBQR; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
  exists I; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet A X1 R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_1_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_1_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_3_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet P B X2 ->
  Bet Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch P X2 Q X1 R HCol1 (between_symmetry Q R X2 HCol4));
destruct H as [I[HPX2I HRX1I]].
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
assert (HRAI : Col R A I) by (assert_cols; ColR).
assert (H := l5_3 P B I X2 HCol3 HPX2I); elim H; clear H; intro HPBI.

  {
  assert (HTS : TS R B Q A).
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
        exists X1; split.

          {
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          exists Q; Col.
          }

          {
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          exists R; split; Col; Between.
          }
        }
      }

      {
      apply one_side_transitivity with P.

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A I) by Col.
        assert (H3 : Col B P I) by (assert_cols; Col).
        assert (H := l9_19 R A B P I H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities; Col).
        Between.
        }

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col P Q X1) by (assert_cols; Col).
        assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
        show_distinct P X1; Col.
        split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
        split; Col.
        split; try (intro; treat_equalities; Col).
        Between.
        }
      }
    }
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : TS R A Q B).
    {
    apply l9_8_2 with P.

      {
      show_distinct P X1; Col.
      split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
      split; Col.
      exists I; split; Col.
      }

      {
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A X1) by (assert_cols; Col).
      assert (H3 : Col P Q X1) by (assert_cols; Col).
      assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
      show_distinct P X1; Col.
      split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
      split; Col.
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
  exists I'; right; right; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_3_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet P B X2 ->
  Bet R X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
elim (eq_dec_points R X2); intro HRX2; treat_equalities.

  {
  assert (HTS : TS R B Q A).
    {
    apply l9_8_2 with X1.

      {
      split; try (intro; apply HABR; assert_cols; ColR).
      split; Col.
      exists R; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> B) by (assert_diffs; auto).
      assert (H2 : Col R B P) by (assert_cols; Col).
      assert (H3 : Col Q X1 P) by (assert_cols; Col).
      assert (H := l9_19 R B Q X1 P H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : TS R B Q A).
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
        exists X1; split.

          {
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          exists Q; Col.
          }

          {
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          exists R; split; Col; Between.
          }
        }
      }

      {
      assert (HOS : OS R A X2 Q).
        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by (assert_cols; Col).
        assert (H3 : Col Q X2 R) by (assert_cols; Col).
        assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; try (intro; treat_equalities; Col).
        split; try (intro; treat_equalities); Between.
        }
      apply one_side_transitivity with X2; Col.
      apply one_side_symmetry; apply l9_17 with P; Between.
      apply one_side_transitivity with Q; Col.
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A X1) by (assert_cols; Col).
      assert (H3 : Col P Q X1) by (assert_cols; Col).
      assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
      show_distinct P X1; Col.
      split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
      split; Col.
      split; try (intro; treat_equalities; Col).
      Between.
      }
    }
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_3_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet P B X2 ->
  Bet X2 Q R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
assert (HTS : TS R B Q A).
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
      exists X1; split.

        {
        split; Col.
        split; try (intro; treat_equalities; apply HAQR; assert_diffs; assert_cols; ColR).
        exists Q; Col.
        }

        {
        split; Col.
        split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
        exists R; split; Col; Between.
        }
      }
    }

    {
    assert (HOS : OS R A X2 Q).
      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by (assert_cols; Col).
      assert (H3 : Col Q X2 R) by (assert_cols; Col).
      assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities); Between.
      }
    apply one_side_transitivity with X2; Col.
    apply one_side_symmetry; apply l9_17 with P; Between.
    apply one_side_transitivity with Q; Col.
    apply one_side_symmetry.
    assert (H1 : R <> A) by (assert_diffs; auto).
    assert (H2 : Col R A X1) by (assert_cols; Col).
    assert (H3 : Col P Q X1) by (assert_cols; Col).
    assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
    show_distinct P X1; Col.
    split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
    split; Col.
    split; try (intro; treat_equalities; Col).
    Between.
    }
  }
  destruct HTS as [H1 [H2  [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_1_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet P B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_1_3_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_1_3_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_3_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_3_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R A Q B).
  {
  elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    elim (eq_dec_points P X1); intro HPX1; treat_equalities.

      {
      intuition.
      }

      {
      assert (HAPR : ~ Col A P R).
        {
        intro; apply HNC; assert_diffs; assert_cols; ColR.
        }
      apply l9_8_2 with P.

        {
        split; Col.
        split; Col.
        exists R; split; Col; Between.
        }

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A X1) by (assert_cols; Col).
        assert (H3 : Col P Q X1) by (assert_cols; Col).
        assert (H := l9_19 R A P Q X1 H1 H2 H3); rewrite H.
        split; Col.
        split; Col.
        split; try (intro; treat_equalities; apply HAQR; Col).
        Between.
        }
      }
    }

    {
    apply l9_2; apply l9_8_2 with X2.

      {
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists R; split; Col; Between.
      }

      {
      apply one_side_symmetry.
      assert (H := outer_pasch P X2 Q X1 R HCol1 (between_symmetry Q R X2 HCol4)).
      destruct H as [I [HPX2I HRX1I]]; elim (eq_dec_points R X1); intro HRX1; treat_equalities.

        {
        exfalso; apply HNC; assert_cols; Col.
        }

        {
        elim (eq_dec_points P X2); intro HPX2; treat_equalities.

          {
          exfalso; apply HNC; assert_cols; Col.
          }

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          assert (H2 : Col R A I) by (assert_diffs; assert_cols; ColR).
          assert (H3 : Col B X2 I) by (assert_cols; ColR).
          assert (H := l9_19 R A B X2 I H1 H2 H3); rewrite H.
          split; Col.
          split; try (intro; treat_equalities; apply HABR; Col).
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          eBetween.
          }
        }
      }
    }
  }
destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
exists I; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_1_3_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet R X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
    split; Col.
    split; Col.
    exists X2; assert_cols; split; Col; Between.
    }

    {
    exists X1; split.

      {
      split; Col.
      split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
      exists Q; Col.
      }

      {
      split; Col.
      split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
      exists R; split; Col; Between.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_1_3_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet B X2 P ->
  Bet X2 Q R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
    split; Col.
    split; Col.
    exists X2; assert_cols; split; Col; Between.
    }

    {
    exists X1; split.

      {
      split; Col.
      split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
      exists Q; Col.
      }

      {
      split; Col.
      split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
      exists R; split; Col; Between.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_1_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet B X2 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_1_3_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_1_3_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_3_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_3_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet X2 P B ->
  Bet Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q A R B).
  {
  assert (HOS : OS Q A R X2).
    {
    assert (H1 : Q <> A) by (assert_diffs; auto).
    assert (H2 : Col Q A Q) by Col.
    assert (H3 : Col R X2 Q) by (assert_cols; ColR).
    assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
    split; Col.
    split; assert_diffs; Col.
    }
  assert (HTS1 : TS Q A P R).
    {
    apply l9_2.
    assert (H := inner_pasch P A X1 Q R HCol1 (between_symmetry X1 R A HCol2));
    destruct H as [I [HQAI HPRI]].
    split; Col.
    show_distinct A X1; Col.
    split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
    exists I; assert_cols; Col.
    }
  assert (HTS2 : TS Q A P X2)
    by (apply l9_2; apply l9_8_2 with R; try apply l9_2; Col).
  apply l9_2; apply l9_8_2 with P; Col.
  destruct HTS2 as [H1 [HQAX2 [I [HQAI HPX2I]]]]; clear H1.
  assert (H1 : Q <> A) by (assert_diffs; auto).
  assert (H2 : Col Q A I) by (assert_cols; Col).
  assert (H3 : Col P B I) by (show_distinct P X2; Col; assert_cols; ColR).
  assert (H := l9_19 Q A P B I H1 H2 H3); rewrite H.
  split; try (intro; unfold TS in HTS1; spliter; Col).
  split; try (intro; treat_equalities; unfold TS in HTS1; spliter; Col).
  split; try (intro; treat_equalities; Col).
  eBetween.
  }
destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_1_3_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet X2 P B ->
  Bet R X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  assert (HTS : TS Q A B R).
    {
    apply l9_8_2 with P.

      {
      apply l9_2.
      assert (H := inner_pasch P A X1 Q R HCol1 (between_symmetry X1 R A HCol2));
        destruct H as [I [HQAI HPRI]].
      split; Col.
      show_distinct A X1; Col.
      split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
      exists I; assert_cols; Col.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by Col.
      assert (H3 : Col B P Q) by (assert_cols; Col).
      assert (H := l9_19 Q A B P Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      }
    }
  destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
  exists I; right; left; split; Col.
  }

  {
  assert (HTS : TS Q A R B).
    {
    assert (HOS : OS Q A R X2).
      {
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by Col.
      assert (H3 : Col R X2 Q) by (assert_cols; ColR).
      assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities); Between.
      }
    assert (HTS1 : TS Q A P R).
      {
      apply l9_2.
      assert (H := inner_pasch P A X1 Q R HCol1 (between_symmetry X1 R A HCol2));
        destruct H as [I [HQAI HPRI]].
      split; Col.
      show_distinct A X1; Col.
      split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
      exists I; assert_cols; Col.
      }
    assert (HTS2 : TS Q A P X2)
      by (apply l9_2; apply l9_8_2 with R; try apply l9_2; Col).
    apply l9_2; apply l9_8_2 with P; Col.
    destruct HTS2 as [H1 [HQAX2 [I [HQAI HPX2I]]]]; clear H1.
    assert (H1 : Q <> A) by (assert_diffs; auto).
    assert (H2 : Col Q A I) by (assert_cols; Col).
    assert (H3 : Col P B I) by (show_distinct P X2; Col; assert_cols; ColR).
    assert (H := l9_19 Q A P B I H1 H2 H3); rewrite H.
    split; try (intro; unfold TS in HTS1; spliter; Col).
    split; try (intro; treat_equalities; unfold TS in HTS1; spliter; Col).
    split; try (intro; treat_equalities; Col).
    eBetween.
    }
  destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
  exists I; right; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_3_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet X2 P B ->
  Bet X2 Q R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch P A X1 Q R HCol1 (between_symmetry X1 R A HCol2));
destruct H as [I1 [HQAI1 HPRI1]];
assert (H := inner_pasch R B X2 Q P (between_symmetry X2 Q R HCol4));
destruct (H (between_symmetry X2 P B HCol3)) as [I2 [HQBI2 HPRI2]]; clear H.
assert (HQI1 : Q <> I1) by (intro; treat_equalities; assert_cols; Col).
assert (HQI2 : Q <> I2) by (intro; treat_equalities; assert_cols; Col).
assert (H := l5_3 P I1 I2 R (between_symmetry R I1 P HPRI1) HPRI2); elim H; clear H; intro PI1I2.

  {
  assert (HTS : TS Q B A R).
    {
    apply l9_8_2 with I1.

      {
      split; try (intro; apply HABQ; assert_cols; ColR).
      split; Col.
      exists I2; assert_cols; split; Col; eBetween.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> B) by (assert_diffs; auto).
      assert (H2 : Col Q B Q) by Col.
      assert (H3 : Col A I1 Q) by (show_distinct P X2; Col; assert_cols; ColR).
      assert (H := l9_19 Q B A I1 Q H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; assert_diffs; Col).
      split; try (intro; assert_diffs); Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HQBI HRAI]]]]; clear H1; clear H2.
  exists I; right; right; split; Col.
  }

  {
  assert (HTS : TS Q A B R).
    {
    apply l9_8_2 with I2.

      {
      split; try (intro; apply HABQ; assert_cols; ColR).
      split; Col.
      exists I1; assert_cols; split; Col; eBetween.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by Col.
      assert (H3 : Col B I2 Q) by (show_distinct P X2; Col; assert_cols; ColR).
      assert (H := l9_19 Q A B I2 Q H1 H2 H3); rewrite H.
      split; Col.
      split; try (intro; assert_diffs; Col).
      split; try (intro; assert_diffs); Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
  exists I; right; left; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Bet X2 P B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_1_3_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_1_3_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_3_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Bet X1 R A ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_1_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_1_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet P Q X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol2 HCol3 HCol4 HCol1.
elim HCol2; clear HCol2; intro HCol2.

  {
  apply coplanar_trans_1_aux_4_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol2; clear HCol2; intro HCol2.

    {
    apply coplanar_trans_1_aux_4_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_1_3 with P X1 X2; assumption.
    }
  }
Qed.

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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X2); intro HRX2; treat_equalities.

  {
  assert (HTS : TS R A B Q).
    {
    apply l9_8_2 with P.

      {
      split; try (intro; apply HABR; assert_diffs; assert_cols; ColR).
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
  destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
  exists I; right; right; split; Col.
  }

  {
  assert (HTS : TS R A B Q).
    {
    assert (HTS : TS R A X2 Q).
      {
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
      split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
      split; Col.
      exists X1; assert_cols; split; Col; Between.
      }
    }
  destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
  exists I; right; right; split; Col.
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_1_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet P B X2 ->
  Bet R X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X2); intro HRX2; treat_equalities.

  {
  assert (HTS : TS R A B Q).
    {
    apply l9_8_2 with P.

      {
      split; try (intro; apply HABR; assert_diffs; assert_cols; ColR).
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
  destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
  exists I; right; right; split; Col.
  }

  {
  assert (H := inner_pasch P R Q X1 X2 (between_symmetry Q X1 P HCol1) HCol4);
  destruct H as [I [HRX1I HPX2I]].
  assert (H := l5_3 X2 B I P (between_symmetry P B X2 HCol3) HPX2I).
  assert (HARI : Col A R I) by (show_distinct R X1; Col; assert_cols; ColR).
  elim H; clear H; intro HBX2I.

    {
    elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

      {
      assert_cols; Cop.
      }

      {
      assert (HTS : TS R B Q A).
        {
        apply l9_31.

          {
          apply one_side_transitivity with P.

            {
            assert (H1 : R <> Q) by (assert_diffs; auto).
            assert (H2 : Col R Q X2) by Col.
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
              assert (H2 : Col R Q Q) by Col.
              assert (H3 : Col P X1 Q) by (assert_cols; Col).
              assert (H := l9_19 R Q P X1 Q H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              }

              {
              apply one_side_symmetry.
              assert (H1 : R <> Q) by (assert_diffs; auto).
              assert (H2 : Col R Q R) by Col.
              assert (H3 : Col A X1 R) by (assert_cols; Col).
              assert (H := l9_19 R Q A X1 R H1 H2 H3); rewrite H.
              split; Col.
              split; assert_diffs; Col.
              }
            }
          }

          {
          apply one_side_transitivity with X2.

            {
            assert (H1 : R <> A) by (assert_diffs; auto).
            assert (H2 : Col R A I) by Col.
            assert (H3 : Col B X2 I) by (assert_cols; Col).
            assert (H := l9_19 R A B X2 I H1 H2 H3); rewrite H.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities); Col.
            Between.
            }

            {
            apply one_side_symmetry.
            assert (H1 : R <> A) by (assert_diffs; auto).
            assert (H2 : Col R A R) by Col.
            assert (H3 : Col Q X2 R) by (assert_cols; Col).
            assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
            split; Col.
            split; assert_diffs; Col.
            }
          }
        }
      destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
      exists I'; right; left; split; Col.
      }
    }

    {
    assert (HTS : TS R A Q B).
      {
      apply l9_8_2 with X2.

        {
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        show_distinct P X2; assert_cols; Col.
        exists I; split; Col.
        }

        {
        apply one_side_symmetry.
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by Col.
        assert (H3 : Col Q X2 R) by (assert_cols; Col).
        assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        }
      }
    destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
    exists I'; right; right; split; Col.
    }
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q A B R).
  {
  elim (eq_dec_points A X1); intro HAX1; treat_equalities.

    {
    apply l9_8_2 with X2.

      {
      assert_diffs.
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
      assert (HOS : OS Q A X1 P).
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
      assert (HTS : TS Q A X1 R).
        {
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists A; split; Col; Between.
        }
      apply l9_8_2 with X1; Col.
      apply one_side_transitivity with P; Col.
      apply l9_17 with X2; Col.
      apply one_side_transitivity with X1; apply one_side_symmetry; Col.
      exists R; split; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists Q; split; Col.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_1_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet P B X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_2_1_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_2_1_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_1_1_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_1_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet B X2 P ->
  Bet Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
    split; Col.
    split; Col.
    exists X2; assert_cols; split; Col; Between.
    }

    {
    apply one_side_transitivity with X1.

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by Col.
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
      assert (H2 : Col Q R R) by Col.
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_1_2_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet B X2 P ->
  Bet R X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
    split; Col.
    split; Col.
    exists X2; assert_cols; split; Col; Between.
    }

    {
    apply one_side_transitivity with X1.

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by Col.
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
      assert (H2 : Col Q R R) by Col.
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_1_2_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet B X2 P ->
  Bet X2 Q R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
    split; Col.
    split; Col.
    exists X2; assert_cols; split; Col; Between.
    }

    {
    apply one_side_transitivity with X1.

      {
      assert (H1 : Q <> R) by (assert_diffs; auto).
      assert (H2 : Col Q R Q) by Col.
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
      assert (H2 : Col Q R R) by Col.
      assert (H3 : Col A X1 R) by (assert_cols; Col).
      assert (H := l9_19 Q R A X1 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
exists I; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_1_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet B X2 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_2_1_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_2_1_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_1_2_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_1_3_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet X2 P B ->
  Bet Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q A B R).
  {
  elim (eq_dec_points A X1); intro HAX1; treat_equalities.

    {
    assert (HQX2 : Q <> X2) by (intro; treat_equalities; Col).
    apply l9_2; apply l9_8_2 with X2.

      {
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists P; assert_cols; Col.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by Col.
      assert (H3 : Col R X2 Q) by (assert_cols; Col).
      assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      }
    }

    {
    assert (HOS1 : OS Q A P X1).
      {
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by Col.
      assert (H3 : Col P X1 Q) by (assert_cols; Col).
      assert (H := l9_19 Q A P X1 Q H1 H2 H3); rewrite H.
      split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
      split; assert_diffs; Col.
      split; try (intro; treat_equalities; assert_cols; Col).
      Between.
      }
    assert (HOS2 : OS Q A R X2).
      {
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by Col.
      assert (H3 : Col R X2 Q) by (assert_cols; Col).
      assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      }
    assert (HTS : TS Q A P X2).
      {
      apply l9_2; apply l9_8_2 with R; Col.
      apply l9_2; apply l9_8_2 with X1; try apply one_side_symmetry; Col.
      split; try (intro; assert_cols; apply HAQR; ColR).
      split; Col.
      exists A; split; Col; Between.
      }
    destruct HTS as [Hclear1 [Hclear2 [I [HQAI HPX2I]]]].
    clear Hclear1; clear Hclear2; assert_diffs.
    apply l9_2; apply l9_8_2 with X2; try apply one_side_symmetry; Col.
    split; try (intro; apply HAQR; assert_cols; ColR).
    split; Col.
    exists I; eBetween.
    }
  }
destruct HTS as [H1 [H2 [I [HQAI HBRI]]]]; clear H1; clear H2.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_1_3_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet X2 P B ->
  Bet R X2 Q ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q A B R).
  {
  elim (eq_dec_points A X1); intro HAX1; treat_equalities.

    {
    assert (HQX2 : Q <> X2).
      {
      intro; treat_equalities; assert_diffs; assert_cols; apply HABQ; ColR.
      }
    apply l9_2; apply l9_8_2 with X2.

      {
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists P; assert_cols; Col.
      }

      {
      apply one_side_symmetry.
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by Col.
      assert (H3 : Col R X2 Q) by (assert_cols; Col).
      assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; Between.
      }
    }

    {
    elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

      {
      apply l9_8_2 with P.

        {
        apply l9_8_2 with X1.

          {
          split; try (intro; assert_cols; apply HAQR; ColR).
          split; Col.
          exists A; split; Col; Between.
          }

          {
          apply one_side_symmetry.
          assert (H1 : Q <> A) by (assert_diffs; auto).
          assert (H2 : Col Q A Q) by Col.
          assert (H3 : Col P X1 Q) by (assert_cols; Col).
          assert (H := l9_19 Q A P X1 Q H1 H2 H3); rewrite H.
          split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
          split; assert_diffs; Col.
          split; try (intro; treat_equalities; assert_cols; Col).
          Between.
          }
        }

        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by Col.
        assert (H3 : Col P B Q) by (assert_cols; Col).
        assert (H := l9_19 Q A P B Q H1 H2 H3); rewrite H.
        split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
        split; assert_diffs; Col.
        }
      }

      {
      assert (HOS1 : OS Q A P X1).
        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by Col.
        assert (H3 : Col P X1 Q) by (assert_cols; Col).
        assert (H := l9_19 Q A P X1 Q H1 H2 H3); rewrite H.
        split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
        split; assert_diffs; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      assert (HOS2 : OS Q A R X2).
        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by Col.
        assert (H3 : Col R X2 Q) by (assert_cols; Col).
        assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; try (intro; treat_equalities; assert_cols; Col).
        Between.
        }
      assert (HTS : TS Q A P X2).
        {
        apply l9_2; apply l9_8_2 with R; Col.
        apply l9_2; apply l9_8_2 with X1; try apply one_side_symmetry; Col.
        split; try (intro; assert_cols; apply HAQR; ColR).
        split; Col.
        exists A; split; Col; Between.
        }
      destruct HTS as [Hclear1 [Hclear2 [I [HQAI HPX2I]]]].
      clear Hclear1; clear Hclear2; assert_diffs.
      apply l9_2; apply l9_8_2 with X2; try apply one_side_symmetry; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists I; eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQAI HBRI]]]]; clear H1; clear H2.
exists I; right; left; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_1_3_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet X2 P B ->
  Bet X2 Q R ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R A Q B).
  {
  elim (eq_dec_points P X1); intro HPX1; treat_equalities.

    {
    apply l9_8_2 with X2.

      {
      show_distinct R X2; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists P; assert_cols; Col.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by Col.
      assert (H3 : Col Q X2 R) by (assert_cols; Col).
      assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities); Between.
      }
    }

    {
    assert (HTS : TS R A P X2).
      {
      apply l9_2; apply l9_8_2 with Q.

        {
        split; Col.
        split; try (intro; apply HAQR; assert_diffs; assert_cols; ColR).
        exists X1; assert_cols; Col.
        }

        {
        assert (H1 : R <> A) by (assert_diffs; auto).
        assert (H2 : Col R A R) by Col.
        assert (H3 : Col Q X2 R) by (assert_cols; Col).
        assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
        split; Col.
        split; assert_diffs; Col.
        split; try (intro; treat_equalities); Between.
        }
      }
    apply l9_8_2 with X2.

      {
      destruct HTS as [H1 [H2 [I [HRAI HPX2I]]]]; clear H1; clear H2.
      show_distinct R X2; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists I; assert_cols; split; Col; eBetween.
      }

      {
      apply one_side_symmetry.
      assert (H1 : R <> A) by (assert_diffs; auto).
      assert (H2 : Col R A R) by Col.
      assert (H3 : Col Q X2 R) by (assert_cols; Col).
      assert (H := l9_19 R A Q X2 R H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities); Between.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
exists I; right; right; split; Col.
Qed.

Lemma coplanar_trans_1_aux_4_2_1_3 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Bet X2 P B ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim HCol4; clear HCol4; intro HCol4.

  {
  apply coplanar_trans_1_aux_4_2_1_3_1 with P X1 X2; assumption.
  }

  {
  elim HCol4; clear HCol4; intro HCol4.

    {
    apply coplanar_trans_1_aux_4_2_1_3_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_1_3_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1_aux_4_2_1 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Bet R A X1 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol3 HCol4 HCol1 HCol2.
elim HCol3; clear HCol3; intro HCol3.

  {
  apply coplanar_trans_1_aux_4_2_1_1 with P X1 X2; assumption.
  }

  {
  elim HCol3; clear HCol3; intro HCol3.

    {
    apply coplanar_trans_1_aux_4_2_1_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_1_3 with P X1 X2; assumption.
    }
  }
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R A B Q).
  {
  elim (eq_dec_points P X1); intro HPX1; treat_equalities.

    {
    apply l9_8_2 with X2.

      {
      show_distinct R X2; try (apply HABR; assert_diffs; assert_cols; ColR).
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
      split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
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
          split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
          split; Col.
          exists X1; split; Col; Between.
          }

          {
          split; try (intro; apply HAQR; assert_cols; ColR).
          split; Col.
          exists R; split; Col; Between.
          }
        }
      }
    }
  }
destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q B A R).
  {
  elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

    {
    split; Col.
    split; Col.
    exists X1; split; Col.
    assert_diffs; assert_cols; ColR.
    }

    {
    elim (eq_dec_points P B); intro HPB; treat_equalities.

      {
      split; Col.
      split; Col.
      exists X1; assert_cols; Col.
      }

      {
      assert (HTS : TS Q B X1 R).
        {
        apply l9_8_2 with P.

          {
          apply l9_2; apply l9_8_2 with X2.

            {
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
      destruct HTS as [H1 [H2 [I [HQBI HRX1I]]]]; clear H1; clear H2.
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
destruct HTS as [H1 [H2 [I [HQBI HARI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch X2 P Q R X1 HCol4 (between_symmetry Q X1 P HCol1));
destruct H as [I [HPX2I HRX1I]].
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
assert (H := l5_3 X2 B I P (between_symmetry P B X2 HCol3) HPX2I);
elim H; clear H; intro HBX2I.

  {
  assert (HTS : TS R B Q A).
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
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : TS R A Q B).
    {
    apply l9_8_2 with X2.

      {
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
  destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
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
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch Q B X2 R P HCol4 (between_symmetry X2 P B HCol3));
destruct H as [I [HRBI HPQI]].
assert (H := l5_3 P X1 I Q (between_symmetry Q X1 P HCol1) HPQI); elim H; clear H; intro PX1I.

  {
  assert (HTS : TS R B A Q).
    {
    apply l9_8_2 with X1.

      {
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
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : TS R A Q B).
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
  destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R A Q B).
  {
  elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; try (intro; apply HABR; assert_diffs; assert_cols; ColR).
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
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists P; assert_cols; Col.
        }

        {
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
destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R A Q B).
  {
  elim (eq_dec_points R X2); intro HRX2; treat_equalities.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; try (intro; apply HABR; assert_diffs; assert_cols; ColR).
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
        split; try (intro; apply HAQR; assert_cols; ColR).
        split; Col.
        exists P; assert_cols; Col.
        }

        {
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
destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : TS Q R B A).
  {
  apply l9_8_2 with X1.

    {
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
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch P Q X2 B R (between_symmetry B X2 P HCol3) HCol4);
destruct H as [I [HPQI HRBI]].
assert (H := l5_3 P X1 I Q (between_symmetry Q X1 P HCol1) HPQI); elim H; clear H; intro PX1I.

  {
  assert (HTS : TS R A Q B).
    {
    apply l9_31.

      {
      exists X1; split.

        {
        split; Col.
        show_distinct R X1; assert_cols; Col.
        split; try (intro; apply HAQR; ColR).
        exists R; split; Col; Between.
        }

        {
        apply l9_2; apply l9_8_2 with P.

          {
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
        split; Col.
        show_distinct R X1; assert_cols; Col.
        split; try (intro; apply HABR; ColR).
        exists R; split; Col; Between.
        }

        {
        split; Col.
        show_distinct R X1; assert_cols; Col.
        split; try (intro; apply HABR; ColR).
        exists I; split; Col; eBetween.
        }
      }
    }
  destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
  exists I'; right; right; split; Col.
  }

  {
  assert (HTS : TS R B Q A).
    {
    apply l9_8_2 with X1.

      {
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
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
  {
  assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
  apply l9_31.

    {
    exists X1; split.

      {
      apply l9_2; apply l9_8_2 with P.

        {
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
        split; Col.
        split; try (intro; apply HABR; assert_diffs; assert_cols; ColR).
        exists R; Col.
        }

        {
        split; Col.
        split; try (intro; apply HABR; assert_diffs; assert_cols; ColR).
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
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
  {
  assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
  apply l9_31.

    {
    exists X1; split.

      {
      apply l9_2; apply l9_8_2 with P.

        {
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
        split; Col.
        split; try (intro; apply HABR; assert_diffs; assert_cols; ColR).
        exists R; Col.
        }

        {
        split; Col.
        split; try (intro; apply HABR; assert_diffs; assert_cols; ColR).
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
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : TS Q R B A).
  {
  apply l9_8_2 with X1.

    {
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
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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

Lemma coplanar_trans_1_aux_4_2 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col R A X1 ->
  Col P B X2 ->
  Col Q R X2 ->
  Bet Q X1 P ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol2 HCol3 HCol4 HCol1.
elim HCol2; clear HCol2; intro HCol2.

  {
  apply coplanar_trans_1_aux_4_2_1 with P X1 X2; assumption.
  }

  {
  elim HCol2; clear HCol2; intro HCol2.

    {
    apply coplanar_trans_1_aux_4_2_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_2_3 with P X1 X2; assumption.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch X1 X2 Q P R HCol1 (between_symmetry Q R X2 HCol4));
destruct H as [I [HPX2I HRX1I]].
assert (H := l5_3 P B I X2 HCol3 HPX2I); elim H; clear H; intro HPBI.

  {
  assert (HTS : TS R B Q A).
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
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : TS R A Q B).
    {
    assert (HRX1 : R <> X1) by (intro; treat_equalities; Col).
    elim (eq_dec_points P I); intro HPI; treat_equalities.

      {
      apply l9_2; apply l9_8_2 with X2.

        {
        show_distinct R X2; try (apply HABR; assert_diffs; assert_cols; ColR).
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
        show_distinct P X1; try (apply HABR; assert_cols; ColR).
        split; try (intro; apply HAQR; assert_diffs; assert_cols; ColR).
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
  destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
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
      assert (HOS : OS R A X2 Q).
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
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
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
      }
    }

    {
    assert (HOS : OS R A X2 Q).
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
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
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
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
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
          split; Col.
          split; try (intro; assert_cols; apply HAQR; ColR).
          exists P; assert_cols; split; Col; Between.
          }

          {
          split; Col.
          split; try (intro; assert_cols; apply HAQR; ColR).
          exists R; Col.
          }
        }

        {
        assert (HTS : TS R A P X2).
          {
          apply l9_8_2 with Q.

            {
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
          destruct HTS as [HAPR [HARX2 [I [HARI HPX2I]]]].
          assert (HPX2 : P <> X2) by (intro; treat_equalities; Col).
          assert (H2 : Col R A I) by Col.
          assert (H3 : Col P B I) by (assert_cols; ColR).
          assert (H := l9_19 R A P B I); rewrite H; Col.
          split; Col.
          split; try (intro; treat_equalities; Col).
          split; try (intro; treat_equalities; Col).
          eBetween.
          intro; subst A; Col.
          }

          {
          split; Col.
          split; try (intro; apply HAQR; assert_cols; ColR).
          exists R; Col.
          }
        }
      }
    }
  }
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q A B R).
  {
  elim (eq_dec_points A X1); intro HAX1; treat_equalities.

    {
    apply l9_2; apply l9_8_2 with X2.

      {
      show_distinct Q X2; try (apply HABQ; assert_diffs; assert_cols; ColR).
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
      assert (HOS : OS Q A R X2).
        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        assert (H2 : Col Q A Q) by (assert_cols; Col).
        assert (H3 : Col R X2 Q) by (assert_cols; Col).
        assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
        split; Col.
        assert_diffs; split; Between.
        }
      assert (HTS : TS Q A P X2).
        {
        apply l9_2; apply l9_8_2 with R; Col.
        split; Col.
        split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
        destruct (inner_pasch Q R X1 P A (between_symmetry X1 P Q HCol1) HCol2) as [I [HPRI HQAI]].
        exists I; assert_cols; split; Col; Between.
        }
      apply l9_2; apply l9_8_2 with X2; try (apply one_side_symmetry; Col).
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      destruct HTS as [Hc1 [Hc2 [I [HQAI HPX2I]]]].
      exists I; eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch Q R X1 P A (between_symmetry X1 P Q HCol1) HCol2);
destruct H as [I1 [HPRI1 HQAI1]].
apply between_symmetry in HCol3; apply between_symmetry in HCol4.
assert (H := inner_pasch R B X2 Q P HCol4 HCol3); destruct H as [I2 [HQBI2 HPRI2]].
assert (H := l5_3 P I1 I2 R HPRI1 HPRI2); elim H; clear H; intro PI1I2.

  {
  assert (HTS : TS Q B A R).
    {
    apply l9_8_2 with I1.

      {
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
  destruct HTS as [H1 [H2 [I [HQBI HRAI]]]]; clear H1; clear H2.
  exists I; right; right; split; Col.
  }

  {
  assert (HTS : TS Q A B R).
    {
    apply l9_8_2 with I2.

      {
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
  destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HOS : OS R Q A B).
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
  assert (HTS : TS R B Q A).
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
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : TS R A Q B).
    {
    assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
    elim (eq_dec_points P X1); intro HPX1; treat_equalities.

      {
      apply l9_2; apply l9_8_2 with X2.

        {
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
        split; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
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
  destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
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
      assert (HOS : OS R A X2 Q).
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
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
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
    assert (HOS : OS R A X2 Q).
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
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS Q R A B).
  {
  apply l9_8_2 with P.

    {
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
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
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
          split; Col.
          split; try (intro; apply HAQR; assert_cols; ColR).
          exists P; assert_cols; split; Col; Between.
          }

          {
          split; Col.
          split; try (intro; apply HAQR; assert_cols; ColR).
          exists R; Col.
          }
        }

        {
        assert (HTS : TS R A P X2).
          {
          apply l9_8_2 with Q.

            {
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
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            destruct HTS as [Hc1 [Hc2 [I [HRAI HPX2I]]]].
            exists I; split; Col; eBetween.
            }

            {
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; Col.
            }
        }
      }
    }
  }
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch R B X2 Q P HCol4 (between_symmetry X2 P B HCol3));
destruct H as [I [HRBI HPQI]].
assert (HQP : Q <> P) by (assert_diffs; Col).
assert (H := l5_2 Q P X1 I HQP (between_symmetry X1 P Q HCol1) HPQI); elim H; clear H; intro HPX1I.

  {
  assert (HTS : TS R A Q B).
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
  destruct HTS as [H1 [H2 [I' [HRAI' HQBI']]]]; clear H1; clear H2.
  exists I'; right; right; split; Col.
  }

  {
  assert (HTS : TS R B A Q).
    {
    apply l9_8_2 with X1.

      {
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
  destruct HTS as [H1 [H2 [I' [HRBI' HQAI']]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := inner_pasch R B X2 Q P); destruct H as [I [HQBI HPRI]]; Between.
assert (HTS : TS Q B R A).
  {
  elim (eq_dec_points P B); intro HPB; treat_equalities.

    {
    split; Col.
    split; Col.
    exists X1; assert_cols; split; Col; Between.
    }

    {
    elim (eq_dec_points P I); intro HPI; treat_equalities.

      {
      split; Col.
      split; Col.
      exists X1; assert_diffs; assert_cols; split; Between; ColR.
      }

      {
      assert (HTS : TS Q B R X1).
        {
        assert (HQX2 : Q <> X2).
          {
          intro; treat_equalities; assert_diffs; assert_cols; apply HNC; ColR.
          }
        apply l9_2; apply l9_8_2 with P.

          {
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
      split; Col.
      split; Col.
      destruct HTS as [Hc1 [Hc2 [I' [HQBI' HRX1I']]]].
      exists I'; assert_cols; split; Col; eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [I' [HQBI' HQRI']]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : TS Q R A B).
  {
  apply l9_2; apply l9_8_2 with P.

    {
    apply l9_8_2 with X1.

      {
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
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R A Q B).
  {
  elim (eq_dec_points P X1); intro HPX2; treat_equalities.

    {
    apply l9_2; apply l9_8_2 with X2.

      {
      show_distinct R X2; assert_diffs; assert_cols; try (apply HABR; ColR).
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
        split; try (intro; assert_diffs; assert_cols; apply HABR; ColR).
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
      assert (HTS1 : TS R A X2 Q).
        {
        split; try (intro; assert_cols; apply HAQR; ColR).
        split; Col.
        exists R; split; Col; Between.
        }
      apply l9_2; apply l9_8_2 with X2; Col.
      assert (HTS2 : TS R A P X2).
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
      split; try (intro; assert_diffs; assert_cols; apply HAQR; ColR).
      split; Col.
      destruct HTS2 as [Hc1 [Hc2 [I [HRAI HPX2I]]]].
      exists I; assert_cols; split; Col; eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [I [HRAI HQBI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
      assert (HTS : TS Q A R B).
        {
        apply l9_31.

          {
          exists X1; split.

            {
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; split; Col; Between.
            }

            {
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            assert_diffs; exists Q; split; Col; eBetween.
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
      destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
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
      assert (HTS : TS Q A R B).
        {
        apply l9_31.

          {
          exists X1; split.

            {
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; split; Col; Between.
            }

            {
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
      destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
      exists I; right; left; split; Col.
      }

      {
      exfalso; apply HAQR; assert_cols; ColR.
      }
    }

    {
    elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

      {
      assert (HTS : TS Q A R B).
        {
        apply l9_31.

          {
          exists X1; split.

            {
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; split; Col; Between.
            }

            {
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            assert_diffs; exists Q; split; Col; eBetween.
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
      destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
      exists I; right; left; split; Col.
      }

      {
      exfalso; apply HAQR; assert_cols; ColR.
      }
    }

    {
    assert (H := l5_2 X1 X2 I1 I2 HX1X2 HX1X2I1 HX1X2I2); elim H; clear H; intro HX2I1I2.

      {
      assert (HTS : TS Q A R B).
        {
        apply l9_2; apply l9_8_2 with I2.

          {
          apply l9_2; apply l9_8_2 with X2.

            {
            show_distinct Q X2; assert_diffs; assert_cols; try (apply HABQ; ColR).
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
      destruct HTS as [H1 [H2 [I [HQAI HRBI]]]]; clear H1; clear H2.
      exists I; right; left; split; Col.
      }

      {
      assert (HTS : TS Q B R A).
        {
        apply l9_2; apply l9_8_2 with I1.

          {
          apply l9_2; apply l9_8_2 with X2.

            {
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
      destruct HTS as [H1 [H2 [I [HQBI HRQI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : TS R B Q A).
  {
  apply l9_8_2 with X1.

    {
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
destruct HTS as [H1 [H2 [I [HRBI HQAI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
assert (HTS : TS Q R A B).
  {
  apply l9_2; apply l9_8_2 with P.

    {
    apply l9_8_2 with X1.

      {
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
destruct HTS as [H1 [H2 [I [HQRI HABI]]]]; clear H1; clear H2.
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
  Coplanar Q R A B.
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
  Coplanar Q R A B.
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

Lemma coplanar_trans_1_aux_4 : forall P Q R A B X1 X2,
  ~ Col P Q R ->
  ~ Col A B Q ->
  ~ Col A B R ->
  ~ Col A Q R ->
  ~ Col B Q R ->
  Col P Q X1 ->
  Col R A X1 ->
  Col P B X2 ->
  Col Q R X2 ->
  Coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim HCol1; clear HCol1; intro HCol1.

  {
  apply coplanar_trans_1_aux_4_1 with P X1 X2; assumption.
  }

  {
  elim HCol1; clear HCol1; intro HCol1.

    {
    apply coplanar_trans_1_aux_4_2 with P X1 X2; assumption.
    }

    {
    apply coplanar_trans_1_aux_4_3 with P X1 X2; assumption.
    }
  }
Qed.

Lemma coplanar_trans_1 : forall P Q R A B,
  ~Col P Q R -> Coplanar P Q R A -> Coplanar P Q R B -> Coplanar Q R A B.
Proof.
intros P Q R A B HNC HCop1 HCop2.
destruct HCop1 as [X1 HCop1].
destruct HCop2 as [X2 HCop2].
elim (Col_dec A B Q); intro HABQ; Cop.
elim (Col_dec A B R); intro HABR; Cop.
elim (Col_dec A Q R); intro HAQR; Cop.
elim (Col_dec B Q R); intro HBQR; Cop.
elim HCop1; clear HCop1; intro HCop1; try (destruct HCop1 as [HCol1 HCol2]).

  {
  elim HCop2; clear HCop2; intro HCop2; try (destruct HCop2 as [HCol3 HCol4]).

    {
    apply coplanar_trans_1_aux_1 with P X1 X2; assumption.
    }

    {
    elim HCop2; clear HCop2; intro HCop2; try (destruct HCop2 as [HCol3 HCol4]).

      {
      apply coplanar_trans_1_aux_3 with P X1 X2; assumption.
      }

      {
      apply coplanar_trans_1_aux_4 with P X1 X2; assumption.
      }
    }
  }

  {
  elim HCop1; clear HCop1; intro HCop1; try (destruct HCop1 as [HCol1 HCol2]).

    {
    elim HCop2; clear HCop2; intro HCop2; try (destruct HCop2 as [HCol3 HCol4]).

      {
      assert (Coplanar R Q A B) by (apply coplanar_trans_1_aux_3 with P X1 X2; Col); Cop.
      }

      {
      elim HCop2; clear HCop2; intro HCop2; try (destruct HCop2 as [HCol3 HCol4]).

        {
        assert (H1 : ~ Col P R Q) by Col.
        assert (H2 : ~ Col A R Q) by Col.
        assert (H3 : ~ Col B R Q) by Col.
        assert (H := coplanar_trans_1_aux_1 P R Q A B X1 X2 H1 HABR HABQ H2 H3 HCol1 HCol2 HCol3 HCol4); Cop.
        }

        {
        assert (Coplanar R Q A B) by (apply coplanar_trans_1_aux_4 with P X1 X2; Col); Cop.
        }
      }
    }

    {
    elim HCop2; clear HCop2; intro HCop2; try (destruct HCop2 as [HCol3 HCol4]).

      {
      assert (Coplanar Q R B A) by (apply coplanar_trans_1_aux_4 with P X2 X1; Col); Cop.
      }

      {
      elim HCop2; clear HCop2; intro HCop2; try (destruct HCop2 as [HCol3 HCol4]).

        {
        assert (Coplanar R Q B A) by (apply coplanar_trans_1_aux_4 with P X2 X1; Col); Cop.
        }

        {
        apply coplanar_trans_1_aux_2 with P X1 X2; assumption.
        }
      }
    }
  }
Qed.

Lemma coplanar_pseudo_trans : forall A B C D P Q R,
  ~ Col P Q R ->
  Coplanar P Q R A ->
  Coplanar P Q R B ->
  Coplanar P Q R C ->
  Coplanar P Q R D ->
  Coplanar A B C D.
Proof.
intros A B C D P Q R HNC HCop1 HCop2 HCop3 HCop4.
elim (Col_dec R A B); intro HRAB.

  {
  elim (Col_dec R C D); intro HRCD.

    {
    exists R; Col5.
    }

    {
    elim (Col_dec Q R C); intro HQRC.

      {
      assert (HQRD : ~ Col Q R D) by (intro; assert_diffs; apply HRCD; ColR).
      assert (HCop5 := coplanar_trans_1 P Q R D A HNC HCop4 HCop1).
      assert (HCop6 := coplanar_trans_1 P Q R D B HNC HCop4 HCop2).
      assert (HCop7 := coplanar_trans_1 P Q R D C HNC HCop4 HCop3).
      assert (HCop8 := coplanar_trans_1 Q R D C A HQRD HCop7 HCop5).
      assert (HCop9 := coplanar_trans_1 Q R D C B HQRD HCop7 HCop6).
      assert (HRDC : ~ Col R D C) by Col.
      assert (HCop := coplanar_trans_1 R D C A B HRDC HCop8 HCop9).
      Cop.
      }

      {
      assert (HCop5 := coplanar_trans_1 P Q R C A HNC HCop3 HCop1).
      assert (HCop6 := coplanar_trans_1 P Q R C B HNC HCop3 HCop2).
      assert (HCop7 := coplanar_trans_1 P Q R C D HNC HCop3 HCop4).
      assert (HCop8 := coplanar_trans_1 Q R C D A HQRC HCop7 HCop5).
      assert (HCop9 := coplanar_trans_1 Q R C D B HQRC HCop7 HCop6).
      assert (HCop := coplanar_trans_1 R C D A B HRCD HCop8 HCop9).
      Cop.
      }
    }
  }

  {
  elim (Col_dec Q R A); intro HQRA.

    {
    assert (HQRB : ~ Col Q R B) by (intro; assert_diffs; apply HRAB; ColR).
    assert (HCop5 := coplanar_trans_1 P Q R B A HNC HCop2 HCop1).
    assert (HCop6 := coplanar_trans_1 P Q R B C HNC HCop2 HCop3).
    assert (HCop7 := coplanar_trans_1 P Q R B D HNC HCop2 HCop4).
    assert (HCop8 := coplanar_trans_1 Q R B A C HQRB HCop5 HCop6).
    assert (HCop9 := coplanar_trans_1 Q R B A D HQRB HCop5 HCop7).
    assert (HRBA : ~ Col R B A) by Col.
    assert (HCop := coplanar_trans_1 R B A C D HRBA HCop8 HCop9).
    Cop.
    }

    {
    assert (HCop5 := coplanar_trans_1 P Q R A B HNC HCop1 HCop2).
    assert (HCop6 := coplanar_trans_1 P Q R A C HNC HCop1 HCop3).
    assert (HCop7 := coplanar_trans_1 P Q R A D HNC HCop1 HCop4).
    assert (HCop8 := coplanar_trans_1 Q R A B C HQRA HCop5 HCop6).
    assert (HCop9 := coplanar_trans_1 Q R A B D HQRA HCop5 HCop7).
    assert (HCop := coplanar_trans_1 R A B C D HRAB HCop8 HCop9).
    Cop.
    }
  }
Qed.

End Coplanar_trans.
