Require Export Coplanar_perm.

Section Coplanar_trans_1.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : two_sides A R B Q).
    {
    apply l9_8_2 with X2.

      {
      assert (R <> X2) by (intro; assert_cols; apply HABR; ColR).
      split; try (intro; subst; apply HABR; Col).
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : two_sides B R A Q).
      {
      apply l9_8_2 with X1.

        {
        assert (R <> X1) by (intro; assert_cols; apply HABR; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (HTS1 : two_sides Q R X1 X2).
      {
      split; try  (intro; subst; apply HNC; ColR).
      assert (R <> X1) by (intro; subst; apply HNC; ColR).
      split; try (intro; assert_cols; apply HAQR; ColR).
      assert (R <> X2) by (intro; subst; apply HNC; ColR).
      split; try (intro; assert_cols; apply HBQR; ColR).
      exists Q; Col; Between.
      }
    assert (HTS2 : two_sides Q R A X2).
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
    assert (H : two_sides Q R A B).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : two_sides A R B Q).
    {
    apply l9_8_2 with X2.

      {
      assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; subst; apply HABR; Col).
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : two_sides B R A Q).
      {
      apply l9_8_2 with X1.

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides R Q A B).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : two_sides R Q A B).
    {
    apply l9_31.

      {
      exists X2; split.

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : two_sides A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : two_sides A R B Q).
    {
    apply l9_8_2 with X2.

      {
      assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; subst; apply HABR; Col).
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : two_sides B R A Q).
      {
      apply l9_8_2 with X1.

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides R Q A B).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : two_sides R Q A B).
    {
    apply l9_31.

      {
      exists X2; split.

        {
        assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : two_sides A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol3 HCol2 HCol4.
assert (HQX1X2 : Col Q X1 X2) by (assert_diffs; ColR).
elim HQX1X2; clear HQX1X2; intro HQX1X2.

  {
  assert (H : two_sides B R Q A).
    {
    apply l9_8_2 with X1.

      {
      assert (R <> X1) by (intro; assert_cols; apply HNC; ColR).
      split; try (intro; subst; apply HABR; Col).
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2.

    {
    assert (H : two_sides A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (R <> X2) by (intro; assert_cols; apply HNC; ColR).
        split; try (intro; subst; apply HABR; Col).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
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
    assert (H : coplanar Q R B A) by (apply coplanar_trans_1_aux_1_1_2 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (H : coplanar Q R B A) by (apply coplanar_trans_1_aux_1_1_3 with P X2 X1; Col; Between); Cop.
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
    assert (H : coplanar Q R B A) by (apply coplanar_trans_1_aux_1_2_3 with P X2 X1; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_1_3_3 with P X1 X2; assumption.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol3 HCol4 HCol1 HCol2.
elim (eq_dec_points R X2); intro HRX2; treat_equalities.
  {
  assert_cols; Cop.
  }

  {
  assert (HTS : two_sides R A Q X2).
    {
    apply l9_8_2 with P.

      {
      split; try (intro; apply HABR); treat_equalities; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HRAI HQX2I]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q R A B).
  {
  apply l9_8_2 with X1.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; try (intro; treat_equalities; apply HNC; Col).
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
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q R A B).
  {
  apply l9_8_2 with X1.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; try (intro; treat_equalities; apply HNC; Col).
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
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
apply between_symmetry in HCol4.
assert (H := outer_pasch R B X2 P Q HCol2 HCol4); destruct H as [I [HRIB HPQI]].
assert (HElim : Bet Q I X1 \/ Bet Q X1 I) by (apply l5_2 with P; assert_diffs; Between).
elim HElim; clear HElim; intro HQX1I.

  {
  assert (HTS : two_sides R B A Q).
    {
    elim (eq_dec_points R X1); intro HRX1.

      {
      exfalso; apply HNC; subst; Col.
      }

      {
      apply l9_8_2 with X1.

        {
        split; try (intro; treat_equalities; apply HNC; Col).
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
    destruct HTS as [H1 [H2 [H3 [I' [HRBI' HAQI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q R A B).
  {
  apply l9_8_2 with X1.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; try (intro; treat_equalities; apply HNC; Col).
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
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q R A B).
  {
  apply l9_8_2 with X1.

    {
    apply l9_2; apply l9_8_2 with P.

      {
      split; try (intro; treat_equalities; apply HNC; Col).
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
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
apply between_symmetry in HCol4.
assert (H := outer_pasch R B X2 P Q HCol2 HCol4); destruct H as [I [HRIB HPQI]].
assert (HElim : Bet Q I X1 \/ Bet Q X1 I) by (apply l5_2 with P; assert_diffs; Between).
elim HElim; clear HElim; intro HQX1I.

  {
  assert (HTS : two_sides R B A Q).
    {
    elim (eq_dec_points R X1); intro HRX1.

      {
      exfalso; apply HNC; subst; Col.
      }

      {
      apply l9_8_2 with X1.

        {
        split; try (intro; treat_equalities; apply HNC; Col).
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
    destruct HTS as [H1 [H2 [H3 [I' [HRBI' HAQI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1.

  {
  exfalso; apply HNC; subst; Col.
  }

  {
  assert (HTS : two_sides R B Q A).
    {
    apply l9_8_2 with X1.

      {
      split; try (intro; assert_diffs; Col).
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
  destruct HTS as [H1 [H2 [H3 [I [HRBI HAQI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
    assert (HTS : two_sides Q B R A).
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
              split; try (assert_diffs; Col).
              split; Col.
              split; try (intro; apply HAQR; assert_cols; ColR).
              exists Q; Col.
              }

              {
              split; try (assert_diffs; Col).
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
      destruct HTS as [H1 [H2 [H3 [I' [HQBI' HRAI']]]]]; clear H1; clear H2; clear H3.
      exists I'; right; right; assert_cols; Col.
    }

    {
    assert (HTS : two_sides Q A B R).
      {
      apply l9_8_2 with X2.

        {
        split; try (assert_diffs; Col).
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
    destruct HTS as [H1 [H2 [H3 [I' [HQAI' HRBI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (HTS : two_sides Q R A B).
    {
    apply l9_8_2 with X2.

      {
      split; try (assert_diffs; Col).
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
            split; try (assert_diffs; Col).
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists Q; Col.
            }

            {
            split; try (assert_diffs; Col).
            split; Col.
            split; try (intro; apply HAQR; assert_cols; ColR).
            exists R; split; Col; Between.
            }
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  assert (HTS : two_sides R B A Q).
    {
    apply l9_8_2 with X1.

      {
      apply l9_8_2 with X2.

        {
        split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HRBI HAQI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : two_sides Q A B R).
    {
    apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
      split; try (intro; assert_cols; apply HABQ; ColR).
      split; Col.
      assert (H := inner_pasch Q R X1 P A (between_symmetry X1 P Q HCol1) HCol3);
      destruct H as [I [HPRI HQAI]]; exists I; split; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HRBI HAQI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : two_sides Q R A B).
    {
    apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
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
          split; try (intro; treat_equalities); Between.
          }
        }
      }
    }
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  assert (HTS : two_sides R B A Q).
    {
    apply l9_8_2 with X1.

      {
      apply l9_8_2 with X2.

        {
        split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HRBI HAQI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
      assert (HTS : two_sides R A Q B).
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
      destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
      exists I'; right; right; assert_cols; Col.
      }

      {
      elim (eq_dec_points R X1); intro HRX1; treat_equalities.

        {
        exfalso; apply HNC; assert_cols; Col.
        }

        {
        assert (HTS : two_sides R B A Q).
          {
          apply l9_8_2 with X1.

            {
            split; assert_diffs; Col.
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
        destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : two_sides Q R A B).
    {
    apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : two_sides Q R B A).
    {
    apply l9_8_2 with X1.

      {
      split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAPR HAQR HBPQ HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; ColR.
  }

  {
  assert (HTS : two_sides Q R B A).
    {
    apply l9_8_2 with X1.

      {
      split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
      assert (HTS : two_sides Q A B R).
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
            split; assert_diffs; Col.
            split; Col.
            split; Col.
            exists I1; assert_cols; split; Col; Between.
            }

            {
            split; assert_diffs; Col.
            split; Col.
            split; Col.
            exists I2; assert_cols; split; Col; Between.
            }
          }
        }
      destruct HTS as [H1 [H2 [H3 [I' [HQAI' HRBI']]]]]; clear H1; clear H2; clear H3.
      exists I'; right; left; assert_cols; Col.
      }

      {
      assert (HTS : two_sides Q B R A).
        {
        apply l9_8_2 with P.

          {
          split; assert_diffs; Col.
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
      destruct HTS as [H1 [H2 [H3 [I' [HQBI' HRAI']]]]]; clear H1; clear H2; clear H3.
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
      assert (HTS : two_sides Q B A R).
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
            split; assert_diffs; Col.
            split; Col.
            split; Col.
            exists I2; assert_cols; split; Col; Between.
            }

            {
            split; assert_diffs; Col.
            split; Col.
            split; Col.
            exists I1; assert_cols; split; Col; Between.
            }
          }
        }
      destruct HTS as [H1 [H2 [H3 [I' [HQBI' HRAI']]]]]; clear H1; clear H2; clear H3.
      exists I'; right; right; assert_cols; Col.
      }

      {
      assert (HTS : two_sides Q A R B).
        {
        apply l9_8_2 with P.

          {
          split; assert_diffs; Col.
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
      destruct HTS as [H1 [H2 [H3 [I' [HQAI' HRBI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
        assert (H : coplanar R Q B A) by (apply coplanar_trans_1_aux_3_1_2 with P X2 X1; Col); Cop.
        }

        {
        assert (H : coplanar R Q B A) by (apply coplanar_trans_1_aux_3_1_3 with P X2 X1; Col); Cop.
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
        assert (H : coplanar R Q B A) by (apply coplanar_trans_1_aux_3_2_3 with P X2 X1; Col); Cop.
        }

        {
        apply coplanar_trans_1_aux_3_3_3 with P X1 X2; assumption.
        }
      }
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
  coplanar Q R A B.
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
    assert (H : two_sides Q A R B).
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
            split; try assumption.
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
          split; try assumption.
          assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists Q; split; Col; eBetween.
          }
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides B Q R A).
      {
      apply l9_8_2 with P.

        {
        assert (H1 : B <> Q) by (assert_diffs; auto).
        split; try assumption.
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
          split; try assumption.
          assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists B; split; Col; eBetween.
          }

          {
          assert (B <> Q) by (assert_diffs; auto).
          split; try assumption.
          assert (HQX2 : Q <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P Q) by (intro; apply HQX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists Q; split; Col; eBetween.
          }
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
    assert (H : two_sides R A Q B).
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
            split; try assumption.
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
          split; try assumption.
          assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists R; split; Col; eBetween.
          }
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides B R Q A).
      {
      apply l9_8_2 with P.

        {
        assert (H1 : B <> R) by (assert_diffs; auto).
        split; try assumption.
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
          split; try assumption.
          assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists B; split; Col; eBetween.
          }

          {
          assert (B <> R) by (assert_diffs; auto).
          split; try assumption.
          assert (HRX2 : R <> X2) by (intro; treat_equalities; intuition).
          assert (~ Col B P R) by (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; Col.
          split; try (intro; assert_cols; apply HBQR; ColR).
          exists R; split; Col; eBetween.
          }
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (H := outer_pasch X1 P X2 R B HRX1X2 HCol3); destruct H as [U [HPUX1 HRBU]].
apply between_symmetry in HPUX1.
assert (H := l5_3 P A U X1 HCol1 HPUX1).
elim H; clear H; intro HAPU.

  {
  assert (H : two_sides B R Q A).
    {
    apply l9_8_2 with X1.

      {
      assert (H1 : B <> R) by (assert_diffs; auto).
      split; try assumption.
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  assert (H : two_sides R A Q B).
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
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
  assert (H : two_sides R A Q B).

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
          split; try assumption.
          split; try (intro; apply HBQR; ColR).
          split; try (intro; apply HBQR; ColR).
          exists R; split; Col; Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try assumption.
          split; try (intro; apply HRX2; apply l6_21 with Q R P B; assert_diffs; Col).
          split; try (intro; apply HBQR; ColR).
          exists B; split; Col; Between.
          }
        }

        {
        exists X2; split.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try assumption.
          split; try (intro; apply HBQR; ColR).
          split; try (intro; apply HBQR; ColR).
          exists R; split; Col; Between.
          }

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try assumption.
          split; try (intro; apply HBQR; ColR).
          split; try (intro; apply HBQR; ColR).
          exists R; split; Col; eBetween.
          }
        }
      }
    }
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
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
  assert (H' := between_egality R Q X1 HQRX1 H); treat_equalities; exfalso; apply HNC; Col.
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
    assert (H : two_sides R B Q A).

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
            split; try assumption.
            split; try (intro; apply HRX1; apply l6_21 with Q R P A; assert_diffs; Col).
            split; try (intro; apply HAQR; ColR).
            exists A; split; Col; Between.
            }

            {
            apply l9_17 with X2; Between.
            exists X1; split.

              {
              assert (H1 : R <> A) by (assert_diffs; auto).
              split; try assumption.
              split; try (intro; apply HRX1; apply l6_21 with Q R P A; assert_diffs; Col).
              split; try (intro; apply HAQR; ColR).
              exists A; split; Col; Between.
              }

              {
              assert (H1 : R <> A) by (assert_diffs; auto).
              split; try assumption.
              split; try (intro; apply HAQR; ColR).
              split; try (intro; apply HAQR; ColR).
              exists R; split; Col; Between.
              }
            }
          }

          {
          assert (H1 : R <> A) by (assert_diffs; auto).
          split; try assumption.
          split; try (intro; apply HAQR; ColR).
          split; try (intro; apply HAQR; ColR).
          exists R; split; Col; eBetween.
          }
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
    assert (H : two_sides Q B R A).

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
            split; try assumption.
            split; try (intro; apply HQX1; apply l6_21 with Q R P A; assert_diffs; Col).
            split; try (intro; apply HAQR; ColR).
            exists A; split; Col; Between.
            }

            {
            apply l9_17 with X2; Between.
            exists X1; split.

              {
              assert (H1 : Q <> A) by (assert_diffs; auto).
              split; try assumption.
              split; try (intro; apply HQX1; apply l6_21 with Q R P A; assert_diffs; Col).
              split; try (intro; apply HAQR; ColR).
              exists A; split; Col; Between.
              }

              {
              assert (H1 : Q <> A) by (assert_diffs; auto).
              split; try assumption.
              split; try (intro; apply HAQR; ColR).
              split; try (intro; apply HAQR; ColR).
              exists Q; split; Col; Between.
              }
            }
          }

          {
          assert (H1 : Q <> A) by (assert_diffs; auto).
          split; try assumption.
          split; try (intro; apply HAQR; ColR).
          split; try (intro; apply HAQR; ColR).
          exists Q; split; Col; Between.
          }
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  assert (H : Bet X1 Q R) by eBetween.
  apply between_symmetry in HQRX1.
  apply between_symmetry in H.
  assert (H' := between_egality R Q X1 H HQRX1); treat_equalities; exfalso; apply HNC; Col.
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
  coplanar Q R A B.
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
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_1_1_2 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar R Q A B) by (apply coplanar_trans_1_aux_2_1_1_1_3 with P X1 X2; Col; Between); Cop.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_1_1_1 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_1_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar R Q B A) by (apply coplanar_trans_1_aux_2_1_1_1_3 with P X2 X1; Col; Between); Cop.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2 HCol2 HCol4 HCol1 HCol3.
assert (H : two_sides Q R A B).
  {
  apply l9_8_2 with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    split; try assumption.
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
destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
exists I; assert_cols; Col5.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2 HCol2 HCol4 HCol1 HCol3.
assert (H : two_sides Q R B A).
  {
  apply l9_8_2 with P.

    {
    assert (H1 : Q <> R) by (assert_diffs; auto).
    split; try assumption.
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
destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
exists I; assert_cols; Col5.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
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
      split; try (intro; treat_equalities); Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
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
      split; try (intro; treat_equalities); Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
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
      split; try (intro; treat_equalities); Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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

End Coplanar_trans_1.