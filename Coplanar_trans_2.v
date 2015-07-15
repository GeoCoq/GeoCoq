Require Import Coplanar_perm.

Section Coplanar_trans_2.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

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
      assert (H : two_sides Q B A R).
        {
        apply l9_8_2 with X1.

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          split; try assumption.
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
      destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
      assert (H : two_sides Q A R B).
        {
        apply l9_31.

          {
          exists P; split.

            {
            assert (H1 : Q <> R) by (assert_diffs; auto).
            split; try assumption.
            split; Col.
            split; Col.
            exists X1; split; Col; Between.
            }

            {
            assert (H1 : Q <> R) by (assert_diffs; auto).
            split; try assumption.
            split; Col.
            split; Col.
            exists X2; split; Col; Between.
            }
          }

          {
          exists X1; split.

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            split; try assumption.
            split; Col.
            split; try (intro; assert_cols; apply HABQ; ColR).
            exists U; split; Col; Between.
            }

            {
            assert (H1 : Q <> B) by (assert_diffs; auto).
            split; try assumption.
            split; Col.
            split; try (intro; assert_cols; apply HABQ; ColR).
            exists Q; split; Col; Between.
            }
          }
        }
      destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
      assert (H : two_sides R B A Q).
        {
        apply l9_8_2 with X1.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try assumption.
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
      destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
      assert (H : two_sides R A Q B).
        {
        apply l9_31.

          {
          exists P; split.

            {
            assert (H1 : R <> Q) by (assert_diffs; auto).
            split; try assumption.
            split; Col.
            split; Col.
            exists X1; split; Col; Between.
            }

            {
            assert (H1 : R <> Q) by (assert_diffs; auto).
            split; try assumption.
            split; Col.
            split; Col.
            exists X2; split; Col; Between.
            }
          }

          {
          exists X1; split.

            {
            assert (H1 : R <> B) by (assert_diffs; auto).
            split; try assumption.
            split; Col.
            split; try (intro; assert_cols; apply HABR; ColR).
            exists U; split; Col; Between.
            }

            {
            assert (H1 : R <> B) by (assert_diffs; auto).
            split; try assumption.
            split; Col.
            split; try (intro; assert_cols; apply HABR; ColR).
            exists R; split; Col; Between.
            }
          }
        }
      destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  assert (H : two_sides B Q R A).
    {
    apply l9_8_2 with P.

      {
      assert (B <> Q) by (assert_diffs; auto).
      split; try assumption.
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }
    
  {
  assert (H := outer_pasch B Q X2 P X1 HCol3 HQX1X2); destruct H as [U [HBUQ HPX1U]].
  apply between_symmetry in HCol1.
  assert (HPX1 : P <> X1) by (intro; treat_equalities; assert_cols; apply HNC; Col).
  assert (H := l5_2 P X1 A U HPX1 HCol1 HPX1U).
  elim H; clear H; intro HAX1U.

    {
    assert (H : two_sides Q A R B).
      {
      apply l9_31.

        {
        exists P; split.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          split; try assumption.
          split; Col.
          split; Col.
          exists X1; split; Col; Between.
          }

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          split; try assumption.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides B Q R A).
      {
      apply l9_8_2 with X1.

        {
        assert (B <> Q) by (assert_diffs; auto).
        split; try assumption.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  assert (H : two_sides B Q R A).
    {
    apply l9_8_2 with P.

      {
      assert (B <> Q) by (assert_diffs; auto).
      split; try assumption.
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }
    
  {
  assert (H := outer_pasch B Q X2 P X1 HCol3 HQX1X2); destruct H as [U [HBUQ HPX1U]].
  apply between_symmetry in HCol1.
  assert (HPX1 : P <> X1) by (intro; treat_equalities; assert_cols; apply HNC; Col).
  assert (H := l5_2 P X1 A U HPX1 HCol1 HPX1U).
  elim H; clear H; intro HAX1U.

    {
    assert (H : two_sides Q A R B).
      {
      apply l9_31.

        {
        exists P; split.

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          split; try assumption.
          split; Col.
          split; Col.
          exists X1; split; Col; Between.
          }

          {
          assert (H1 : Q <> R) by (assert_diffs; auto).
          split; try assumption.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides B Q R A).
      {
      apply l9_8_2 with X1.

        {
        assert (B <> Q) by (assert_diffs; auto).
        split; try assumption.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
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
    assert (H : two_sides A Q B R).
      {
      apply l9_8_2 with X2.

        {
        assert (A <> Q) by (assert_diffs; auto).
        split; try assumption.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
    assert (H : two_sides A R B Q).
      {
      apply l9_8_2 with X2.

        {
        assert (A <> R) by (assert_diffs; auto).
        split; try assumption.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
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
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_2_2_1_2 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar R Q A B) by (apply coplanar_trans_1_aux_2_2_2_1_3 with P X1 X2; Col; Between); Cop.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_2_2_1_1 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_2_2_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar R Q B A) by (apply coplanar_trans_1_aux_2_2_2_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_2_2_2_2_2 with P X1 X2; assumption.
    }
  }
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
  coplanar Q R A B.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides A R Q B).
      {
      apply l9_8_2 with X2.

        {
        assert (A <> R) by (assert_diffs; auto).
        split; try assumption.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides A Q R B).
      {
      apply l9_8_2 with X2.

        {
        assert (A <> Q) by (assert_diffs; auto).
        split; try assumption.
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HCol1.
assert (H := outer_pasch Q A X1 X2 P HQX1X2 HCol1); destruct H as [U [HAUQ HX2PU]].
assert (HPX2 : X2 <> P) by (intro; treat_equalities; apply HNC; Col).
assert (H := l5_2 X2 P B U HPX2 HCol3 HX2PU).
elim H; clear H; intro HBPU.

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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  assert (H : two_sides A Q R B).
    {
    apply l9_8_2 with X2.

      {
      assert (A <> Q) by (assert_diffs; auto).
      split; try assumption.
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HCol1.
assert (H := outer_pasch Q A X1 X2 P HQX1X2 HCol1); destruct H as [U [HAUQ HX2PU]].
assert (HPX2 : X2 <> P) by (intro; treat_equalities; apply HNC; Col).
assert (H := l5_2 X2 P B U HPX2 HCol3 HX2PU).
elim H; clear H; intro HBPU.

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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  assert (H : two_sides A Q R B).
    {
    apply l9_8_2 with X2.

      {
      assert (A <> Q) by (assert_diffs; auto).
      split; try assumption.
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
apply between_symmetry in HQX1X2.
apply between_symmetry in HRX1X2.
assert (HOS : one_side Q R A B).
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
    assert (H : two_sides Q A R B).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides Q A R B).
      {
      apply l9_31; try assumption.
      exists X1; split.

        {
        apply between_symmetry in HCol3.
        assert (H := inner_pasch B X1 X2 P Q HCol3 HQX1X2); destruct H as [U [HPUX1 HBUQ]].
        assert (Q <> B) by (assert_diffs; auto).
        split; try assumption.
        split; Col.
        split; try (intro; apply HBQR; ColR).
        exists U; assert_cols; split; Col; eBetween.
        }

        {
        assert (Q <> B) by (assert_diffs; auto).
        split; try assumption.
        split; Col.
        split; try (intro; apply HBQR; ColR).
        exists Q; split; Col; Between.
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }
  }

  {
  elim (eq_dec_points R X1); intro HRX1; treat_equalities.

    {
    assert (H : two_sides R A Q B).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
    exists I; assert_cols; Col5.
    }

    {
    assert (H : two_sides R A Q B).
      {
      apply l9_31; try (apply invert_one_side; assumption).
      exists X1; split.

        {
        apply between_symmetry in HCol3.
        assert (H := inner_pasch B X1 X2 P R HCol3 HRX1X2); destruct H as [U [HPUX1 HBUR]].
        assert (R <> B) by (assert_diffs; auto).
        split; try assumption.
        split; Col.
        split; try (intro; apply HBQR; ColR).
        exists U; assert_cols; split; Col; eBetween.
        }

        {
        assert (R <> B) by (assert_diffs; auto).
        split; try assumption.
        split; Col.
        split; try (intro; apply HBQR; ColR).
        exists R; split; Col; Between.
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
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
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_3_3_1_2 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar R Q A B) by (apply coplanar_trans_1_aux_2_3_3_1_3 with P X1 X2; Col; Between); Cop.
    }
  }

  {
  elim HQX1X2; clear HQX1X2; intro HQX1X2; elim HRX1X2; clear HRX1X2; intro HRX1X2.

    {
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_3_3_1_1 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_2_3_3_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    assert (coplanar R Q B A) by (apply coplanar_trans_1_aux_2_3_3_1_3 with P X2 X1; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_2_3_3_2_2 with P X1 X2; assumption.
    }
  }
Qed.

End Coplanar_trans_2.