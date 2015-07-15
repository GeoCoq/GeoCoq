Require Import Coplanar_perm.

Section Coplanar_trans_3.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HOS : one_side Q R A B).
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
  assert (H : two_sides Q B R A).
    {
    apply l9_31; apply one_side_symmetry; try assumption.
    exists X2; split.

      {
      assert (H1 : Q <> A) by (assert_diffs; auto).
      split; try assumption.
      split; Col.
      assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      exists Q; split; Col; eBetween.
      }

      {
      assert (H := outer_pasch X2 P X1 Q A HQX1X2 HCol1); destruct H as [U [HPUX2 HQAU]].
      assert (H1 : Q <> A) by (assert_diffs; auto).
      split; try assumption.
      split; Col.
      assert (Q <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      exists U; split; Col; eBetween.
      }
    }
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
  exists I; assert_cols; Col5.
  }

  {
  assert (H : two_sides R B Q A).
    {
    apply l9_31; apply one_side_symmetry; apply invert_one_side; try assumption.
    exists X2; split.

      {
      assert (H1 : A <> R) by (assert_diffs; auto).
      split; try assumption.
      split; Col.
      assert (R <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      exists R; split; Col; eBetween.
      }

      {
      assert (H := outer_pasch X2 P X1 R A HRX1X2 HCol1); destruct H as [U [HPUX2 HRAU]].
      assert (H1 : A <> R) by (assert_diffs; auto).
      split; try assumption.
      split; Col.
      assert (R <> X2) by (intro; treat_equalities; apply HX1X2; reflexivity).
      split; try (intro; apply HAQR; ColR).
      exists U; split; Col; eBetween.
      }
    }
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (H : two_sides A Q R B).
  {
  apply l9_8_2 with X2.

    {
    apply between_symmetry in HQX1X2.
    assert (H := outer_pasch X2 P X1 Q A HQX1X2 HCol1); destruct H as [U [HPUX2 HQAU]].
    assert (H1 : A <> Q) by (assert_diffs; auto).
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
    split; auto.
    split; try (intro; treat_equalities; intuition).
    eBetween.
    }
  }
destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (H : two_sides A Q R B).
  {
  apply l9_8_2 with X2.

    {
    apply between_symmetry in HQX1X2.
    assert (H := outer_pasch X2 P X1 Q A HQX1X2 HCol1); destruct H as [U [HPUX2 HQAU]].
    assert (H1 : A <> Q) by (assert_diffs; auto).
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
    split; auto.
    split; try (intro; treat_equalities; intuition).
    eBetween.
    }
  }
destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HQRX2 := l5_2 X1 X2 Q R HX1X2 HQX1X2 HRX1X2).
assert (HOS : one_side Q R A B).
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
    assert (H : two_sides Q B R A).
      {
      apply l9_31; apply one_side_symmetry; try assumption.
      exists X2; split.

        {
        assert (H1 : Q <> A) by (assert_diffs; auto).
        split; try assumption.
        split; Col.
        split; try (intro; apply HAQR; ColR).
        exists Q; split; Col; eBetween.
        }

        {
        apply between_symmetry in HQX1X2.
        assert (H := inner_pasch P Q X1 A X2 HCol1 HQX1X2); destruct H as [U [HAUQ HPUX2]].
        assert (H1 : Q <> A) by (assert_diffs; auto).
        split; try assumption.
        split; Col.
        split; try (intro; apply HAQR; ColR).
        exists U; split; Col; eBetween.
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
    assert (H : two_sides R B Q A).
      {
      apply l9_31; apply one_side_symmetry; apply invert_one_side; try assumption.
      exists X2; split.

        {
        assert (H1 : A <> R) by (assert_diffs; auto).
        split; try assumption.
        split; Col.
        split; try (intro; apply HAQR; ColR).
        exists R; split; Col; eBetween.
        }

        {
        apply between_symmetry in HRX1X2.
        assert (H := inner_pasch P R X1 A X2 HCol1 HRX1X2); destruct H as [U [HAUR HPUX2]].
        assert (H1 : A <> R) by (assert_diffs; auto).
        split; try assumption.
        split; Col.
        split; try (intro; apply HAQR; ColR).
        exists U; split; Col; eBetween.
        }
      }
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HOS : one_side Q R A B).
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
  assert (H : two_sides Q A B R).
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
  destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABP HABQ HABR HAQR HBQR HAX1 HAX2 HX1X2;
intros HCol2 HCol4 HCol1 HCol3 HQX1X2 HRX1X2.
assert (HOS : one_side Q R A B).
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
  assert (H' := between_egality R Q X1 HQRX1 H); treat_equalities; exfalso; apply HNC; Col.
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
      assert (H : two_sides Q A B R).
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
      destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
      assert (H : two_sides Q B A R).
        {
        apply l9_8_2 with X1.

          {
          assert (H1 : Q <> B) by (assert_diffs; auto).
          split; try assumption.
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
      destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
    assert (H : two_sides R A B Q).
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
    destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
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
      assert (H : two_sides R B A Q).
        {
        apply l9_8_2 with X1.

          {
          assert (H1 : R <> B) by (assert_diffs; auto).
          split; try assumption.
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
      destruct H as [HDiff [HCol5 [HCol6 [I [HCol7 HCol8]]]]].
      exists I; assert_cols; Col5.
      }
    }
  }

  {
  assert (H : Bet X1 Q R) by eBetween.
  apply between_symmetry in HQRX1.
  apply between_symmetry in H.
  assert (H' := between_egality R Q X1 H HQRX1); treat_equalities; exfalso; apply HNC; Col.
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
  coplanar Q R A B.
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
    assert (coplanar R Q A B) by (apply coplanar_trans_1_aux_2_1_3_1_2 with P X1 X2; Col; Between); Cop.
    }

    {
    assert (coplanar R Q A B) by (apply coplanar_trans_1_aux_2_1_3_1_3 with P X1 X2; Col; Between); Cop.
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
    assert (coplanar R Q A B) by (apply coplanar_trans_1_aux_2_1_3_2_3 with P X1 X2; Col; Between); Cop.
    }

    {
    apply coplanar_trans_1_aux_2_1_3_3_3 with P X1 X2; assumption.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol4 HCol1 HCol2 HCol3.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  exfalso; apply HAQR; assert_cols; Col.
  }

  {
  assert (HTS : two_sides Q R B A).
    {
    apply l9_8_2 with P.

      {
      apply l9_2; apply l9_8_2 with X1.

        {
        split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (HTS : two_sides R A Q B).
    {
    apply l9_31.

      {
      exists P; split.

        {
        apply l9_8_2 with X1.

          {
          split; assert_diffs; Col.
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
        split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
    assert (HTS : two_sides R B Q A).
      {
      apply l9_31.

        {
        exists P; split.

          {
          split; assert_diffs; Col.
          split; Col.
          split; Col.
          exists X2; assert_cols; split; Col; Between.
          }

          {
          split; assert_diffs; Col.
          split; Col.
          split; Col.
          assert (H := inner_pasch P R X1 Q A HCol1 HCol2); destruct H as [I' [HQRI' HPAI']].
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
    destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
    exists I'; right; left; split; Col.
    }

    {
    assert (HTS : two_sides R A Q B).
      {
      apply l9_8_2 with P.

        {
        split; assert_diffs; Col.
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
    destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points R X1); intro HRX1; treat_equalities.

  {
  exfalso; apply HNC; assert_cols; Col.
  }

  {
  assert (HTS : two_sides Q A R B).
    {
    apply l9_31.

      {
      exists P; split.

        {
        apply l9_8_2 with X1.

          {
          split; assert_diffs; Col.
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
        split; assert_diffs; Col.
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
          split; assert_diffs; Col.
          split; Col.
          split; Col.
          exists I; assert_cols; split; Col; Between.
          }

          {
          split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  exfalso; apply HAQR; assert_cols; Col.
  }

  {
  assert (HTS : two_sides Q R B A).
    {
    apply l9_8_2 with P.

      {
      apply l9_2; apply l9_8_2 with X1.

        {
        split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  exfalso; apply HAQR; assert_cols; Col.
  }

  {
  assert (HTS : two_sides Q R B A).
    {
    apply l9_8_2 with P.

      {
      apply l9_2; apply l9_8_2 with X1.

        {
        split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R A Q B).
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
        split; assert_diffs; Col.
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
      split; assert_diffs; Col.
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
destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
        assert (HTS : two_sides R B Q A).
          {
          apply l9_31.

            {
            apply one_side_transitivity with X1.

              {
              exists P; split.

                {
                split; assert_diffs; Col.
                split; Col.
                split; Col.
                exists X2; assert_cols; split; Col.
                }

                {
                apply l9_2.
                split; assert_diffs; Col.
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
        destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
        exists I'; right; left; split; Col.
        }

        {
        assert (HTS : two_sides R A Q B).
          {
          apply l9_8_2 with P.

            {
            split; assert_diffs; Col.
            show_distinct P X1; try (apply HAQR; Col).
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
        destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch B R X2 P Q HCol3 (between_symmetry X2 Q R HCol4));
destruct H as [I [HRBI HPQI]].
assert (HPQ : P <> Q) by (assert_diffs; Col).
assert (H := l5_2 P Q X1 I HPQ HCol1 HPQI); elim H; clear HPQ; clear H; intro HQX1I.

  {
  assert (HTS : two_sides R A Q B).
    {
    apply l9_31.

      {
      exists P; split.

        {
        apply l9_8_2 with X1.

          {
          split; assert_diffs; Col.
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
        split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; right; split; Col.
  }

  {
  assert (HTS : two_sides R B A Q).
    {
    apply l9_8_2 with X1.

      {
      split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X1); intro HQX1; treat_equalities.

  {
  exfalso; apply HAQR; assert_cols; Col.
  }

  {
  assert (HTS : two_sides Q R B A).
    {
    apply l9_8_2 with P.

      {
      apply l9_2; apply l9_8_2 with X1.

        {
        split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (H := outer_pasch P X2 Q X1 R HCol1 (between_symmetry Q R X2 HCol4));
destruct H as [I[HPX2I HRX1I]].
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
assert (HRAI : Col R A I) by (assert_cols; ColR).
assert (H := l5_3 P B I X2 HCol3 HPX2I); elim H; clear H; intro HPBI.

  {
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
        exists X1; split.

          {
          split; assert_diffs; Col.
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          exists Q; Col.
          }

          {
          split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; left; split; Col.
  }

  {
  assert (HTS : two_sides R A Q B).
    {
    apply l9_8_2 with P.

      {
      split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
elim (eq_dec_points R X2); intro HRX2; treat_equalities.

  {
  assert (HTS : two_sides R B Q A).
    {
    apply l9_8_2 with X1.

      {
      split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
  exists I'; right; left; split; Col.
  }

  {
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
        exists X1; split.

          {
          split; assert_diffs; Col.
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          exists Q; Col.
          }

          {
          split; assert_diffs; Col.
          split; Col.
          split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
          exists R; split; Col; Between.
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
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
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
      exists X1; split.

        {
        split; assert_diffs; Col.
        split; Col.
        split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
        exists Q; Col.
        }

        {
        split; assert_diffs; Col.
        split; Col.
        split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
        exists R; split; Col; Between.
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
  destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R A Q B).
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
        split; assert_diffs; Col.
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
      split; assert_diffs; Col.
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
destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
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
    exists X1; split.

      {
      split; assert_diffs; Col.
      split; Col.
      split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
      exists Q; Col.
      }

      {
      split; assert_diffs; Col.
      split; Col.
      split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
      exists R; split; Col; Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HRX1 : R <> X1) by (intro; treat_equalities; assert_cols; Col).
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
    exists X1; split.

      {
      split; assert_diffs; Col.
      split; Col.
      split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
      exists Q; Col.
      }

      {
      split; assert_diffs; Col.
      split; Col.
      split; try (intro; treat_equalities; apply HAQR; assert_cols; ColR).
      exists R; split; Col; Between.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQRI HABI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q A R B).
  {
  assert (HOS : one_side Q A R X2).
    {
    assert (H1 : Q <> A) by (assert_diffs; auto).
    assert (H2 : Col Q A Q) by Col.
    assert (H3 : Col R X2 Q) by (assert_cols; ColR).
    assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
    split; Col.
    split; assert_diffs; Col.
    split; try (intro; treat_equalities); Between.
    }
  assert (HTS1 : two_sides Q A P R).
    {
    apply l9_2.
    assert (H := inner_pasch P A X1 Q R HCol1 (between_symmetry X1 R A HCol2));
    destruct H as [I [HQAI HPRI]].
    split; assert_diffs; Col.
    split; Col.
    show_distinct A X1; Col.
    split; try (intro; apply HNC; assert_cols; ColR).
    exists I; assert_cols; Col.
    }
  assert (HTS2 : two_sides Q A P X2)
    by (apply l9_2; apply l9_8_2 with R; try apply l9_2; Col).
  apply l9_2; apply l9_8_2 with P; Col.
  destruct HTS2 as [H1 [H2 [HQAX2 [I [HQAI HPX2I]]]]]; clear H1; clear H2.
  assert (H1 : Q <> A) by (assert_diffs; auto).
  assert (H2 : Col Q A I) by (assert_cols; Col).
  assert (H3 : Col P B I) by (show_distinct P X2; Col; assert_cols; ColR).
  assert (H := l9_19 Q A P B I H1 H2 H3); rewrite H.
  split; try (intro; unfold two_sides in HTS1; spliter; Col).
  split; try (intro; treat_equalities; unfold two_sides in HTS1; spliter; Col).
  split; try (intro; treat_equalities; Col).
  eBetween.
  }
destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
elim (eq_dec_points Q X2); intro HQX2; treat_equalities.

  {
  assert (HTS : two_sides Q A B R).
    {
    apply l9_8_2 with P.

      {
      apply l9_2.
      assert (H := inner_pasch P A X1 Q R HCol1 (between_symmetry X1 R A HCol2));
        destruct H as [I [HQAI HPRI]].
      split; assert_diffs; Col.
      split; Col.
      show_distinct A X1; Col.
      split; try (intro; apply HNC; assert_cols; ColR).
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
  destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
  exists I; right; left; split; Col.
  }

  {
  assert (HTS : two_sides Q A R B).
    {
    assert (HOS : one_side Q A R X2).
      {
      assert (H1 : Q <> A) by (assert_diffs; auto).
      assert (H2 : Col Q A Q) by Col.
      assert (H3 : Col R X2 Q) by (assert_cols; ColR).
      assert (H := l9_19 Q A R X2 Q H1 H2 H3); rewrite H.
      split; Col.
      split; assert_diffs; Col.
      split; try (intro; treat_equalities); Between.
      }
    assert (HTS1 : two_sides Q A P R).
      {
      apply l9_2.
      assert (H := inner_pasch P A X1 Q R HCol1 (between_symmetry X1 R A HCol2));
        destruct H as [I [HQAI HPRI]].
      split; assert_diffs; Col.
      split; Col.
      show_distinct A X1; Col.
      split; try (intro; apply HNC; assert_cols; ColR).
      exists I; assert_cols; Col.
      }
    assert (HTS2 : two_sides Q A P X2)
      by (apply l9_2; apply l9_8_2 with R; try apply l9_2; Col).
    apply l9_2; apply l9_8_2 with P; Col.
    destruct HTS2 as [H1 [H2 [HQAX2 [I [HQAI HPX2I]]]]]; clear H1; clear H2.
    assert (H1 : Q <> A) by (assert_diffs; auto).
    assert (H2 : Col Q A I) by (assert_cols; Col).
    assert (H3 : Col P B I) by (show_distinct P X2; Col; assert_cols; ColR).
    assert (H := l9_19 Q A P B I H1 H2 H3); rewrite H.
    split; try (intro; unfold two_sides in HTS1; spliter; Col).
    split; try (intro; treat_equalities; unfold two_sides in HTS1; spliter; Col).
    split; try (intro; treat_equalities; Col).
    eBetween.
    }
  destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  assert (HTS : two_sides Q B A R).
    {
    apply l9_8_2 with I1.

      {
      split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQBI HRAI]]]]]; clear H1; clear H2; clear H3.
  exists I; right; right; split; Col.
  }

  {
  assert (HTS : two_sides Q A B R).
    {
    apply l9_8_2 with I2.

      {
      split; assert_diffs; Col.
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
  destruct HTS as [H1 [H2 [H3 [I [HQAI HRBI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
      assert (HTS : two_sides R B Q A).
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
              split; try (intro; treat_equalities); Between.
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
      destruct HTS as [H1 [H2 [H3 [I' [HRBI' HQAI']]]]]; clear H1; clear H2; clear H3.
      exists I'; right; left; split; Col.
      }
    }

    {
    assert (HTS : two_sides R A Q B).
      {
      apply l9_8_2 with X2.

        {
        split; assert_diffs; Col.
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
    destruct HTS as [H1 [H2 [H3 [I' [HRAI' HQBI']]]]]; clear H1; clear H2; clear H3.
    exists I'; right; right; split; Col.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q A B R).
  {
  elim (eq_dec_points A X1); intro HAX1; treat_equalities.

    {
    assert (HQX2 : Q <> X2) by (intro; treat_equalities; Col).
    apply l9_2; apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
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
    assert (HOS1 : one_side Q A P X1).
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
    assert (HOS2 : one_side Q A R X2).
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
    assert (HTS : two_sides Q A P X2).
      {
      apply l9_2; apply l9_8_2 with R; Col.
      apply l9_2; apply l9_8_2 with X1; try apply one_side_symmetry; Col.
      split; assert_diffs; Col.
      split; try (intro; assert_cols; apply HAQR; ColR).
      split; Col.
      exists A; split; Col; Between.
      }
    destruct HTS as [Hclear1 [Hclear2 [Hclear3 [I [HQAI HPX2I]]]]].
    clear Hclear1; clear Hclear2; assert_diffs; clear Hclear3.
    apply l9_2; apply l9_8_2 with X2; try apply one_side_symmetry; Col.
    split; assert_diffs; Col.
    split; try (intro; apply HAQR; assert_cols; ColR).
    split; Col.
    exists I; eBetween.
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQAI HBRI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides Q A B R).
  {
  elim (eq_dec_points A X1); intro HAX1; treat_equalities.

    {
    assert (HQX2 : Q <> X2).
      {
      intro; treat_equalities; assert_diffs; assert_cols; apply HABQ; ColR.
      }
    apply l9_2; apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
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
          split; assert_diffs; Col.
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
      assert (HOS1 : one_side Q A P X1).
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
      assert (HOS2 : one_side Q A R X2).
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
      assert (HTS : two_sides Q A P X2).
        {
        apply l9_2; apply l9_8_2 with R; Col.
        apply l9_2; apply l9_8_2 with X1; try apply one_side_symmetry; Col.
        split; assert_diffs; Col.
        split; try (intro; assert_cols; apply HAQR; ColR).
        split; Col.
        exists A; split; Col; Between.
        }
      destruct HTS as [Hclear1 [Hclear2 [Hclear3 [I [HQAI HPX2I]]]]].
      clear Hclear1; clear Hclear2; assert_diffs; clear Hclear3.
      apply l9_2; apply l9_8_2 with X2; try apply one_side_symmetry; Col.
      split; assert_diffs; Col.
      split; try (intro; apply HAQR; assert_cols; ColR).
      split; Col.
      exists I; eBetween.
      }
    }
  }
destruct HTS as [H1 [H2 [H3 [I [HQAI HBRI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
Proof.
intros P Q R A B X1 X2 HNC HABQ HABR HAQR HBQR HCol1 HCol2 HCol3 HCol4.
assert (HTS : two_sides R A Q B).
  {
  elim (eq_dec_points P X1); intro HPX1; treat_equalities.

    {
    apply l9_8_2 with X2.

      {
      split; assert_diffs; Col.
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
    assert (HTS : two_sides R A P X2).
      {
      apply l9_2; apply l9_8_2 with Q.

        {
        split; assert_diffs; Col.
        split; Col.
        split; try (intro; apply HAQR; assert_cols; ColR).
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
      destruct HTS as [H1 [H2 [H3 [I [HRAI HPX2I]]]]]; clear H1; clear H2; clear H3.
      split; assert_diffs; Col.
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
destruct HTS as [H1 [H2 [H3 [I [HRAI HQBI]]]]]; clear H1; clear H2; clear H3.
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
  coplanar Q R A B.
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

End Coplanar_trans_3.