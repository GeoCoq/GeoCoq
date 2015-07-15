Require Export Coplanar_trans_1.
Require Export Coplanar_trans_2.
Require Export Coplanar_trans_3.
Require Export Coplanar_trans_4.

Section Coplanar_trans.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

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
  coplanar Q R A B.
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
        assert (H : coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_2 with P X2 X1; Col; Between); Cop.
        }

        {
        assert (H : coplanar Q R B A) by (apply coplanar_trans_1_aux_2_1_3 with P X2 X1; Col; Between); Cop.
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
        assert (H : coplanar Q R B A) by (apply coplanar_trans_1_aux_2_2_3 with P X2 X1; Col; Between); Cop.
        }

        {
        apply coplanar_trans_1_aux_2_3_3 with P X1 X2; assumption.
        }
      }
    }
  }
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  coplanar Q R A B.
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
  ~Col P Q R -> coplanar P Q R A -> coplanar P Q R B -> coplanar Q R A B.
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
      assert (coplanar R Q A B) by (apply coplanar_trans_1_aux_3 with P X1 X2; Col); Cop.
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
        assert (coplanar R Q A B) by (apply coplanar_trans_1_aux_4 with P X1 X2; Col); Cop.
        }
      }
    }

    {
    elim HCop2; clear HCop2; intro HCop2; try (destruct HCop2 as [HCol3 HCol4]).

      {
      assert (coplanar Q R B A) by (apply coplanar_trans_1_aux_4 with P X2 X1; Col); Cop.
      }

      {
      elim HCop2; clear HCop2; intro HCop2; try (destruct HCop2 as [HCol3 HCol4]).

        {
        assert (coplanar R Q B A) by (apply coplanar_trans_1_aux_4 with P X2 X1; Col); Cop.
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
  coplanar P Q R A ->
  coplanar P Q R B ->
  coplanar P Q R C ->
  coplanar P Q R D ->
  coplanar A B C D.
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