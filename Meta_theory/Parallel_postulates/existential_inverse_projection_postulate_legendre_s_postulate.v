Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section existential_inverse_projection_postulate_legendre_s_postulate.

Context `{T2D:Tarski_2D}.

Lemma existential_inverse_projection_postulate__legendre_s_postulate :
  existential_inverse_projection_postulate -> legendre_s_postulate.
Proof.
intros [A [B [C [HNC [HAcute HP]]]]]; exists A, B, C; split; try split; Col.
intros T HInAngle; elim (Col_dec A B T); intro HABT.

  {
  assert (HNC' : ~ Col B C T)
    by (intro; apply HNC; unfold InAngle in *; spliter; ColR).
  destruct (l8_18_existence B C T) as [Y [HC HPerp]]; [auto|exists T, Y].
  assert (HOut : Out B A T).
    {
    apply col_in_angle_out with C; try (intro; apply HNC; assert_cols); Col.
    }
  split; [|split]; Between.
  apply l6_6; apply acute_col_perp__out with T; Col.
  apply acute_conga__acute with A B C; auto.
  apply out213_suma__conga with T B A; try apply l6_6; auto.
  exists C; split; [|split]; try apply col123__nos; Col;
  apply conga_refl; assert_diffs; auto.
  }

  {
  destruct (l8_18_existence A B T) as [X [HC HPerp]]; Col.
  assert (HOut1 : Out B A X).
    {
    apply l6_6; apply acute_col_perp__out with T; Col; Perp.
    apply acute_lea_acute with A B C; auto.
    apply lea_left_comm; apply l11_29_b;
    exists C; split; auto; apply conga_refl; assert_diffs; auto.
    }
  destruct (HP X T) as [Y [HOut2 H]];
  try apply perp_per_1; try solve[assert_diffs; auto];
  try apply perp_sym; try apply perp_col0 with A B;
  try solve[assert_diffs; assert_cols; Col].
  exists X, Y; repeat (split; auto); elim H; clear H; intro H; auto.
  elim (eq_dec_points T Y); intro HTY; treat_equalities; Between.
  assert (HACT : ~ Col B C T).
    {
    intro; apply HTY; apply l6_21 with B C X T; Col;
    try solve[assert_diffs; auto]; try (intro; apply HNC; assert_diffs; ColR).
    elim H; assert_cols; Col.
    }
  elim H; clear H; intro HBet.

    {
    assert (HOS : OS C B T A)
      by (apply in_angle_one_side; try apply l11_24; Col).
    exfalso; apply (l9_9_bis _ _ _ _ HOS).
    apply l9_2; apply l9_8_2 with X.

      {
      split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
      split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
      exists Y; assert_cols; split; Col; Between.
      }

      {
      apply l9_19 with B; try split; try apply l6_6; assert_diffs; assert_cols;
      Col; intro; apply HNC; ColR.
      }
    }

    {
    assert (HOS : OS A B T C) by (apply in_angle_one_side; Col).
    exfalso; apply (l9_9_bis _ _ _ _ HOS).
    apply l9_2; apply l9_8_2 with Y.

      {
      split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
      split; [intro; assert_diffs; assert_cols; apply HNC; ColR|].
      exists X; assert_cols; split; Col; Between.
      }

      {
      apply l9_19 with B; try split; try apply l6_6; assert_diffs; assert_cols;
      Col; intro; apply HNC; ColR.
      }
    }
  }
Qed.

End existential_inverse_projection_postulate_legendre_s_postulate.