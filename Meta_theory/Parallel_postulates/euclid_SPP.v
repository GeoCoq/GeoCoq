Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_SPP_aux_1.
Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_SPP_aux_2.
Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_SPP_aux_3.
Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_SPP_aux_4.

Section euclid_SPP.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma euclid_5_implies_strong_parallel_postulate_aux :
  euclid_5 ->
  (forall P Q R S T U : Tpoint,
   BetS P T Q ->
   BetS R T S ->
   ~ Col P R U ->
   Coplanar P Q R U ->
   Cong P T Q T ->
   Cong R T S T ->
   OS P R S U ->
   OS P S R U ->
   exists I : Tpoint, Col S Q I /\ Col P U I).
Proof.
intros HE5 P Q R S T U HPTQ HRTS HNC HCop HCong1 HCong2 HOS1 HOS2.
elim (Col_dec P Q S); intro HPQS.

  {
  exists P; Col.
  }

  {
  destruct HCop as [X H]; elim H; clear H; intro H; try (destruct H as [H1 H2]);
  try (elim H; clear H; intro H; destruct H as [H1 H2]).

    {
    elim H1; clear H1; intro H1; try (elim H1; clear H1; intro H1).

      {
      apply euclid_5_implies_strong_parallel_postulate_aux_1_1 with R T X; Col.
      }

      {
      apply euclid_5_implies_strong_parallel_postulate_aux_1_2 with R T X; Col.
      }

      {
      apply euclid_5_implies_strong_parallel_postulate_aux_1_3 with R T X; Col.
      }
    }

    {
    apply euclid_5_implies_strong_parallel_postulate_aux_2 with R T X; Col.
    }

    {
    apply euclid_5_implies_strong_parallel_postulate_aux_3 with R T X; Col.
    }
  }
Qed.

Lemma euclid_5_both_sides :
  euclid_5 ->
  (forall P Q Q' R R' S T T',
   Cong P T Q T ->
   Cong P T' Q' T' ->
   Cong R T S T ->
   Cong R' T' S T' ->
   Cong Q S Q' S ->
   BetS P T Q ->
   Bet P T' Q' ->
   BetS R T S ->
   Bet R' T' S ->
   Bet Q S Q' ->
   ~ Col P Q S ->
   Col P R R').
Proof.
intros HE5 P Q Q' R R' S T T' Hcong1 HCong2 HCong3 HCong4 HCong5 HPTQ HPT'Q' HRTS HR'T'S HQSQ' HPQS.
elim (Col_dec P R R'); intro HPRR'; Col; exfalso.
assert (HPQ'S : ~ Col P Q' S).
  {
  unfold BetS in *; spliter; show_distinct Q' S; Col; intro; apply HPQS; assert_cols; ColR.
  }
assert (H : BetS P T' Q').
  {
  split; Col.
  unfold BetS in *; spliter; split; try (intro; treat_equalities; Col).
  }
clear HPT'Q'; rename H into HPT'Q'.
assert (H : BetS R' T' S).
  {
  split; Col.
  unfold BetS in *; spliter; assert_cols; split; try (intro; treat_equalities; Col).
  }
clear HR'T'S; rename H into HR'T'S.
assert (H : BetS Q S Q').
  {
  split; Col.
  split; try (intro; treat_equalities; Col).
  }
clear HQSQ'; rename H into HQSQ'.
assert (HCop : Coplanar P S R R') by apply all_coplanar.
(* DO NOT REMOVE!!!
  {
  assert (HTS : TS P S R R').
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
            exists S; unfold BetS in *; spliter; Col.
            }

            {
            assert (H3 : P <> S) by (assert_diffs; Col).
            assert (H4 : Col P S P) by Col.
            assert (H5 : Col Q T P) by (unfold BetS in *; spliter; assert_cols; Col).
            assert (H := l9_19 P S Q T P H3 H4 H5); rewrite H.
            split; Col.
            unfold BetS in *; spliter; split; Col.
            }
          }

          {
          assert (H3 : P <> S) by (assert_diffs; Col).
          assert (H4 : Col P S P) by Col.
          assert (H5 : Col Q' T' P) by (unfold BetS in *; spliter; assert_cols; Col).
          assert (H := l9_19 P S Q' T' P H3 H4 H5); rewrite H.
          split; Col.
          unfold BetS in *; spliter; split; Col.
          }
        }

        {
        assert (H3 : P <> S) by (assert_diffs; Col).
        assert (H4 : Col P S S) by Col.
        assert (H5 : Col T' R' S) by (unfold BetS in *; spliter; assert_cols; Col).
        assert (H := l9_19 P S T' R' S H3 H4 H5); rewrite H.
        unfold BetS in *; spliter; split; try (intro; apply HPQ'S; assert_cols; ColR).
        split; Col.
        split; try (intro; treat_equalities); Between.
        }
      }

      {
      assert (H3 : P <> S) by (assert_diffs; Col).
      assert (H4 : Col P S S) by Col.
      assert (H5 : Col T R S) by (unfold BetS in *; spliter; assert_cols; Col).
      assert (H := l9_19 P S T R S H3 H4 H5); rewrite H.
      unfold BetS in *; spliter; split; try (intro; apply HPQS; assert_cols; ColR).
      split; Col.
      split; try (intro; treat_equalities); Between.
      }
    }
  destruct HTS as [Hc1 [Hc2 [Hc3 [I [HPSI HRR'I]]]]]; clear Hc1; clear Hc2; clear Hc3.
  exists I; assert_cols; left; Col.
  }
*)
destruct HCop as [X H]; elim H; clear H; intro H; try (destruct H as [H1 H2]);
try (elim H; clear H; intro H; destruct H as [H1 H2]).

  {
  apply euclid_5_both_sides_1 with P Q Q' R R' S T T' X; Col.
  }

  {
  elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

    {
    apply euclid_5_both_sides_2_1 with P Q Q' R R' S T T' X; Col.
    }

    {
    apply euclid_5_both_sides_2_2 with P Q Q' R R' S T T' X; Col.
    }

    {
    apply euclid_5_both_sides_2_3 with P Q Q' R R' S T T' X; Col.
    }
  }

  {
  elim H2; clear H2; intro H2; try (elim H2; clear H2; intro H2).

    {
    apply euclid_5_both_sides_3_1 with P Q Q' R R' S T T' X; Col.
    }

    {
    apply euclid_5_both_sides_3_2 with P Q Q' R R' S T T' X; Col.
    }

    {
    apply euclid_5_both_sides_3_3 with P Q Q' R R' S T T' X; Col.
    }
  }
Qed.

Lemma euclid_5_implies_strong_parallel_postulate :
  euclid_5 ->
  SPP.
Proof.
intros HE5 P Q R S T U HPTQ HRTS HNC HCop HCong1 HCong2.
elim (Col_dec P Q S); intro HPQS.

  {
  exists P; Col.
  }

  {
  elim (Col_dec P S U); intro HPSU.

    {
    exists S; Col.
    }

    {
    destruct (symmetric_point_construction Q S) as [Q' [HQSQ' HCong3]].
    destruct (midpoint_existence P Q') as [T' [HPT'Q' HCong4]].
    destruct (symmetric_point_construction S T') as [R' [HST'R' HCong5]].
    assert (HPRR' : Col P R R')
      by (apply euclid_5_both_sides with Q Q' S T T'; Col; Cong; Between).
    assert (HPQ'S : ~ Col P Q' S)
      by (intro; unfold BetS in *; spliter; assert_diffs; assert_cols; apply HPQS; ColR).
    assert (HNC' : ~ Col P R' U).
      {
      show_distinct P T'; Col; show_distinct P R';
      try (unfold BetS in *; spliter; assert_cols; apply HPQ'S; ColR).
      intro; unfold BetS in *; spliter; assert_cols; apply HNC; ColR.
      }
    assert (H : BetS P T' Q'); try (clear HPT'Q'; rename H into HPT'Q').
      {
      split; Col.
      split; try (intro; treat_equalities; Col).
      }
    assert (H : BetS R' T' S); try (clear HST'R'; rename H into HR'T'S).
      {
      split; Between.
      repeat split; intro; treat_equalities; unfold BetS in *; spliter; assert_cols; Col.
      }
    assert (HCase1 : OS P R S U -> OS P S R U ->
                     exists I : Tpoint, Col S Q I /\ Col P U I).
      {
      apply euclid_5_implies_strong_parallel_postulate_aux with T; Col.
      }
    assert (HCase2 : OS P R' S U -> OS P S R' U ->
                     exists I : Tpoint, Col S Q I /\ Col P U I).
      {
      assert (HCop' : Coplanar P Q' R' U).
        {
        (*
        apply coplanar_pseudo_trans with P Q R; Cop;
        try (intro; apply BetSEq in HPTQ; apply BetSEq in HRTS;
             spliter; assert_cols; apply HPQS; ColR).
        assert (HTS : TS P Q R Q').
          {
          apply l9_2; apply l9_8_2 with S.

            {
            assert_diffs; split; Col.
            split; Col.
            unfold BetS in *; spliter; assert_cols; split; try (intro; apply HPQS; ColR).
            exists T; split; Col; Between.
            }

            {
            assert (HH3 : P <> Q) by (assert_diffs; Col).
            assert (HH4 : Col P Q Q) by Col.
            assert (HH5 : Col S Q' Q) by (assert_cols; Col).
            assert (HH := l9_19 P Q S Q' Q HH3 HH4 HH5); rewrite HH.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }
        destruct HTS as [Hc1 [Hc2 [Hc3 [I [HPQI HRQ'I]]]]]; exists I; left; assert_cols; Col.
        *)
        apply all_coplanar.
        }
      intros HOS1 HOS2; destruct (euclid_5_implies_strong_parallel_postulate_aux HE5 P Q' R' S T' U)
      as [I [HQ'SI HPUI]]; Cong; show_distinct Q' S; Col; exists I; assert_cols; split; ColR.
      }
    destruct (symmetric_point_construction U P) as [U' HU'].
    assert (HCop' : Coplanar P Q R U').
      {
      (*
      apply coplanar_pseudo_trans with P R U; assert_cols; Cop.
      *)
      apply all_coplanar.
      }
    assert (HCase3 : OS P R S U' -> OS P S R U' ->
                     exists I : Tpoint, Col S Q I /\ Col P U I).
      {
      intros HOS1 HOS2; destruct (euclid_5_implies_strong_parallel_postulate_aux HE5 P Q R S T U')
      as [I [HQSI HPU'I]]; Cong; try (intro; apply HNC; assert_diffs; assert_cols; ColR).
      elim (eq_dec_points P U'); intro; treat_equalities.

        {
        exists Q; Col.
        }

        {
        exists I; assert_cols; split; ColR.
        }
      }
    assert (HCase4 : OS P R' S U' -> OS P S R' U' ->
                    exists I : Tpoint, Col S Q I /\ Col P U I).
      {
      assert (HCop'' : Coplanar P Q' R' U').
        {
        (*
        apply coplanar_pseudo_trans with P Q R; Cop;
        try (intro; apply BetSEq in HPTQ; apply BetSEq in HRTS;
             spliter; assert_cols; apply HPQS; ColR).
        assert (HTS : TS P Q R Q').
          {
          apply l9_2; apply l9_8_2 with S.

            {
            assert_diffs; split; Col.
            split; Col.
            unfold BetS in *; spliter; assert_cols; split; try (intro; apply HPQS; ColR).
            exists T; split; Col; Between.
            }

            {
            assert (HH3 : P <> Q) by (assert_diffs; Col).
            assert (HH4 : Col P Q Q) by Col.
            assert (HH5 : Col S Q' Q) by (assert_cols; Col).
            assert (HH := l9_19 P Q S Q' Q HH3 HH4 HH5); rewrite HH.
            split; Col.
            split; try (intro; treat_equalities; Col).
            split; try (intro; treat_equalities; Col).
            Between.
            }
          }
        destruct HTS as [Hc1 [Hc2 [Hc3 [I [HPQI HRQ'I]]]]]; exists I; left; assert_cols; Col.
        *)
        apply all_coplanar.
        }
      intros HOS1 HOS2; destruct (euclid_5_implies_strong_parallel_postulate_aux HE5 P Q' R' S T' U')
      as [I [HQ'SI HPU'I]]; Cong; try (intro; apply HNC'; assert_diffs; assert_cols; ColR).
      show_distinct Q' S; Col; elim (eq_dec_points P U'); intro; treat_equalities.

        {
        exists Q; Col.
        }

        {
        exists I; assert_cols; split; ColR.
        }
      }
    clear HCop'; assert (HTS : TS P S R R').
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
              exists S; unfold BetS in *; spliter; Col.
              }

              {
              assert (H3 : P <> S) by (assert_diffs; Col).
              assert (H4 : Col P S P) by Col.
              assert (H5 : Col Q T P) by (unfold BetS in *; spliter; assert_cols; Col).
              assert (H := l9_19 P S Q T P H3 H4 H5); rewrite H.
              split; Col.
              unfold BetS in *; spliter; assert_diffs; split; Col.
              }
            }

            {
            assert (H3 : P <> S) by (assert_diffs; Col).
            assert (H4 : Col P S P) by Col.
            assert (H5 : Col Q' T' P) by (unfold BetS in *; spliter; assert_cols; Col).
            assert (H := l9_19 P S Q' T' P H3 H4 H5); rewrite H.
            split; Col.
            unfold BetS in *; spliter; assert_diffs; split; Col.
            }
          }

          {
          assert (H3 : P <> S) by (assert_diffs; Col).
          assert (H4 : Col P S S) by Col.
          assert (H5 : Col T' R' S) by (unfold BetS in *; spliter; assert_cols; Col).
          assert (H := l9_19 P S T' R' S H3 H4 H5); rewrite H.
          unfold BetS in *; spliter; split; try (intro; apply HPQ'S; assert_cols; ColR).
          split; Col.
          split; try (intro; treat_equalities); Between.
          }
        }

        {
        assert (H3 : P <> S) by (assert_diffs; Col).
        assert (H4 : Col P S S) by Col.
        assert (H5 : Col T R S) by (unfold BetS in *; spliter; assert_cols; Col).
        assert (H := l9_19 P S T R S H3 H4 H5); rewrite H.
        unfold BetS in *; spliter; split; try (intro; apply HPQS; assert_cols; ColR).
        split; Col.
        split; try (intro; treat_equalities); Between.
        }
      }
    assert (HMid : Midpoint P R R').
      {
      split.

        {
        destruct HTS as [Hc1 [Hc2 [Hc3 [I [H1 H2]]]]].
        assert (P = I); subst; Col.
          {
          apply l6_21 with P S R R'; unfold BetS in *; spliter; assert_cols;
          try (intro; treat_equalities); Col.
          }
        }

        {
        unfold BetS in *; spliter;
        assert (Cong P R Q S) by (apply l7_13 with T; split; Between; Cong);
        assert (Cong P R' Q' S) by (apply l7_13 with T'; split; Between; Cong); eCong.
        }
      }
    assert (HRR' : R <> R') by (intro; subst; apply (not_two_sides_id R' P S); Col).
    assert (H : Coplanar P R S U); try (clear HCop; rename H into HCop).
      {
      (*
      apply coplanar_pseudo_trans with P Q R; Cop;
      try (intro; apply BetSEq in HPTQ; apply BetSEq in HRTS;
           spliter; assert_cols; apply HPQS; ColR).
      exists T; left; unfold BetS in *; spliter; assert_cols; Col.
      *)
      apply all_coplanar.
      }
    elim (coplanar_side_dec P R R' S U U'); Col; apply BetSEq in HPTQ;
    apply BetSEq in HRTS; apply BetSEq in HPT'Q'; apply BetSEq in HR'T'S;
    spliter; assert_cols;
    try (intro; apply HPQS; ColR); try (intro; apply HNC; ColR); intuition.
    }
  }
Qed.

End euclid_SPP.
