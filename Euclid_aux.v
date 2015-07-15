Require Export Euclid_aux_1.
Require Export Euclid_aux_2.
Require Export Euclid_aux_3.
Require Export Euclid_aux_4.

Section Euclid_aux.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma euclid_5_implies_strong_parallel_postulate_aux :
  euclid_5 ->
  (forall P Q R S T U : Tpoint,
   BetS P T Q ->
   BetS R T S ->
   ~ Col P R U ->
   coplanar P Q R U ->
   Cong P T Q T ->
   Cong R T S T ->
   one_side P R S U ->
   one_side P S R U ->
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
assert (HCop : coplanar P S R R') by apply all_coplanar.
(*
  {
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

End Euclid_aux.