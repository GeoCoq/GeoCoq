Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Main.Tarski_dev.Ch12_parallel.

Section midpoint_playfair.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma midpoint_converse_postulate_implies_playfair :
  midpoint_converse_postulate ->
  playfair_s_postulate.
Proof.
intros HT A1 A2 B1 B2 C1 C2 P HPar1 HCol1 HPar2 HCol2.
elim HPar1; clear HPar1; intro HPar1; elim HPar2; clear HPar2; intro HPar2.

  {
  assert (HDiff : P <> A1) by (intro; apply HPar1; exists P; subst; Col).
  assert (HX := symmetric_point_construction A1 P); destruct HX as [X HMid1].
  revert B1 B2 C1 C2 HCol1 HCol2 HPar1 HPar2.
  assert (Haux : forall B1 B2, Col P B1 B2 -> Par_strict A1 A2 B1 B2 ->
            exists B3, Col B1 B2 B3 /\ BetS A2 B3 X /\ Par_strict A1 A2 P B3).
    {
    cut (forall B1 B2, Col P B1 B2 -> Par_strict A1 A2 B1 B2 -> P <> B1 ->
            exists B3, Col B1 B2 B3 /\ BetS A2 B3 X /\ Par_strict A1 A2 P B3).
      {
      intros Haux B1 B2 HCol1 HPar1.
      elim (eq_dec_points P B1); auto.
      intro.
      assert (P <> B2) by (intro; subst; assert_diffs; auto).
      destruct (Haux B2 B1) as [B3 []]; Par; Col.
      exists B3; split; Col.
      }
    intros B1 B2 HCol1 HPar1 HPB1.
    assert_diffs.
    destruct (hilbert_s_version_of_pasch X A1 A2 B1 P) as [B3 [HCol HBet]];
    [..|repeat split; Between|].

        {
        apply coplanar_perm_22, col_cop__cop with P; Col.
        apply coplanar_perm_2, col_cop__cop with B2; Col.
        apply par__coplanar; Par.
        }

        {
        apply par_strict_not_col_2 with A1.
        apply par_strict_right_comm, par_strict_col_par_strict with B2; Col.
        }

        {
        intro; apply HPB1, l6_21 with A1 P B1 P; Col; [|ColR].
        apply par_strict_not_col_2 with A2.
        apply par_strict_comm, par_strict_col_par_strict with B2; Col.
        }

        {
        assert (Col B1 B2 B3) by ColR.
        exists B3; split; trivial.
        unfold BetS in *.
        induction HBet; spliter; [|exfalso; apply HPar1; exists B3; split; Col].
        split; [repeat split; Between|].
        apply par_strict_col2_par_strict with B1 B2; Col.
        intro; treat_equalities; apply HPar1; exists P; split; ColR.
        }
      }
  intros B1 B2 C1 C2 HCol1 HCol2 HPar1 HPar2.
  destruct (Haux B1 B2 HCol1 HPar1) as [B3 [HCol3 [HBet1 HPar3]]].
  destruct (Haux C1 C2 HCol2 HPar2) as [C3 [HCol4 [HBet2 HPar4]]].
  assert (HCol5 : Col A2 X B3) by (unfold BetS in *; spliter; Col).
  assert (HCol6 : Col A2 X C3) by (unfold BetS in *; spliter; Col).
  assert (HNC' : ~ Col A1 A2 X)
    by (intro; apply HPar1; exists P; split; ColR).
  assert (B3 = C3) by (apply l7_17 with A2 X; apply HT with A1 P; Col; Par).
  subst; split; ColR.
  }

  {
  spliter; exfalso; apply HPar1.
  exists P; split; ColR.
  }

  {
  spliter; exfalso; apply HPar2.
  exists P; split; ColR.
  }

  {
  spliter; split; ColR.
  }
Qed.

End midpoint_playfair.
