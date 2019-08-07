Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section posidonius_postulate_rah.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma posidonius_postulate__rah : posidonius_postulate -> postulate_of_right_saccheri_quadrilaterals.
Proof.
intro H.
assert (HF : exists A1 A2 B1 B2,
             Per A2 A1 B1 /\ Per A1 A2 B2 /\
             Cong A1 B1 A2 B2 /\ OS A1 A2 B1 B2 /\
             forall A3 B3,
               Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
               Cong A3 B3 A1 B1).
  {
  destruct H as [A1' [A2' [B1 [B2 [HNC [HNE [HCop HF]]]]]]].
  destruct (l8_18_existence _ _ _ HNC) as [A1 [HC1 HPerp1]].
  assert_diffs.
  assert (HPar : Par_strict A1' A2' B1 B2).
    {
    split; trivial.
    intros [I [HI1 HI2]].
    assert (HNE' : B1 <> I) by (intro; subst; apply HNC; Col).
    destruct (midpoint_existence B1 I) as [B3 HB3].
    assert (HNE'' : B1 <> B3) by (apply midpoint_distinct_1 in HB3; spliter; auto).
    destruct (l8_18_existence A1' A2' B3) as [A3 [HC4 HPerp3]].
      intro; apply HNC; ColR.
    assert (HCong : Cong A1 B1 A3 B3)
      by (apply HF; Perp; ColR).
    assert (HCong' : Cong B1 I B3 I).
      {
      assert (HNE''' : A3 <> I).
        {
        intro; assert (A1 = A3); treat_equalities.
          {
          apply l8_18_uniqueness with A1' A2' B1; Col.
          apply perp_col0 with A3 B3; Col; Perp.
          }
        assert (HFalse : B3 <> B1) by auto.
        apply HFalse, between_cong with A1; [Between|Cong].
        }
      assert (HNE'''' : B3 <> I).
        {
        apply midpoint_distinct_1 with B1; auto.
        }
      assert (HNE''''' : A1 <> I).
        {
        intro; treat_equalities; apply HNE'''.
        apply l8_18_uniqueness with A1' A2' B3; Col; Perp.
          intro; apply HNC; ColR.
        apply perp_col2_bis with B1 A1; Col.
        }
      destruct (l11_50_2 B1 A1 I B3 A3 I); Cong.

        {
        intro H.
        apply HNE'''.
        apply perp_sym in HPerp1.
        destruct (perp_not_col2 _ _ _ _ HPerp1);
        [apply l6_21 with A1 B1 A1' A2'|apply l6_21 with A1 B1 A2' A1']; ColR.
        }

        {
        apply out2__conga; [|Out].
        repeat split; auto.
        left; apply col_two_sides_bet with B3; [ColR|].
        assert (~ Col A3 B3 B1) by (intro; apply HNE'''; apply l6_21 with A1' A2' B1 B3; Col).
        apply l9_2, l9_8_2 with B1.

          {
          apply invert_two_sides, bet__ts; Between; Col.
          }

          {
          apply l12_6; apply par_not_col_strict with B1; Col.
          apply l12_9 with A1' A2'; Perp; Cop.
          exists I; left; split; Col.
          }
        }

        {
        assert_diffs; apply l11_16; auto;
        apply perp_per_1, perp_col0 with A1' A2'; Perp; Col.
        }
      }
    assert (HFalse : B3 <> B1) by auto.
    apply HFalse, between_cong with I; Between; Cong.
    }
  destruct (l8_18_existence A1' A2' B2) as [A2 [HC2 HPerp2]].
    apply par_strict_not_col_4 with B1, HPar.
  assert (HNE' : A1 <> A2).
    {
    intro; treat_equalities.
    apply HPar; exists A1; split; Col.
    apply cop_perp2__col with A1' A2'; Perp.
    }
  apply perp_right_comm in HPerp1.
  apply perp_right_comm in HPerp2.
  exists A1, A2, B1, B2.
  repeat split; [apply l8_2, perp_per_2, perp_col0 with A1' A2'; auto..|apply HF; Col| |].
    apply (col2_os__os A1' A2'); Side.
  intros A3 B3 HC4 HC5 HPerp3.
  apply HF; Col; [ColR|].
  apply perp_col2 with A1 A2; auto; ColR.
  }
destruct HF as [A [D [B [C [HPer1 [HPer2 [HCong [HOS posid]]]]]]]].
assert (HSac : Saccheri A B C D) by (repeat split; Perp; Cong).
apply (per_sac__rah A B C D); auto.
destruct (midpoint_existence B C) as [M HM].
destruct (midpoint_existence A D) as [N HN].
assert(HPerp := mid2_sac__perp_lower A B C D M N HSac HM HN).
assert_diffs.
assert(Hdiff := sac_distincts A B C D HSac).
spliter.
assert_diffs.
apply (t22_7__per _ _ _ D M N); Between.
  apply perp_per_1, (perp_col1 _ _ _ D); Col; Perp.
apply cong_left_commutativity, posid; Col; Perp.
Qed.

End posidonius_postulate_rah.