Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Main.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Main.Annexes.suma.
Require Import GeoCoq.Main.Annexes.perp_bisect.
Require Import GeoCoq.Main.Tarski_dev.Ch13_1.

Section bachmann_s_lotschnittaxiom_legendre_s_parallel_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bachmann_s_lotschnittaxiom__legendre_s_parallel_postulate :
  bachmann_s_lotschnittaxiom -> legendre_s_parallel_postulate.
Proof.
rewrite bachmann_s_lotschnittaxiom_aux.
intro bla.
cut (exists A B C, ~ Col A B C /\ Acute A B C /\ forall P Q,
          Out B A P -> P <> Q -> Per B P Q -> Coplanar A B C Q ->
          exists Y, Out B C Y /\ Col P Q Y).
  {
  clear bla.
  intros [A [B [C [HNC [HAcute HP]]]]]; exists A, B, C; repeat split; Col.
  intros T HInAngle; elim (col_dec A B T); intro HABT.

    {
    assert (HNC' : ~ Col B C T)
      by (intro; apply HNC; ColR).
    destruct (l8_18_existence B C T HNC') as [Y [HC HPerp]].
    exists T, Y.
    assert (HOut : Out B A T).
      {
      apply col_in_angle_out with C; [|intro; apply HNC|]; Col.
      }
    split; [|split]; Between.
    apply l6_6, acute_col_perp__out with T; Col.
    apply acute_conga__acute with A B C; auto.
    apply out213_suma__conga with T B A; [|Out].
    assert_diffs.
    exists C; repeat (split; try (apply conga_refl; auto)).
      apply col123__nos; Col.
      Cop.
    }

    {
    destruct (l8_18_existence A B T) as [X [HC HPerp]]; Col.
    assert (HOut1 : Out B A X).
      {
      apply l6_6, acute_col_perp__out with T; Col; Perp.
      apply acute_lea_acute with A B C; auto.
      apply lea_left_comm, l11_29_b.
      exists C; split; trivial.
      assert_diffs; apply conga_refl; auto.
      }
    destruct (HP X T) as [Y [HOut2 H]].
      assumption.
      assert_diffs; auto.
      assert_diffs; apply perp_per_1, perp_sym, perp_col0 with A B; Col.
      Cop.
    exists X, Y; repeat (split; [assumption|]).
    elim H; clear H; intro H; auto.
    elim (eq_dec_points T Y); intro HTY.
      subst; Between.
    assert (HACT : ~ Col B C T).
      {
      assert_diffs; intro; apply HTY, l6_21 with B C X T; Col.
        intro; apply HNC; ColR.
        right; assumption.
      }
    elim H; clear H; intro HBet.

      {
      assert (HOS : OS C B T A)
        by (apply in_angle_one_side; [Col..|apply l11_24, HInAngle]).
      exfalso; apply (l9_9_bis _ _ _ _ HOS).
      apply l9_2, l9_8_2 with X.

        {
        repeat split; [intro; apply HNC; ColR..|].
        exists Y; split; [Col|Between].
        }

        {
        apply l9_19 with B; Col.
        split; [Out|intro; apply HNC; ColR].
        }
      }

      {
      assert (HOS : OS A B T C) by (apply in_angle_one_side; Col).
      exfalso; apply (l9_9_bis _ _ _ _ HOS).
      apply l9_2; apply l9_8_2 with Y.

        {
        repeat split; [intro; assert_diffs; apply HNC; ColR..|].
        exists X; split; Col.
        }

        {
        apply l9_19 with B; Col.
        split; [Out|intro; apply HNC; ColR].
        }
      }
    }
  }

  {
  destruct lower_dim_ex as [C [E [D H]]].
  assert (HNC : ~ Col C E D) by auto; clear H.
  destruct (l8_18_existence D E C) as [B [HC1 HPerp]]; Col.
  assert (HF : exists F, Col D E F /\ B <> F).
    {
    assert_diffs; elim (eq_dec_points B E); intro;
    [exists D|exists E]; subst; split; Col.
    }
  destruct HF as [F [HC2 HNE]].
  destruct (segment_construction_2 F B B C) as [A [Hd HCong1]]; auto.
  assert (HC3 : Col D E A)
    by (assert (Col A B F) by (induction Hd; Col); ColR).
  clear Hd.
  assert (HPerp1 : Perp B A C B)
    by (assert_diffs; apply perp_sym, perp_col0 with D E; Perp).
  clear dependent D; clear dependent F; clear E.
  assert (HNC := perp_not_col _ _ _ HPerp1).
  destruct (midpoint_existence A C) as [D HD].
  exists A, B, D.
  split; [intro; apply HNC; ColR|split].

    {
    assert_diffs.
    assert (D <> B) by (intro; subst; apply HNC; Col).
    exists A, B, C; split; [Perp|split].

      {
      exists D; split; [repeat split|apply conga_refl]; auto.
      exists D; split; [Between|right; Out].
      }

      {
      intro HCongA.
      assert (HPer1 : Per A B D).
        {
        apply l11_17 with A B C; [Perp|CongA].
        }
      assert (HPer2 : Per C B D).
        {
        apply l11_17 with A B D; trivial.
        apply cong3_conga; auto.
        repeat split; Cong.
        }
      assert (HSumA : SumA A B D C B D A B C).
        {
        exists C; repeat (split; CongA); [|Cop].
        apply l9_9.
        repeat split; [apply per_not_col; auto..|].
        exists D; split; [Col|Between].
        }
      assert (HC := per2_suma__bet _ _ _ _ _ _ _ _ _ HPer1 HPer2 HSumA).
      apply HNC; Col.
      }
    }

    {
    intros P Q HOut1 HNE1 HPer HCop1.
    destruct (l6_11_existence B B P C) as [P' [HOut2 HCong2]]; [assert_diffs; auto..|].
    destruct (ex_perp_cop B C P' A) as [Q' [HPerp2 HCop2]]; [assert_diffs; auto|].
    assert (HPerp3 : Perp B A Q P).
      {
      assert_diffs.
      apply l8_16_2 with B; Col; Perp.
      apply per_not_col in HPer; auto.
      intro; apply HPer; ColR.
      }
    assert (Coplanar B Q A C)
      by (assert_diffs; apply col2_cop__cop with A D; Col; Cop).
    assert (B <> P') by (destruct HOut2; auto).
    assert (B <> P) by (intro; treat_equalities; auto).
    destruct (bla B A B C P Q P' Q' B P P') as [I [HC1 HC2]]; Col; Perp; [CopR..|].
    assert (HNE2 : B <> D)
      by (intro; treat_equalities; apply HNC; Col).
    assert (HOS : OS B C P I).
      {
      apply l12_6; apply par_strict_col_par_strict with Q; Col.

        {
        intro; treat_equalities; apply (perp_not_col _ _ _ HPerp1).
        destruct (not_strict_par A B P' Q' P) as [HC3 HC4]; [|ColR..].
        apply l12_9 with B C; Perp; Cop.
        }

        {
        apply par_not_col_strict with P; [apply l12_9 with A B|..]; Perp; Col; Cop.
        intro; apply HNC; ColR.
        }
      }
    exists I; split; Col; apply l6_4_2; split.

      {
      elim (eq_dec_points D I); intro HNE3; [treat_equalities; Col|].
      assert (Coplanar A B C I) by (apply col_cop2__cop with P Q; Cop).
      assert_diffs.
      apply cop_perp2__col with A C;
      [Cop|apply perp_bisect_perp, perp_bisect_sym_1, cong_mid_perp_bisect; Cong..].
      assert (HPerp4 : Perp P I B P).
        {
        apply perp_col0 with A B; [apply perp_col0 with P Q|..]; Col; Perp.
        intro; treat_equalities; apply HNC.
        assert (HPar : Par B A P' Q') by (apply l12_9 with B C; Perp; Cop).
        destruct (not_strict_par B A P' Q' P); ColR.
        }
      assert (HPerp5 : Perp P' I B P').
        {
        apply perp_col0 with B C; [apply perp_col0 with P' Q'|..]; Col; Perp.
        intro; treat_equalities; apply HNC.
        assert (HPar : Par B C P Q) by (apply l12_9 with B A; Perp; Cop).
        destruct (not_strict_par B C P Q P'); ColR.
        }
      assert_diffs.
      destruct (per_lt B P I) as [HLt _]; [Perp..|].
      destruct (l11_52 I P B I P' B) as [_ [_ HCongA2]]; Cong; Le.
        apply l11_16; Perp.
      apply cong2_conga_cong with B B; Cong.
      apply l11_10 with P I P' I; Out.
      }

      {
      intro; apply (l9_9_bis _ _ _ _ HOS).
      assert (~ Col B C D) by (intro; apply HNC; ColR).
      apply l9_8_2 with D; try apply one_side_transitivity with A.

        {
        apply one_side_symmetry in HOS; apply one_side_not_col123 in HOS.
        repeat split; [..|exists B; split]; Col.
        }

        {
        assert_diffs.
        apply l9_19 with C; Col; split; Out.
        }

        {
        apply l9_19 with B; Col.
        }
      }
    }
  }
Qed.

End bachmann_s_lotschnittaxiom_legendre_s_parallel_postulate.
