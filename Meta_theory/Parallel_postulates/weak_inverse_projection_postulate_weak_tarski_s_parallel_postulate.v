Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section weak_inverse_projection_postulate_weak_tarski_s_parallel_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma weak_inverse_projection_postulate__weak_tarski_s_parallel_postulate :
  weak_inverse_projection_postulate -> weak_tarski_s_parallel_postulate.
Proof.
intro wipp.
cut (forall A B C P T,
       Per A B C -> InAngle T A B C ->
       P <> T -> CongA P B A P B C -> Per B P T -> Coplanar A B C P ->
       exists X Y, Out B A X /\ Col T P X /\ Out B C Y /\ Col T P Y).

  {
  intros rabp A B C T HPer HInAngle.
  assert_diffs.
  destruct (angle_bisector A B C) as [P0 [HIn HConga]]; auto.
  assert_diffs.
  assert (HNCol1 : ~ Col A B C) by (apply per_not_col; auto).
  assert (HNCol2 : ~ Col P0 B A).
  { assert (SumA P0 B A P0 B A A B C) by (apply (conga3_suma__suma A B P0 P0 B C A B C); CongA; SumA).
    intro; apply HNCol1, (col2_suma__col P0 B A P0 B A); assumption.
  }
  assert (HXY : exists X Y, Out B A X /\ Out B C Y /\ Col X T Y).
  { destruct (col_dec B P0 T).
    - assert (HT' : exists T', InAngle T' A B C /\ Perp B T T T').
      { destruct (l10_15 B P0 T A) as [T0 [HPerp HOS]]; Col.
        destruct (cop_inangle__ex_col_inangle A B C T T0) as [T' [HT1 [HT2 HT3]]]; trivial.
            intro; apply HNCol1; Col.
            CopR.
        exists T'; split; trivial.
        assert_diffs.
        apply perp_col with P0; Col.
        apply perp_col1 with T0; Perp.
      }
      destruct HT' as [T' []].
      assert_diffs.
      destruct (rabp A B C T T') as [X [Y]]; Perp; Cop.
        apply col_conga__conga with P0; auto.
      spliter; exists X, Y; repeat (split; [assumption|]); ColR.
    - destruct (l8_18_existence B P0 T) as [P [HP1 HP2]]; trivial.
      assert (Out B P P0).
        apply (acute_col_perp__out T); trivial.
        apply acute_sym, conga_inangle2_per__acute with A C; trivial.
      assert_diffs.
      destruct (rabp A B C P T) as [X [Y]]; auto.
        apply col_conga__conga with P0; auto.
        apply perp_per_1, perp_left_comm, perp_col with P0; auto.
        CopR.
      spliter; exists X, Y; repeat (split; [assumption|]); ColR.
  }
  destruct HXY as [X [Y [HOutX [HOutY HCol]]]].
  assert_diffs.
  assert (HNCol3 : ~ Col A B Y) by (intro; apply HNCol1; ColR).
  assert (X <> Y) by (intro; subst; apply HNCol3; Col).
  exists X, Y; repeat (split; [assumption|]).
  destruct (eq_dec_points T X) as [|HTX]; [subst; Between|].
  destruct (eq_dec_points T Y) as [|HTY]; [subst; Between|].
  apply out2__bet.
  - apply col_one_side_out with B; trivial.
    apply invert_one_side, col_one_side with A; Col.
    apply out_out_one_side with C; trivial.
    apply invert_one_side, in_angle_one_side; Col.
    intro; apply HTX, (l6_21 A B Y X); Col.
  - apply col_one_side_out with B; Col.
    apply invert_one_side, col_one_side with C; Col.
    apply one_side_symmetry, out_out_one_side with A; trivial.
    apply invert_one_side, in_angle_one_side; [Col| |apply l11_24, HInAngle].
    intro; apply HTY, (l6_21 B C X Y); Col.
    intro; apply HNCol1; ColR.
  }

  {
  intros A B C P T HPer HInangle HPT HConga HPerP HCop.
  assert_diffs.
  assert (HIn : InAngle P A B C) by (apply conga_cop_inangle_per2__inangle with T; assumption).
  assert (HSumA : SumA P B A P B A A B C).
    apply (conga3_suma__suma A B P P B C A B C); CongA; SumA.
  assert (HAcute : Acute P B A) by (apply acute_sym, conga_inangle_per__acute with C; assumption).
  assert (HOut : Out B P P) by (apply out_trivial; auto).
  assert (~ Col A B C) by (apply per_not_col; auto).
  destruct (wipp P B A A B C P T) as [X [HX1 HX2]]; trivial; [CopR|].
  destruct (wipp P B C C B A P T) as [Y [HY1 HY2]]; Perp.
    apply (acute_conga__acute P B A); assumption.
    apply (conga3_suma__suma P B A P B A A B C); CongA.
    CopR.
  exists X, Y; repeat (split; Col).
  }
Qed.

End weak_inverse_projection_postulate_weak_tarski_s_parallel_postulate.