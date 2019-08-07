Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section alternate_interior_angles_proclus.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma alternate_interior__proclus_aux :
  greenberg_s_axiom ->
  alternate_interior_angles_postulate -> forall A C D P Q,
  Par_strict P A C D -> Perp C D P C -> OS P A C Q -> OS P C Q A -> OS P C Q D ->
  exists Y, Col P Q Y /\ Col C D Y.
Proof.
  intros greenberg aia.
  intros A C D P Q HParS HPerp HOS1 HOS2 HOS3.
  destruct (symmetric_point_construction D C) as [D' []].
  assert_diffs.
  assert (~ Col P A Q) by (apply one_side_not_col124 with C, HOS1).
  assert (~ Col P C Q) by (apply one_side_not_col123 with D, HOS3).
  assert (~ Col P C D) by (apply one_side_not_col124 with Q, HOS3).
  assert (LtA A P Q A P C) by (apply inangle__lta; [Col|Side]).
  assert (OS P C D A) by (apply one_side_transitivity with Q; Side).
  assert (Acute A P Q).
  { exists A, P, C; split; auto.
    apply (l11_17 P C D').
      apply per_col with D; Col; Perp.
    apply conga_sym, conga_right_comm, aia; [|apply par_col_par with D; Par; Col].
    apply l9_8_2 with D; trivial.
    apply invert_two_sides, bet__ts; Col.
  }
  destruct (greenberg P C D A P Q) as [S [HS1 HS2]]; Perp; Col.
  assert (OS P C S D) by (apply invert_one_side, out_one_side; Col).
  assert (HY : InAngle Q C P S).
  { apply os2__inangle.
      apply one_side_transitivity with D; Side.
    exists A.
    assert (OS P C S A).
      apply one_side_transitivity with D; Side.
    assert (Par_strict P A S C).
    { apply lta_distincts in HS1; spliter.
      apply par_strict_right_comm, par_strict_col_par_strict with D; Col.
    }
    assert (HTS : TS P S C A) by (apply l9_31; Side).
    split; trivial.
    assert (CongA A P S C S P) by (apply aia; [Side|Par]).
    assert (HLta : LtA A P S A P Q) by (apply (conga_preserves_lta P S C A P Q); CongA).
    destruct HLta as [HLea HNConga].
    apply invert_two_sides, in_angle_two_sides; [|destruct HTS as [_ []]; Col|].
    { intro.
      assert (Out P Q S).
        apply col_one_side_out with C; [|apply one_side_transitivity with A]; Side.
      apply HNConga, out2__conga; Out.
    }
    apply l11_24, lea_in_angle; trivial.
    apply one_side_transitivity with C; Side.
  }
  clear dependent A.
  destruct HY as [_ [_ [_ [Y [HY1 HY2]]]]].
  exists Y; split; [|ColR].
  destruct HY2; [subst|]; Col.
Qed.

Lemma alternate_interior__proclus :
  greenberg_s_axiom ->
  alternate_interior_angles_postulate ->
  proclus_postulate.
Proof.
  intros greenberg aia.
  intros A B C D P Q HPar HP HQ HCop.
  elim(col_dec C D P).
    intro HConf; exists P; split; Col.
  intro HStrict.
  assert(HParS : Par_strict A B C D).
  { apply par_strict_symmetry, par_not_col_strict with P; auto.
    apply par_symmetry, HPar.
  }
  destruct (l8_18_existence C D P) as [C0 []]; auto.
  destruct (col_dec P Q C0) as [|HNCol1].
    exists C0; split; auto.
  assert_diffs.
  assert(HQ1 : exists Q1, Col Q P Q1 /\ OS A B C0 Q1).
  { apply cop_not_par_same_side with P; Col.
      apply not_col_permutation_1, (par_not_col C D); Col; Par.
    apply coplanar_pseudo_trans with C D P; trivial; apply coplanar_perm_1;
      [apply col_cop__cop with B|apply col_cop__cop with A; Col|]; Cop.
  }
  destruct HQ1 as [Q1 [HCol1 HOS1]].
  assert(P<>Q1) by (intro; subst; apply one_side_not_col124 in HOS1; apply HOS1, HP).
  assert(~ Col P C0 Q1) by (intro; apply HNCol1; ColR).
  assert(HA1 : exists A1, Col A B A1 /\ OS P C0 Q1 A1).
  { destruct (col_dec P C0 A).
    - destruct (cop_not_par_same_side P C0 B A P Q1) as [A1 []]; Col.
        intro; apply HParS; exists C0; split; ColR.
       apply coplanar_perm_19, col_cop__cop with A; Col; Cop.
      exists A1; split; Col.
    - apply (cop_not_par_same_side _ _ _ _ P); Col.
      apply coplanar_perm_19, col_cop__cop with B; Cop.
  }
  destruct HA1 as [A1 []].
  assert(HC1 : exists C1, Col C D C1 /\ OS P C0 Q1 C1).
  { assert (Coplanar C D P Q1) by (apply col_cop__cop with Q; Col).
    destruct (perp_not_col2 P C0 C D); Perp.
      apply (cop_not_par_same_side _ _ _ _ C0); Col.
      apply coplanar_perm_5, col_cop__cop with D; Cop.
    destruct (cop_not_par_same_side P C0 D C C0 Q1) as [C1 []]; Col.
      apply coplanar_perm_5, col_cop__cop with C; Col; Cop.
    exists C1; split; Col.
  }
  destruct HC1 as [C1 []].
  assert_diffs.
  destruct (alternate_interior__proclus_aux greenberg aia A1 C0 C1 P Q1) as [Y []]; auto.
    apply (par_strict_col4__par_strict A B C D); auto.
    apply (perp_col2 C D); auto.
    apply (col2_os__os A B); auto.
  clear dependent A.
  exists Y; split; ColR.
Qed.

End alternate_interior_angles_proclus.