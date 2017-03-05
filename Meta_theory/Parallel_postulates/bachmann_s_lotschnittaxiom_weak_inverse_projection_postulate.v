Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section bachmann_s_lotschnittaxiom_weak_inverse_projection_postulate.

Context `{T2D:Tarski_2D}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma bachmann_s_lotschnittaxiom__weak_inverse_projection_postulate :
  bachmann_s_lotschnittaxiom -> weak_inverse_projection_postulate.
Proof.
intro lotschnitt.
cut (forall A1 A2 B1 B2 C1 C2 D1 D2,
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        ~ Col A1 A2 D1 -> ~ Col B1 B2 C1 ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).

  {
  clear lotschnitt; intro lotschnitt.
  intros A B C D E F P Q HAcute HPer HSuma HOut HPQ HPerP.
  suma.assert_diffs.
  assert (HNCol : ~ Col A B C).
  { intro HCol.
    apply (per_not_col D E F); auto.
    apply (col2_suma__col A B C A B C); assumption.
  }
  assert (HNCol1 : ~ Col B C P) by (intro; apply HNCol; ColR).
  destruct (l10_6_existence_spec B C P) as [P' HP']; trivial.
  assert (HP'1 : Reflect P P' B C) by (apply is_image_is_image_spec; auto).
  assert (HNCol2 : ~ Col B C P') by (apply osym_not_col with P; trivial).
  destruct (l10_6_existence_spec B C Q) as [Q' HQ']; trivial.
  assert (HQ'1 : Reflect Q Q' B C) by (apply is_image_is_image_spec; auto).
  assert_diffs.
  assert (P' <> Q').
   intro; subst Q'; assert (P = Q) by (apply (l10_2_uniqueness B C P'); assumption); auto.
  apply l6_6 in HOut.
  assert (HCongA : CongA C B P' A B C).
    apply out_conga with C P' P C; try (apply out_trivial); auto.
    apply conga_sym, conga_left_comm, reflectl__conga; auto.
    apply is_image_spec_rev, HP'.
  assert (HTS : TS B C P P').
    repeat split; Col; destruct HP' as [[X [HX1 HX2]] _]; exists X; split; Col; Between.
  assert (HPer1 : Per A B P').
  { apply l11_17 with D E F; trivial.
    apply (suma2__conga A B C A B C); trivial.
    apply conga3_suma__suma with A B C C B P' A B P'; CongA.
    exists P'; assert_diffs; repeat (split; CongA).
    apply l9_9, l9_5 with P B; Col.
  }
  assert (HNCol3 : ~ Col A B P') by (apply per_not_col; auto).
  assert (HNCol4 : ~ Col B P' P) by (intro; apply HNCol3; ColR).
  assert (HPerp1 : Perp A B B P') by (apply per_perp; auto).
  assert (HPerp2 : Perp A B P Q) by (apply perp_left_comm, perp_col with P; Col; apply per_perp; auto).
  assert (HPerp3 : Perp B P' P' Q').
    apply per_perp; auto; apply image_preserves_per with B P Q B C; trivial; apply col__refl; Col.
  assert (HNCol5 : ~ Col P Q P').
    apply par_strict_not_col with B P'; Col.
    apply par_not_col_strict with P; Col.
    apply l12_9 with A B; Perp.
  destruct (lotschnitt A B B P' P Q P' Q') as [Y [HY1 HY2]]; trivial.
  exists Y; split; trivial.
  apply col_one_side_out with A.
    apply col_permutation_1, intersection_with_image_gen with P Q P' Q'; trivial.
  apply invert_one_side, one_side_transitivity with P'.
    apply not_two_sides_one_side; Col.
    apply (conga_isi_nos__nts A B C A B C P'); SumA.
    apply l9_9, l9_5 with P B; Col.
  apply l12_6, par_strict_col_par_strict with Q'; trivial.
    intro; subst; apply HNCol5, HY1.
  apply par_not_col_strict with P'; Col.
  apply l12_9 with B P'; Perp.
  }

  {
  intros A1 A2 B1 B2 C1 C2 D1 D2 HPerpAB HPerpAC HPerpBD HNCol1 HNCol2.
  assert (HParA : Par_strict A1 A2 D1 D2).
    apply par_not_col_strict with D1; Col; apply l12_9 with B1 B2; Perp.
  assert (HParB : Par_strict B1 B2 C1 C2).
    apply par_not_col_strict with C1; Col; apply l12_9 with A1 A2; Perp.
  assert (HP := HPerpAC); destruct HP as [P [_ [_ [HP1 [HP2 HP3]]]]].
  assert (HQ := HPerpAB); destruct HQ as [Q [_ [_ [HQ1 [HQ2 HQ3]]]]].
  assert (HR := HPerpBD); destruct HR as [R [_ [_ [HR1 [HR2 HR3]]]]].
  assert (HNCol3 : ~ Col P B1 B2) by (apply par_not_col with C1 C2; Par).
  assert (HNCol4 : ~ Col R A1 A2) by (apply par_not_col with D1 D2; Par).
  assert (HPQ : P <> Q) by (intro; subst; contradiction).
  assert (HQR : Q <> R) by (intro; subst; contradiction).
  assert (Per P Q R) by (apply HQ3; trivial).
  destruct (diff_col_ex3 C1 C2 P) as [P1 [HC1P1 [HC2P1 [HPP1 HCP1]]]]; Col.
  destruct (diff_col_ex3 D1 D2 R) as [R1 [HD1R1 [HD2R1 [HRR1 HDR1]]]]; Col.
  destruct (lotschnitt P Q R P1 R1) as [I [HI1 HI2]]; auto.
    apply HP3; Col.
    apply HR3; Col.
  exists I.
  split; assert_diffs; ColR.
  }
Qed.

End bachmann_s_lotschnittaxiom_weak_inverse_projection_postulate.