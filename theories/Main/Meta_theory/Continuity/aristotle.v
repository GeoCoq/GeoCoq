Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Main.Annexes.saccheri.

Section Aristotle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma aristotle__greenberg : aristotle_s_axiom -> greenberg_s_axiom.
Proof.
  intros aristotle P Q R A B C.
  intros HNColB HABCacute HQRdiff HQright.
  elim (eq_dec_points P Q); intro HPQdiff.
  { treat_equalities.
    assert_diffs.
    exists R.
    split; [|apply out_trivial; auto].
    split.
    apply lea121345; auto.
    intro.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (eq_conga_out P R); auto.
  }
  assert (HXY : (exists X Y, Out B A X /\ Out B C Y /\ Per B X Y /\ Lt P Q X Y)) by (apply aristotle; assumption).
  destruct HXY as [X [Y [PX [PY [HXright [Hle HNcong]]]]]].
  assert_diffs.
  assert (HXYdiff : X <> Y) by (intro; treat_equalities; auto).
  assert (HT : (exists T, Out Q T P /\ Cong Q T X Y)) by (apply l6_11_existence; auto).
  destruct HT as [T []].
  assert (HS : (exists S, Out Q S R /\ Cong Q S X B)) by (apply l6_11_existence; auto).
  destruct HS as [S []].
  assert_diffs.
  exists S.
  split; auto.
  assert (Per S Q P) by (apply (l8_3 R); Perp; Col).
  assert (Per T Q S) by (apply (l8_3 P); Perp; Col).
  assert (P<>S).
  { intro; treat_equalities.
    assert (P=Q) by (apply l8_8; auto); treat_equalities; absurde.
  }
  assert (T<>S).
  { intro; treat_equalities.
    assert (T=Q) by (apply l8_8; auto); treat_equalities; absurde.
  }
  apply conga_preserves_lta with P S Q T S Q; try (apply conga_refl; auto); [|split].
  - apply conga_trans with X B Y; [|apply out2__conga; auto].
    assert (HInter : (Cong T S Y B /\ (T <> S -> CongA Q T S X Y B /\ CongA Q S T X B Y))).
    { apply (l11_49 T Q S Y X B); Cong.
      apply l11_16; Perp.
    }
    destruct HInter as [_ [_ HConga]]; auto.
    apply conga_left_comm; auto.

  - apply lea_comm.
    apply (l11_29_b Q S P Q S T).
    exists T.
    split; CongA.
    repeat split; auto.
    exists P.
    split; [|right; apply out_trivial; auto].
    apply l6_13_1.
    apply l6_6; auto.
    apply (le_transitivity Q P X Y).
    apply (le_transitivity Q P P Q); Le.
    apply (cong__le); Cong.

  - intro HConga.
    assert (HInter : Cong Q P Q T /\ Cong S P S T /\ CongA Q P S Q T S).
    { apply l11_50_1; Cong.
      { intro.
        assert (HUn : S=Q\/P=Q) by (apply l8_9; Col).
        destruct HUn; treat_equalities; absurde.
      }
      apply l11_16; Perp.
      CongA.
    }
    destruct HInter as [HCong _].
    apply HNcong.
    apply (cong_transitivity P Q T Q); Cong.
Qed.


(** This proof is inspired by The elementary Archimedean axiom in absolute geometry, by Victor Pambuccian *)

Lemma greenberg__aristotle : greenberg_s_axiom -> aristotle_s_axiom.
Proof.
intros HG P Q A B C HNC HAcute.
destruct (l10_15 A B B C) as [D' [HPerp1 HOS1]]; Col.
elim (eq_dec_points P Q); intro HPQ; treat_equalities.

  {
  destruct (l8_18_existence A B C) as [X [HCol HPerp]]; Col; exists X, C.
  split; [apply l6_6, acute_col_perp__out with C; try apply acute_sym; finish|].
  split; [apply out_trivial; assert_diffs; auto|].
  split; [|apply lt1123; assert_diffs; auto].
  elim (eq_dec_points X B); intro HBX; treat_equalities; Perp.
  apply perp_per_1, perp_col2 with A B; Col.
  }

  {
  destruct (segment_construction_3 B D' P Q) as [P' [HOut1 HCong1]];
  try solve [assert_diffs; auto].
  destruct (HG P' B A A B C) as [C' HC']; Col; try solve [assert_diffs; auto];
  [apply perp_per_2,  perp_col2 with D' B; finish; assert_diffs; auto|].
  destruct HC' as [HLtA HOut2].
  destruct (l10_15 B C' C' C) as [D'' [HPerp2 HOS2]]; Col;
  try (intro H; apply HNC; assert_diffs; assert_cols; ColR).
  destruct (segment_construction_3 C' D'' P Q) as [P'' [HOut3 HCong2]];
  try solve [assert_diffs; auto].
  destruct (segment_construction_3 B C B P'') as [Z [HOut4 HCong3]];
  try (intro; treat_equalities; assert_cols; Col);
  [elim (perp_not_col2 _ _ _ _ HPerp2); intro HF; apply HF; Col|].
  destruct (l8_18_existence A B Z) as [Z' [HCol HPerp3]];
  [intro; apply HNC; ColR|]; assert (HOut5 : Out B Z' A).
    {
      apply acute_col_perp__out with Z; finish.
      apply acute_sym, acute_out2__acute with A C; finish.
      apply out_trivial; assert_diffs; auto.
    }
  exists Z', Z; do 2 (split; finish); split;
  [apply perp_per_1, perp_col2 with A B; assert_diffs; Col|].
  apply cong2_lt__lt with C' P'' Z' Z; Cong.
  apply cong_lt_per2__lt_1 with B B; Cong; try (apply perp_per_1);
  [apply perp_col2 with A B|apply perp_col2_bis with C' D''|];
  try solve [assert_diffs; Col; Perp].
  assert (HCongA : CongA B C' P' A B P'').
    {
    apply l11_10 with B P' C' P''; try solve [assert_diffs; finish].
    apply l11_49; try solve [assert_diffs; finish]; eCong.
    apply l11_16; try solve [assert_diffs; auto]; apply perp_per_1;
    [apply perp_col2 with B D'|apply perp_col2 with C' D''];
    assert_diffs; finish; apply perp_sym; apply perp_col2 with B A; finish.
    }
  assert (HT : InAngle P'' Z' B Z).
    {
    apply l11_25 with P'' A C; finish; [|apply out_trivial; intro];
    [|treat_equalities; elim (perp_not_col2 _ _ _ _ HPerp3); Col].
    apply lea_in_angle.

      {
      apply l11_30 with B C' P' A B C; finish;
      apply conga_refl; assert_diffs; auto.
      }

      {
      apply one_side_transitivity with D''.
      apply col2_os__os with B C'; assert_diffs; finish.
      apply out_one_side_1 with C'; finish.
      elim (perp_not_col2 _ _ _ _ HPerp2); intro HF; Col.
      intro; apply HF; ColR.
      }
    }
  destruct HT as [_ [_ [_ [T [HBet1 [?|HOut6]]]]]]; treat_equalities;
  [exfalso; apply HNC; ColR|destruct HOut6 as [_ [_ HOut6]]].
  assert (HPar : Par Z Z' C' P'').
    {
    apply l12_9 with B C'; Cop; [|apply col__coplanar; ColR|apply perp_sym|];
    [|apply perp_col2 with A B; assert_diffs; finish|
    apply perp_col2 with C' D''; assert_diffs; finish].
    assert (Coplanar B Z C  C') by (apply col__coplanar; ColR).
    assert (Coplanar C' P'' D'' B) by (apply col__coplanar; ColR).
    assert (Coplanar C' B D'' C); [Cop|CopR].
    }
  assert (HTZ : T <> Z).
    {
    intro; treat_equalities; destruct HLtA as [_ HF]; apply HF.
    apply conga_trans with A B P''; finish.
    apply conga_sym, out2__conga; [assert_diffs; finish|].
    apply l6_7 with T; finish.
    assert_diffs; split; auto; split; auto.
    induction HOut6; auto.
    }
  assert (HTZ' : T <> Z').
    {
    intro; treat_equalities; elim (perp_not_col2 _ _ _ _ HPerp2); Col.
    intro HF; apply HF; induction HOut6; ColR.
    }
  assert (HTP'' : T <> P'').
    {
    intro; treat_equalities; assert (HF : Acute B T Z).
      {
      apply cong__acute; try solve [assert_diffs; finish].
      }
    apply (acute__not_obtuse _ _ _ HF).
    apply acute_suppa__obtuse with B T Z';
    try (apply suppa_left_comm, bet__suppa); try solve [assert_diffs; finish].
    apply acute_sym, l11_43; try solve [assert_diffs; auto]; left.
    apply perp_per_1; apply perp_col2 with A B; Col; [|assert_diffs; auto].
    apply perp_sym, perp_col2 with Z Z'; finish.
    }
  assert (HBet2 : Bet B T P''); [|clear HOut6].
    {
    elim HOut6; [auto|clear HOut6; intro HF; exfalso].
    assert (HObtuse : Obtuse Z T B).
      {
      apply acute_suppa__obtuse with B T Z';
      try (apply suppa_left_comm, suppa_right_comm);
      try (apply bet__suppa); try solve [assert_diffs; finish].
      apply acute_sym, l11_43; try solve [assert_diffs; auto]; left.
      apply perp_per_1; apply perp_col2 with A B; Col; [|assert_diffs; auto].
    apply perp_sym, perp_col2 with Z Z'; finish.
      }
    apply (not_and_lta B Z T B T Z); split.

      {
      apply acute_obtuse__lta; [|apply obtuse_sym; auto].
      apply acute_sym, l11_43; assert_diffs; finish.
      right; apply obtuse_sym; auto.
      }

      {
      apply l11_44_2_a; [intro; apply HNC; ColR|].
      apply le1234_lt__lt with B P''; [apply cong__le; finish|].
      apply bet__lt1213; assert_diffs; finish.
      }
    }
  apply par_symmetry in HPar; apply (par_not_col_strict _ _ _ _ T) in HPar; Col;
  [|intro; apply HTP'', l6_21 with C' P'' B T; Col;
    [|intro; treat_equalities; apply HNC; ColR];
    elim (perp_not_col2 _ _ _ _ HPerp2); Col;
    intros HF ?; apply HF; ColR].
  assert (HOS3 := pars__os3412 _ _ _ _ HPar).
  assert (HOut6 : Out P'' T B) by (split; [auto|split; assert_diffs; finish]).
  assert (HOut7 : Out B C' Z') by (apply l6_7 with A; finish).
  destruct HOut7 as [_ [_ [HBet3|HBet3]]];
  [|apply bet__lt1213; Between;
    intro; treat_equalities; apply par_strict_not_col_1 in HPar; Col;
    apply one_side_not_col123 in HOS3; Col].
  exfalso; apply (l9_9_bis _ _ _ _ HOS3), l9_8_2 with B.

    {
    split; [intro; apply HNC; ColR|].
    split; [intro; apply HNC; ColR|].
    exists T; split; finish.
    }

    {
    apply out_one_side_1 with Z'; finish; [intro; apply HNC; ColR|].
    assert_diffs; do 2 (split; auto); right; finish.
    }
  }
Qed.


(** This proof is inspired by Several topics from geometry, by Franz Rothe *)

Lemma aristotle__obtuse_case_elimination :
  aristotle_s_axiom ->
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros aristotle obtuse.
  destruct ex_lambert as [Q' [C' [P [Q HLam]]]].
  assert (HObtuse : Obtuse C' P Q) by (apply <- (lam_obtuse__oah Q'); trivial).
  assert (HPar : Par_strict Q' Q C' P) by (apply lam__pars1423, HLam).
  destruct HLam; spliter.
  destruct (l10_15 P Q P C') as [A' [HPerp HOS]]; Col.
    apply not_col_permutation_1.
    apply par_strict_not_col_1 with Q'; Par.
  assert_diffs.
  assert (HLtA : LtA Q P A' C' P Q) by (apply obtuse_per__lta; Perp).
  destruct HLtA as [HLeA HNCongA].
  assert (HInAngle : InAngle A' Q P C').
    apply lea_in_angle; Side; apply lea_right_comm; trivial.
  destruct (segment_construction C' P C' P) as [C [HC1 HC2]].
  destruct (segment_construction A' P A' P) as [A [HA1 HA2]].
  assert_diffs.
  assert (HInAngle1 : InAngle C A P Q).
    apply in_angle_reverse with A'; auto.
    apply l11_24, in_angle_reverse with C'; auto.
    apply l11_24; trivial.
  assert (HNCol : ~ Col P C' A').
  { intro Habs.
    apply HNCongA, conga_right_comm, out2__conga.
      apply out_trivial; auto.
    apply col_one_side_out with Q; trivial.
  }
  assert (HNCol1 : ~ Col P C A) by (intro; apply HNCol; ColR).
  assert (HNCol2 : ~ Col P Q C) by (intro; apply (par_strict_not_col_2 Q' Q C' P); ColR).
  assert (HPer : Per A P Q) by (apply l8_2, per_col with A'; Perp; Col).
  assert (HOS1 : OS A P C Q).
    apply in_angle_one_side; Col.
    apply per_not_col; auto.
  destruct (aristotle P Q A P C) as [X [Y]]; Col.
  { exists A, P, Q; split; Perp; split.
      apply inangle__lea; trivial.
    intro HCongA.
    assert (Out P C Q) by (apply (conga_os__out A); assumption).
    apply HNCol2; Col.
  }

  spliter.
  apply (not_and_lt P Q X Y).
  split; trivial.
  destruct (l8_18_existence P Q Y) as [Z [HZ1 HZ2]].
    intro; assert_diffs; apply HNCol2; ColR.
  apply lt_transitivity with P Z.

  - assert (P <> Z).
    { intro; subst Z.
      assert_diffs.
      assert (Per Q P C) by (apply per_col with Y; Col; Perp).
      apply HNCol1, cop_perp2__col with P Q; Perp; Cop.
    }
    assert (HLam : Lambert P X Y Z).
    { assert_diffs.
      repeat split; auto.
        apply per_col with Q; Col.
        apply l8_2, per_col with A; Perp; Col.
        apply perp_per_1, perp_left_comm, perp_col with Q; auto.
        assert (InAngle Y X P Q).
          apply l11_25 with C A Q; try (apply l6_6); trivial; apply out_trivial; auto.
        apply coplanar_perm_12, col_cop__cop with Q; Col; Cop.
    }
    apply lam_obtuse__lt; trivial.
    apply <- (lam_obtuse__oah P); trivial.

  - assert (HOut : Out Q P Z).
    { apply col_one_side_out with Q'; Col.
      apply one_side_transitivity with Y.
        assert_diffs; apply l12_6, par_strict_col_par_strict with C'; Par; ColR.
      apply l12_6, par_not_col_strict with Y; Col.
      { apply l12_9 with P Q; Perp; [Cop..| |Cop].
        apply coplanar_perm_12, col_cop__cop with C; Col.
        apply  col_cop__cop with C'; Col; Cop.
      }
      apply not_col_permutation_1, par_not_col with P C'; Par; ColR.
    }
    assert_diffs.
    apply bet__lt1213; auto.
    apply out2__bet; trivial.
    apply col_one_side_out with A; Col.
    apply one_side_transitivity with Y.
    { apply l12_6, par_not_col_strict with Y; Col.
        apply l12_9 with P Q; Perp; [Cop..|].
        apply coplanar_perm_12, col_cop__cop with C; Col; Cop.
      intro; apply HNCol1; ColR.
    }
    apply one_side_symmetry, out_out_one_side with C; Side.
Qed.

Lemma aristotle__acute_or_right :
  aristotle_s_axiom ->
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros aristotle.
  destruct saccheri_s_three_hypotheses as [Ha|[Hr|Ho]]; auto.
  exfalso; apply aristotle__obtuse_case_elimination in aristotle; auto.
Qed.

End Aristotle.
