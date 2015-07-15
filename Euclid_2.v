Require Export Euclid_aux.
Require Export Ch13_1.

Section Euclid_2.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma proclus_s_postulate_implies_strong_parallel_postulate :
  proclus_postulate -> SPP.
Proof.
intros HP P Q R S T U HPTQ HRTS HNC HCop HCong1 Hcong2.
destruct (HP P R Q S P U) as [I [HCol1 HCol2]]; try exists I; Col.
apply l12_17 with T; assert_diffs; Col; split; Cong; unfold BetS in *; spliter; Between.
Qed.

Lemma playfair_s_postulate_implies_midpoints_converse_postulate :
  playfair_s_postulate ->
  midpoints_converse_postulate.
Proof.
intros HP A; intros.
destruct (midpoint_existence A C) as [X HAC].
assert (X = Q).
 assert (Par_strict A B X P).
  apply triangle_mid_par with C; assumption.
 assert_diffs.
 assert_cols.
 apply l6_21 with A C P Q.
  intro.
  assert (Col A B C) by ColR.
  contradiction.
  assert (Par A B Q P /\ A <> B /\ Q <> P) by (apply par_distincts; finish).
  spliter; intuition.
  Col.
  Col.
  destruct (HP A B Q P X P P) as [HCol1 HCol2]; Col; apply par_strict_par; Par.
  Col.
treat_equalities; assumption.
Qed.

Lemma midpoints_converse_postulate_implies_playfair :
  midpoints_converse_postulate ->
  playfair_s_postulate.
Proof.
intros HT A1 A2 B1 B2 C1 C2 P HPar1 HCol1 HPar2 HCol2.
elim HPar1; clear HPar1; intro HPar1; elim HPar2; clear HPar2; intro HPar2.

  {
  assert (HDiff : P <> A1) by (intro; treat_equalities; apply HPar1; exists P; Col).
  assert (HX := symmetric_point_construction A1 P); destruct HX as [X HMid1].
  assert (HB3 : exists B3, Col B1 B2 B3 /\ BetS A2 B3 X).
    {
    assert (H : P <> B1 \/ P <> B2).
      {
      elim (par_strict_distinct A1 A2 B1 B2 HPar1); intros.
      elim (eq_dec_points P B1); intro; elim (eq_dec_points P B2); intro; treat_equalities; intuition.
      }
    elim H; clear H; intro H.

      {
      destruct (hilbert_s_version_of_pasch X A1 A2 B1 P) as [B3 [HCol HBet]];
      assert_diffs; unfold is_midpoint in *; spliter;
      try (exists B3; split); Col; unfold BetS in *; try ColR; [| |repeat split; Between|].

        {
        intro; apply HPar1; exists A2; split; Col; ColR.
        }

        {
        intro; apply H; apply l6_21 with A1 P B1 P; Col.

          {
          intro; apply par_strict_not_col_3 in HPar1; apply HPar1; ColR.
          }

          {
          assert_diffs; assert_cols; ColR.
          }
        }

        {
        induction HBet; spliter; Between.
        assert (Hc : ~ Bet A2 B3 A1) by (intro; apply HPar1; exists B3; assert_cols; split; ColR).
        exfalso; apply Hc; Between.
        }
      }

      {
      destruct (hilbert_s_version_of_pasch X A1 A2 B2 P) as [B3 [HCol HBet]];
      assert_diffs; unfold is_midpoint in *; spliter;
      try (exists B3; split); Col; unfold BetS in *; try ColR; [| |repeat split; Between|].

        {
        intro; apply HPar1; exists A2; split; Col; ColR.
        }

        {
        intro; apply H; apply l6_21 with A1 P B2 P; Col.

          {
          intro; apply par_strict_not_col_3 in HPar1; apply HPar1; ColR.
          }

          {
          assert_diffs; assert_cols; ColR.
          }
        }

        {
        induction HBet; spliter; Between.
        assert (Hc : ~ Bet A2 B3 A1) by (intro; apply HPar1; exists B3; assert_cols; split; ColR).
        exfalso; apply Hc; Between.
        }
      }
    }
  destruct HB3 as [B3 [HCol3 HBet1]].
  assert (HPB3 : P <> B3).
    {
    intro; treat_equalities; apply HPar1.
    exists P; unfold BetS in *; spliter; assert_diffs; assert_cols; split; ColR.
    }
  assert (HPar3 : Par A1 A2 P B3) by (apply par_col2_par with B1 B2; try ColR; try left; Par).
  assert (HC3 : exists C3, Col C1 C2 C3 /\ BetS A2 C3 X).
    {
    assert (H : P <> C1 \/ P <> C2).
      {
      elim (par_strict_distinct A1 A2 C1 C2 HPar2); intros.
      elim (eq_dec_points P C1); intro; elim (eq_dec_points P C2); intro; treat_equalities; intuition.
      }
    elim H; clear H; intro H.

      {
      destruct (hilbert_s_version_of_pasch X A1 A2 C1 P) as [C3 [HCol HBet]];
      assert_diffs; unfold is_midpoint in *; spliter;
      try (exists C3; split); Col; unfold BetS in *; try ColR; [| |repeat split; Between|].

        {
        intro; apply HPar2; exists A2; split; Col; ColR.
        }

        {
        intro; apply H; apply l6_21 with A1 P C1 P; Col.

          {
          intro; apply par_strict_not_col_3 in HPar2; apply HPar2; ColR.
          }

          {
          assert_diffs; assert_cols; ColR.
          }
        }

        {
        induction HBet; spliter; Between.
        assert (Hc : ~ Bet A2 C3 A1) by (intro; apply HPar2; exists C3; assert_cols; split; ColR).
        exfalso; apply Hc; Between.
        }
      }

      {
      destruct (hilbert_s_version_of_pasch X A1 A2 C2 P) as [C3 [HCol HBet]];
      assert_diffs; unfold is_midpoint in *; spliter;
      try (exists C3; split); Col; unfold BetS in *; try ColR; [| |repeat split; Between|].

        {
        intro; apply HPar2; exists A2; split; Col; ColR.
        }

        {
        intro; apply H; apply l6_21 with A1 P C2 P; Col.

          {
          intro; apply par_strict_not_col_3 in HPar2; apply HPar2; ColR.
          }

          {
          assert_diffs; assert_cols; ColR.
          }
        }

        {
        induction HBet; spliter; Between.
        assert (Hc : ~ Bet A2 C3 A1) by (intro; apply HPar2; exists C3; assert_cols; split; ColR).
        exfalso; apply Hc; Between.
        }
      }
    }
  destruct HC3 as [C3 [HCol4 HBet2]].
  assert (HPC3 : P <> C3).
    {
    intro; treat_equalities; apply HPar1.
    exists P; unfold BetS in *; spliter; assert_diffs; assert_cols; split; ColR.
    }
  assert (HPar4 : Par A1 A2 P C3) by (apply par_col2_par with C1 C2; try ColR; try left; Par).
  assert (HCol5 : Col A2 X B3) by (unfold BetS in *; spliter; assert_cols; Col).
  assert (HCol6 : Col A2 X C3) by (unfold BetS in *; spliter; assert_cols; Col).
  assert (HNC' : ~ Col A1 A2 X)
    by (intro; apply HPar1; exists P; assert_diffs; assert_cols; split; ColR).
  assert (B3 = C3) by (apply l7_17 with A2 X; apply HT with A1 P; Col; Par).
  elim (par_strict_distinct A1 A2 B1 B2 HPar1); intros.
  elim (par_strict_distinct A1 A2 C1 C2 HPar2); intros.
  treat_equalities; split; ColR.
  }

  {
  elim (par_strict_distinct A1 A2 B1 B2 HPar1); intros; spliter; exfalso; apply HPar1.
  exists P; split; Col; ColR.
  }

  {
  elim (par_strict_distinct A1 A2 C1 C2 HPar2); intros; spliter; exfalso; apply HPar2.
  exists P; split; Col; ColR.
  }

  {
  spliter; spliter; split; Col; ColR.
  }
Qed.

Lemma tarski_s_euclid_implies_parallel_unicity_aux :
  tarski_s_parallel_postulate ->
  forall A1 A2 B1 B2 C1 C2 P, ~ Col P A1 A2 ->
  Par A1 A2 B1 B2 -> Col P B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2.
Proof.
intros HTE; intros.
apply par_distincts in H0.
apply par_distincts in H2.
spliter.
assert(HPar1 : Par_strict A1 A2 B1 B2) by (apply (par_not_col_strict _ _ _ _ P); Col; intro; apply H; Col).
assert(HPar2 : Par_strict A1 A2 C1 C2) by (apply (par_not_col_strict _ _ _ _ P); Col; intro; apply H; Col).
elim (line_dec B1 B2 C1 C2); intro HLine.

  assumption.

  assert (HLineNew : ~ Col C1 B1 B2 \/ ~ Col C2 B1 B2) by (induction (Col_dec C1 B1 B2); induction (Col_dec C2 B1 B2);tauto).
  clear HLine; rename HLineNew into HLine.
  assert(HC' : exists C', Col C1 C2 C' /\ two_sides B1 B2 A1 C').
    {
    elim HLine; clear HLine; intro HNC;
    [destruct (not_par_other_side B1 B2 C1 C2 P A1) as [C' [HCol HTS]]|
     destruct (not_par_other_side B1 B2 C2 C1 P A1) as [C' [HCol HTS]]];
    try exists C'; Col; intro; apply HPar1; exists A1; Col.
    }
  ex_and HC' C'.
  unfold two_sides in H9.
  spliter.
  ex_and H12 B.
  double C' P C.
  unfold is_midpoint in H14.
  spliter.
  assert(HD : exists D, Bet B D C /\ Bet P D A1) by (apply inner_pasch with C'; Between).
  ex_and HD D.
  assert(C' <> P) by (intro; subst C'; contradiction).
  assert (Par A1 A2 C' P) by (apply par_col2_par with C1 C2; Col).
  assert(HPar3 : Par_strict A1 A2 C' P) by (apply (par_not_col_strict _ _ _ _ P); Col).
  assert(B <> P).
    intro.
    subst B.
    apply (par_not_col _ _ _ _ A1) in HPar3.
      apply HPar3; Col.
      Col.
  assert(P <> C).
    intro.
    treat_equalities.
    absurde.
  assert(Col B P B1) by ColR. 
  assert(Col B P B2) by ColR. 
  assert(Col C' P C1) by ColR.
  assert(Col C P C1) by (assert_cols;ColR).
  assert(Col C' P C2) by ColR. 
  assert(Col C P C2) by (assert_cols;ColR).

  assert(~Col B P C)
    by (intro;apply H11;assert_cols;ColR).
 
  assert(P <> D) by (intro; subst D; apply bet_col in H16; contradiction).
  assert(HE := HTE P B C D A1 H17 H16 H29).
  ex_and HE X; ex_and H30 Y.
  assert(Hx := l12_6 A1 A2 P X).

  assert (P<>X)
    by (intro;treat_equalities;intuition).

  assert(Par_strict A1 A2 P X) by (apply (par_strict_col2_par_strict _ _ B1 B2); Col; apply col3 with B P; Col).
  apply Hx in H34.
  assert(Hy := l12_6 A1 A2 P Y).

  assert (P<>Y)
    by (intro;treat_equalities;intuition).

  assert(HPar4 : Par_strict A1 A2 P Y) by (apply (par_strict_col2_par_strict _ _ C1 C2); Col; apply (col3 C P); Col).
  apply Hy in HPar4.
  assert(HOS : one_side A1 A2 X Y) 
     by (apply one_side_transitivity with P; try assumption; unfold one_side in *; ex_and H34 Z; exists Z; split; assumption).
  assert(Ho := HOS). 
  unfold one_side in HOS.
  ex_and HOS Z.
  unfold two_sides in H36.
  unfold two_sides in H37.
  spliter.
  assert(HTS : two_sides A1 A2 X Y) by (unfold two_sides; repeat split; try assumption; exists A1; split; Col).
  apply l9_9 in HTS.
  contradiction.
Qed.

Lemma tarski_s_euclid_implies_playfair :
 tarski_s_parallel_postulate ->
 playfair_s_postulate.
Proof.
intros HTE A1; intros.
assert( A1 <> A2 /\ B1 <> B2) by (apply par_distinct;auto).
assert( A1 <> A2 /\ C1 <> C2) by (apply par_distinct;auto).
spliter.
clear H4.
induction(Col_dec P A1 A2). 
  (** If P is one line A1A2 then line A1A2=B1B2=C1C2 and we can conclude. *)
  induction H. 

    exfalso.
    apply H.
    exists P.
    split; Col.

    induction H1.

      exfalso.
      apply H1.
      exists P.
      split; Col.

      spliter.
      split;ColR.
  (** In the other case we use the previous lemma. *)
  apply (tarski_s_euclid_implies_parallel_unicity_aux HTE A1 A2 _ _ _ _ P); auto.
Qed.

Lemma par_trans_implies_playfair :
  postulate_of_transitivity_of_parallelism -> playfair_s_postulate.
Proof.
intros HPT A1; intros.
assert (Par C1 C2 B1 B2) by (apply HPT with A1 A2; Par).
induction H3.
exfalso; apply H3; exists P; Col.
spliter; split; Col.
Qed.

Lemma par_trans_implies_par_not_par :
  postulate_of_transitivity_of_parallelism ->
  forall A B C D P Q, Par A B C D -> ~Par A B P Q -> ~Par C D P Q.
Proof.
intro HP; intros A B C D P Q HPar HNPar.
intro HNPar'.
apply HNPar.
apply HP with C D; Par.
Qed.

Lemma inter_dec_plus_par_trans_imply_proclus :
  decidability_of_intersection ->
  postulate_of_transitivity_of_parallelism ->
  proclus_postulate.
Proof.
intros HID HPTP A; intros.
assert (~ Par A B P Q)
  by (apply col_not_col_not_par; [exists P; Col | exists Q; Col]).
assert(~ Par C D P Q) by (apply par_trans_implies_par_not_par with A B; Par).
destruct (inter_dec_implies_not_par_inter_exists HID C D P Q H3) as [Y HY].
exists Y; spliter; Col.
Qed.

Lemma par_perp_perp_implies_playfair :
  perpendicular_transversal_postulate ->
  playfair_s_postulate.
Proof.
intro HPTP; intros A1 A2 B1 B2 C1 C2 P HPar1 HCol1 HPar2 HCol2.
elim (Col_dec A1 A2 P); intro HCol.

  {
  elim HPar1; clear HPar1; intro HPar1; try (exfalso; apply HPar1; exists P; Col);
  elim HPar2; clear HPar2; intro HPar2; try (exfalso; apply HPar2; exists P; Col).
  destruct HPar1 as [HDiff1 [HDiff2 [HCol3 HCol4]]]; clear HDiff1;
  destruct HPar2 as [HDiff1 [HDiff3 [HCol5 HCol6]]].
  split; ColR.
  }

  {
  assert(HI := l8_18_existence A1 A2 P HCol); destruct HI as [I [HCol' HPerp]].
  assert (HPerp1 := HPTP A1 A2 B1 B2 P I HPar1 HPerp).
  assert (HPerp2 := HPTP A1 A2 C1 C2 P I HPar2 HPerp).
  split.

    {
    elim (eq_dec_points P C1); intro HDiff; subst; Col.
    assert (Col P C1 B1).
      {
      elim (eq_dec_points P B1); intro HPB1; subst; Col.
      apply perp_perp_col with P I.
      apply perp_sym; apply perp_col0 with C1 C2; assert_diffs; Col.
      apply perp_sym; apply perp_col0 with B1 B2; assert_diffs; Col.
      }
    assert (Col P C1 B2).
      {
      elim (eq_dec_points P B2); intro HPB2; subst; Col.
      apply perp_perp_col with P I.
      apply perp_sym; apply perp_col0 with C1 C2; assert_diffs; Col.
      apply perp_sym; apply perp_col0 with B1 B2; assert_diffs; Col.
      }
    ColR.
    }

    {
    elim (eq_dec_points P C2); intro HDiff; subst; Col.
    assert (Col P C2 B1).
      {
      elim (eq_dec_points P B1); intro HPB1; subst; Col.
      apply perp_perp_col with P I.
      apply perp_sym; apply perp_col0 with C1 C2; assert_diffs; Col.
      apply perp_sym; apply perp_col0 with B1 B2; assert_diffs; Col.
      }
    assert (Col P C2 B2).
      {
      elim (eq_dec_points P B2); intro HPB2; subst; Col.
      apply perp_perp_col with P I.
      apply perp_sym; apply perp_col0 with C1 C2; assert_diffs; Col.
      apply perp_sym; apply perp_col0 with B1 B2; assert_diffs; Col.
      }
    ColR.
    }
  }
Qed.

Lemma par_perp_perp_implies_par_perp_2_par :
  perpendicular_transversal_postulate ->
  postulate_of_parallelism_of_perpendicular_tranversals.
Proof.
intros HPPP A1; intros.
apply l12_9 with A1 A2; try apply all_coplanar; Perp.
apply perp_sym.
apply HPPP with B1 B2; Par; Perp.
Qed.

Lemma par_perp_2_par_implies_par_perp_perp :
  postulate_of_parallelism_of_perpendicular_tranversals ->
  perpendicular_transversal_postulate.
Proof.
intros HPPP A B C D P Q HPar HPerp.
assert (HX := HPerp); destruct HX as [X HX].
elim (Col_dec C D X); intro HCDX.

  elim HPar; clear HPar; intro HPar.

    exfalso; apply HPar; exists X; unfold Perp_in in HX; spliter; Col.

    apply perp_sym; apply perp_col2_bis with A B; spliter; Col; Perp.

  assert (HY := l8_18_existence C D X HCDX); destruct HY as [Y [HCDY HPerp']].
  assert (HPar' : Par P Q X Y) by (apply HPPP with A B C D; assumption).
  elim HPar'; clear HPar'; intro HPar'.

    exfalso; apply HPar'; exists X; unfold Perp_in in HX; spliter; Col.

    destruct HPar' as [HPQ [HXY [HCol1 HCol2]]].
    apply perp_sym; apply perp_col2 with X Y; Col; Perp.
Qed.

Lemma par_perp_perp_implies_perp_bisect_existence :
  perpendicular_transversal_postulate ->
  forall A B, A <> B -> exists P, exists Q, perp_bisect P Q A B.
Proof.
intros HPTP A B HDiff.
assert (HM := midpoint_existence A B); destruct HM as [M HM].
assert(HP' := l6_25 A B HDiff); destruct HP' as [P' HP'].
assert(HQ' := l8_18_existence A B P' HP'); clear HP'.
destruct HQ' as [Q' [Hc HP'Q']]; clear Hc.
assert (HPQ := parallel_existence P' Q' M).
destruct HPQ as [P [Q [HDiff' [HPar HCol]]]]; try (assert_diffs; assumption).
exists P; exists Q; unfold perp_bisect.
split; assert_diffs; Col.
split; try (exists M; split; Col; Midpoint); left.
apply HPTP with P' Q'; finish.
Qed.

Lemma inter_dec_plus_par_perp_perp_imply_triangle_circumscription :
  decidability_of_intersection ->
  perpendicular_transversal_postulate ->
  triangle_circumscription_principle.
Proof.
intros HID HPTP A B C HNC.
assert (HAB := par_perp_perp_implies_perp_bisect_existence HPTP A B);
destruct HAB as [C1 [C2 HAB]]; try (assert_diffs; assumption).
assert (HAC := par_perp_perp_implies_perp_bisect_existence HPTP A C);
destruct HAC as [B1 [B2 HAC]]; try (assert_diffs; assumption).
assert (HInter := HID B1 B2 C1 C2).
elim HInter; clear HInter; intro HInter.

  destruct HInter as [CC [HCol1 HCol2]].

    exists CC; split.

      elim (eq_dec_points CC C1); intro HEq; try subst.

        apply perp_bisect_cong_1 with C2; assumption.

        apply perp_bisect_cong_1 with C1.
        apply perp_bisect_sym_1.
        apply perp_bisect_equiv_def in HAB.
        destruct HAB as [I [HPerp HMid]].
        apply perp_bisect_equiv_def.
        exists I; split; try assumption.
        apply perp_in_sym.
        apply perp_in_col_perp_in with C2; Col.
        apply perp_in_sym.
        assumption.

      elim (eq_dec_points CC B1); intro HEq; try subst.

        apply perp_bisect_cong_1 with B2; assumption.

        apply perp_bisect_cong_1 with B1.
        apply perp_bisect_sym_1.
        apply perp_bisect_equiv_def in HAC.
        destruct HAC as [I [HPerp HMid]].
        apply perp_bisect_equiv_def.
        exists I; split; try assumption.
        apply perp_in_sym.
        apply perp_in_col_perp_in with B2; Col.
        apply perp_in_sym.
        assumption.

  exfalso; apply HNC.
  assert (HPar : Par B1 B2 C1 C2).

    unfold Par; left.
    repeat split.

      apply perp_bisect_equiv_def in HAC.
      destruct HAC as [I [HPerp HMid]].
      apply perp_in_distinct in HPerp.
      spliter; assumption.

      apply perp_bisect_equiv_def in HAB.
      destruct HAB as [I [HPerp HMid]].
      apply perp_in_distinct in HPerp.
      spliter; assumption.

      apply all_coplanar.

      intro HInter'; apply HInter.
      destruct HInter' as [I HInter'].
      exists I; assumption.

  clear HInter; clear HNC.
  apply perp_bisect_perp in HAB; apply perp_bisect_perp in HAC.
  assert (HPerp := HPTP B1 B2 C1 C2 A C HPar HAC).
  apply par_id.
  apply l12_9 with C1 C2; finish.
  apply all_coplanar.
Qed.

Lemma triangle_circumscription_implies_tarski_s_euclid_aux :
  forall A B C D T X Y Z M1 Z1 M2 Z2,
  triangle_circumscription_principle ->
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  A <> Y ->
  B <> C ->
  B <> D ->
  B <> T ->
  B <> Y ->
  C <> D ->
  C <> T ->
  C <> Y ->
  D <> T ->
  T <> X ->
  T <> Y ->
  X <> Y ->
  Y <> Z1 ->
  Y <> Z2 ->
  ~ Col A B C ->
  Col A B M1 ->
  Col A C M2 ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col T Y Z ->
  Bet Y T X ->
  Bet Y M1 Z1 ->
  Bet Y M2 Z2 ->
  Cong Y T T X ->
  Cong Y M1 M1 Z1 ->
  Cong Y M2 M2 Z2 ->
  Perp B C T Z ->
  Perp A B Y Z1 ->
  Perp A C Y Z2 ->
  exists x, exists y, Bet A B x /\ Bet A C y /\ Bet x T y.
Proof.
intros A B C D T X Y Z M1 Z1 M2 Z2; intro HTC.
intros HAB HAC HAD HAT HAY HBC HBD HBT HBY HCD HCT HCY HDT HTX HTY HXY HYZ1 HYZ2.
intros HABC HABM1 HACM2 HADT HBCT HBDC HTYZ HYTX HYM1Z1.
intros HYM2Z2 HCong5 HCong6 HCong7 HPerp1 HPerp2 HPerp3.
elim (Col_dec X Y Z1); intro HXYZ1; elim (Col_dec X Y Z2); intro HXYZ2.

  exfalso; apply HABC; apply par_id.
  apply l12_9 with Y Z1; try apply all_coplanar; Perp.
  apply perp_col1 with Z2; assert_diffs; Perp; ColR.

  exfalso; apply HABC; apply par_id_1.
  apply l12_9 with Y Z1; try apply all_coplanar; Perp.
  apply perp_sym; apply perp_col2 with T Z; Perp; assert_cols; ColR.

  exfalso; apply HABC; apply par_id_2.
  apply l12_9 with Y Z2; try apply all_coplanar; Perp.
  apply perp_sym; apply perp_col2 with T Z; Perp; assert_cols; ColR.

  assert (H := HXYZ1); apply HTC in H; destruct H as [x [HCong1 HCong2]]; exists x;
  assert (H := HXYZ2); apply HTC in H; destruct H as [y [HCong3 HCong4]]; exists y.
  assert (HxTy : Col x T y) by (elim (eq_dec_points T x); intro; elim (eq_dec_points T y);
                                intro; try (subst; Col); apply col_permutation_4;
                                apply perp_perp_col with X Y; apply perp_bisect_perp;
                                apply cong_perp_bisect; Cong).
  assert (HABx : Col A B x).
    {
    elim (eq_dec_points A M1); intro HAM1; subst.

      {
      apply cong_perp_bisect_col with Y Z1; eCong.
      apply perp_mid_perp_bisect; try split; Cong.
      }

      {
      assert (Col M1 A x).
        {
        apply cong_perp_bisect_col with Y Z1; eCong.
        apply perp_mid_perp_bisect; try split; Cong.
        apply perp_left_comm; apply perp_col with B; Col.
        }
      ColR.
      }
    }

  assert (HACy : Col A C y).
    {
    elim (eq_dec_points A M2); intro HAM1; subst.

      {
      apply cong_perp_bisect_col with Y Z2; eCong.
      apply perp_mid_perp_bisect; try split; Cong.
      }

      {
      assert (Col M2 A y).
        {
        apply cong_perp_bisect_col with Y Z2; eCong.
        apply perp_mid_perp_bisect; try split; Cong.
        apply perp_left_comm; apply perp_col with C; Col.
        }
      ColR.
      }
    }
  assert (Hxy : x <> y).
  {
    intro; treat_equalities.
    assert (A = x) by (apply l6_21 with A B C A; Col); treat_equalities.
    assert (H : Par B C A T).
    {
      apply l12_9 with X Y; try apply all_coplanar.

        apply perp_sym; apply perp_col2 with Z T; Perp; assert_cols; ColR.

        apply perp_bisect_perp; apply cong_perp_bisect; Cong.
    }
    elim H; clear H; intro H.

      apply H; exists D; assert_cols; Col.

      spliter; apply HABC; assert_cols; ColR.
  }
  assert (HPar : Par B C x y).
  {
    apply l12_9 with X Y; try apply all_coplanar.

      apply perp_sym; apply perp_col2 with T Z; Perp; assert_cols; ColR.

      apply perp_bisect_perp; apply cong_perp_bisect; Cong.
  }
  clear HPerp1; clear HPerp2; clear HPerp3.
  clear HCong1; clear HCong2; clear HCong3; clear HCong4.
  assert (HPar' : Par_strict B C x y)
    by (elim HPar; clear HPar; intro HPar; try assumption; spliter; exfalso; apply HABC; assert_cols; ColR);
  clear HPar; rename HPar' into HPar.
  elim HxTy; clear HxTy; intro HxTy.

    elim HABx; clear HABx; intro HABx.

      elim HACy; clear HACy; intro HACy; auto.
      elim HACy; clear HACy; intro HACy.

        exfalso; apply impossible_case_1 with A B C D T x y; assumption.

        exfalso; apply impossible_case_2 with A B C D T x y; assert_cols; Col.

      elim HABx; clear HABx; intro HABx.

        exfalso; apply impossible_case_3 with A B C D T x y; assumption.

        exfalso; apply impossible_case_2 with A C B D T y x; assert_cols; Col; Between.

    elim HxTy; clear HxTy; intro HxTy.

      exfalso; apply impossible_case_4 with A B C D T x y; assumption.

      exfalso; apply impossible_case_4 with A C B D T y x; Between; Col; Par.
Qed.

Lemma tarski_s_euclid_remove_degenerated_cases :
  (forall A B C D T,
   A <> B ->
   A <> C ->
   A <> D -> 
   A <> T ->
   B <> C ->
   B <> D ->
   B <> T ->
   C <> D ->
   C <> T ->
   D <> T ->
   ~ Col A B C ->
   Bet A D T ->
   Bet B D C ->
   exists x y : Tpoint, Bet A B x /\ Bet A C y /\ Bet x T y) ->
  forall A B C D T,
  Bet A D T ->
  Bet B D C ->
  A <> D -> exists x y : Tpoint, Bet A B x /\ Bet A C y /\ Bet x T y.
Proof.
intro HGC; intros A B C D T HADT HBDC HAD.
elim (eq_dec_points A B); intro HAB.
subst; exists T; exists C; Between.
elim (eq_dec_points A C); intro HAC.
subst; exists B; exists T; Between.
elim (eq_dec_points A T); intro HAT.
exfalso; apply HAD; treat_equalities; reflexivity.
elim (eq_dec_points B C); intro HBC.
subst; exists T; exists T; Between.
elim (eq_dec_points B D); intro HBD.
subst; exists T; exists C; Between.
elim (eq_dec_points B T); intro HBT.
subst; exists T; exists C; Between.
elim (eq_dec_points C D); intro HCD.
subst; exists B; exists T; Between.
elim (eq_dec_points C T); intro HCT.
subst; exists B; exists T; Between.
elim (eq_dec_points D T); intro HDT.
subst; exists B; exists C; Between.
elim (Col_dec A B C); intro HABC.

  {
  elim HABC; clear HABC; intro HABC.

    {
    assert (H : Bet A B D) by eBetween; assert (Bet A B T) by eBetween.
    exists T; exists C; Between.
    }

    {
    elim HABC; clear HABC; intro HABC.

      {
      assert (H : Bet A C D) by eBetween; assert (Bet A C T) by eBetween.
      exists B; exists T; Between.
      }

      {
      assert (H : Bet B A D \/ Bet B D A) by (apply l5_3 with C; Between).
      elim H; clear H; intro H.

        {
        assert (H' : Bet A C T \/ Bet A T C) by (apply l5_2 with B; eBetween).
        elim H'; clear H'; intro H'.

          {
          exists B; exists T; Between.
          }

          {
          exists B; exists C; split ; try Between.
          split; try Between.
          eBetween.
          }
        }
        {
        assert (H' : Bet A B T \/ Bet A T B) by (apply l5_1 with D; Between).
        elim H'; clear H'; intro H'.

          {
          exists T; exists C; Between.
          }

          {
          exists B; exists C; split ; try Between.
          split; try Between.
          eBetween.
          }
        }
      }
    }
  }
  {
  apply HGC with D; assumption.
  }
Qed.

Lemma triangle_circumscription_implies_tarski_s_euclid :
  triangle_circumscription_principle ->
  tarski_s_parallel_postulate.
Proof.
unfold tarski_s_parallel_postulate.
intro HTC; apply tarski_s_euclid_remove_degenerated_cases.
intros A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC;
assert (HBCT : ~ Col B C T) by (intro; apply HABC; assert_cols; ColR).
assert (HY := l8_18_existence B C T HBCT); destruct HY as [Y [HBCY HPerp]].
elim (eq_dec_points B Y); intro HBY; elim (eq_dec_points C Y); intro HCY; treat_equalities.

  {
  exfalso; apply HBCT; Col.
  }

  {
  assert (HY := midpoint_existence B T); destruct HY as [Y HY].
  assert (HAY : A <> Y) by (intro; treat_equalities; assert_cols; apply HABC; ColR).
  assert (H := midpoint_distinct_1 Y B T HBT HY); destruct H as [HBY HTY];
  apply not_eq_sym in HBY; apply not_eq_sym in HTY.
  assert (HCY : C <> Y) by (intro; subst; apply HBCT; assert_cols; Col).
  destruct HY as [HBTY HBYTY].
  assert (HACY : ~ Col A C Y) by (apply impossible_two_sides_not_col with B D T; assumption).
  assert (HX := symmetric_point_construction Y T); destruct HX as [X HX].
  assert (H := midpoint_distinct_2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; try contradiction; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; try contradiction; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  elim (eq_dec_points Y Z1); intro HYZ1; treat_equalities.

    {
    assert (HFalse : Col A B C) by (assert_cols; ColR); contradiction.
    }

    {
    elim HZ1; clear HZ1; intro HZ1; try contradiction.
    elim (eq_dec_points Y Z2); intro HYZ2; treat_equalities; try contradiction.
    elim HZ2; clear HZ2; intro HZ2; try contradiction.
    apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y B M1 Z1 M2 Z2; try assumption.
    assert_cols; Col.
    }
  }

  {
  assert (HY := midpoint_existence C T); destruct HY as [Y HY].
  assert (HAY : A <> Y) by (intro; treat_equalities; assert_cols; apply HABC; ColR).
  assert (H := midpoint_distinct_1 Y C T HCT HY); destruct H as [HCY HTY];
  apply not_eq_sym in HCY; apply not_eq_sym in HTY.
  assert (HBY : B <> Y) by (intro; subst; apply HBCT; assert_cols; Col).
  destruct HY as [HCTY HCYTY].
  assert (HACY : ~ Col A B Y) by (apply impossible_two_sides_not_col with C D T; Between; Col).
  assert (HX := symmetric_point_construction Y T); destruct HX as [X HX].
  assert (H := midpoint_distinct_2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; try contradiction; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; try contradiction; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  elim (eq_dec_points Y Z2); intro HYZ2; treat_equalities.

    {
    assert (HFalse : Col A B C) by (assert_cols; ColR); contradiction.
    }

    {
    elim HZ2; clear HZ2; intro HZ2; try contradiction.
    elim (eq_dec_points Y Z1); intro HYZ1; treat_equalities; try contradiction.
    elim HZ1; clear HZ1; intro HZ1; try contradiction.
    apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y C M1 Z1 M2 Z2; try assumption.
    assert_cols; Col.
    }
  }

  {
  assert (HAY : A <> Y) by (intro; treat_equalities; assert_cols; apply HABC; ColR).
  assert (HX := symmetric_point_construction Y T); destruct HX as [X HX].
  assert (H := perp_distinct B C T Y HPerp); destruct H as [Hclear HTY]; clear Hclear.
  assert (H := midpoint_distinct_2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; try contradiction; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; try contradiction; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  assert (HABY : ~ Col A B Y) by (intro; apply HBY; apply l6_21 with A B C B; assert_cols; Col).
  assert (HACY : ~ Col A C Y) by (intro; apply HCY; apply l6_21 with A C B C; assert_cols; Col).
  elim (eq_dec_points Y Z1); intro HYZ1; treat_equalities; try contradiction.
  elim HZ1; clear HZ1; intro HZ1; try contradiction.
  elim (eq_dec_points Y Z2); intro HYZ2; treat_equalities; try contradiction.
  elim HZ2; clear HZ2; intro HZ2; try contradiction.
  apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y Y M1 Z1 M2 Z2; Col.
  }
Qed.

Lemma strong_parallel_postulate_implies_tarski_s_euclid_aux :
  SPP ->
  (forall A B C D T,
   A <> B ->
   A <> C ->
   A <> D -> 
   A <> T ->
   B <> C ->
   B <> D ->
   B <> T ->
   C <> D ->
   C <> T ->
   D <> T ->
   ~ Col A B C ->
   Bet A D T ->
   Bet B D C ->
   exists B', exists B'', exists MB, exists X, Bet A B X /\ Par_strict B C T X /\
   BetS B MB T /\ BetS B' MB B'' /\
   Cong B MB T MB /\ Cong B' MB B'' MB /\
   Col B B' D /\ Bet B'' T X /\
   B <> B' /\ B'' <> T).
Proof.
intros HSPP A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC.
destruct (symmetric_point_construction D B) as [B' HB'].
destruct (midpoint_distinct_2 B D B' HBD HB') as [HB'D HBB'].
destruct HB' as [HBDB' HCong1].
apply between_symmetry in HADT.
apply between_symmetry in HBDB'.
destruct (outer_pasch T B' D A B HADT HBDB') as [B''' [HTB'''B' HABB''']].
destruct (midpoint_existence B T) as [MB HMB].
destruct (midpoint_distinct_1 MB B T HBT HMB) as [HBMB HMBT].
destruct HMB as [HBMBT HCong2].
destruct (symmetric_point_construction B' MB) as [B'' HB''].
assert (HB'MB : MB <> B').
  {
  assert (H : ~ Col B' D MB) by (intro; apply HABC; assert_cols; ColR).
  intro; treat_equalities; apply H; Col.
  }
destruct (midpoint_distinct_2 MB B' B'' HB'MB HB'') as [HB'B'' HB''MB].
destruct HB'' as [HB'MBB'' HCong3].
assert (H1 : BetS B MB T) by (repeat split; Between).
assert (H2 : BetS B' MB B'') by (repeat split; Between).
assert (HB'T : B' <> T).
  {
  assert (H : ~ Col B B' T) by (intro; apply HABC; assert_cols; ColR).
  intro; treat_equalities; apply H; Col.
  }
assert (HB'B''' : B' <> B''').
  {
  assert (H : ~ Col A B B') by (intro; apply HABC; assert_cols; ColR).
  intro; treat_equalities; apply H; Col.
  }
assert (HB'''T : B''' <> T).
  {
  assert (H : ~ Col A B T) by (intro; apply HABC; assert_cols; ColR).
  intro; treat_equalities; apply H; Col.
  }
assert (H3 : BetS T B''' B') by (repeat split; Between).
assert (H4 : ~ Col B T B'') by (intro; apply HABC; assert_cols; ColR).
assert (H5 : Cong B MB T MB) by Cong.
assert (H6 : Cong B' MB B'' MB) by Cong.
destruct (HSPP B T B' B'' MB B''') as [X [HBetS HX]];
Col; try apply all_coplanar; try (intro; apply H4; assert_diffs; assert_cols; ColR).
assert (HNC : ~ Col B B' B''') by (intro; assert_diffs; assert_cols; apply H4; ColR).
assert (HPar1 : Par B B' T B'') by (unfold BetS in *; spliter; apply l12_17 with MB; try split; Col).
assert (HPar2 : Par B B'' T B')
  by (unfold BetS in *; spliter; assert_diffs; apply l12_17 with MB; try split; Between; Cong).
elim HBetS; clear HBetS; intro HBetS.

  {
  elim HX; clear HX; intro HX.

    {
    assert (H : BetS B'' T X).
      {
      repeat split; try (intro; treat_equalities); Col.
      apply H4; assert_diffs; assert_cols; ColR.
      }
    clear HBetS; rename H into HBetS.
    assert (H : BetS B B''' X).
      {
      repeat split; try (intro; treat_equalities); Col; unfold BetS in *; spliter;
      apply H4; assert_diffs; assert_cols; ColR.
      }
    clear HX; rename H into HX.
    apply BetSEq in HBetS; destruct HBetS as [HB''TX [HB''T [HB''X HBTX]]].
    exists B'; exists B''; exists MB; exists X.
    split; unfold BetS in HX; spliter; eBetween.
    assert (HPar : Par B' B B'' T) by (apply l12_17 with MB; try split; Between; Cong).
    assert (HPar' : Par B C B'' T)
      by (apply par_symmetry; apply par_col_par with B'; Par; assert_cols; ColR).
    split.

      {
      apply par_not_col_strict with T; Col.

        {
        apply par_col_par with B''; Par.
        assert_cols; ColR.
        }

        {
        intro; apply HABC; assert_cols; ColR.
        }
      }

      {
      repeat (split; try assumption); unfold BetS in *; spliter; assert_cols; Col.
      }
    }

    {
    elim HX; clear HX; intro HX.

      {
      exfalso; apply impossible_case_5 with B T B' B'' MB B''' X; spliter; assumption.
      }

      {
      exfalso; apply impossible_case_6 with B T B' B'' MB B''' X; spliter; assumption.
      }
    }
  }

  {
  elim HBetS; clear HBetS; intro HBetS.

    {
    exfalso; apply impossible_case_7 with B T B' B'' MB B''' X; spliter; assumption.
    }

    {
    exfalso; apply impossible_case_8 with B T B' B'' MB B''' X; spliter; assumption.
    }
  }

Qed.

Lemma strong_parallel_postulate_implies_tarski_s_euclid :
  SPP ->
  tarski_s_parallel_postulate.
Proof.
unfold tarski_s_parallel_postulate.
intro HSPP; apply tarski_s_euclid_remove_degenerated_cases.
intros A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC.
destruct (strong_parallel_postulate_implies_tarski_s_euclid_aux HSPP A B C D T)
as [B' [B'' [MB [X [HABX [HPar' [HBet1 [HBet2 [HCong1 [HCong2 [HBB'D [HB''TX [HBB' HB''T]]]]]]]]]]]]];
destruct (strong_parallel_postulate_implies_tarski_s_euclid_aux HSPP A C B D T)
as [C' [C'' [MC [Y [HACY [HPar [HBet3 [HBet4 [HCong3 [HCong4 [HCC'D [HC''TY [HCC' HC''T]]]]]]]]]]]]];
Between; Col.
clear HBet3; clear HBet4; clear HCong3; clear HCong4;
clear MC; clear HC''TY; clear HC''T; clear HPar'.
exists X; exists Y; repeat split; try assumption.
elim (Col_dec X T Y); intro HXTY.

  {
  apply between_symmetry in HACY.
  assert (HU := outer_pasch Y B C A D HACY HBDC); destruct HU as [U [HYUB HADU]].
  apply between_symmetry in HABX.
  assert (HV := outer_pasch X Y B A U HABX HYUB); destruct HV as [V [HXVY HAUV]].
  assert (HAX : A <> X) by (intro; treat_equalities; Col).
  assert (HAY : A <> Y) by (intro; treat_equalities; Col).
  assert (HAXY : ~ Col A X Y) by (intro; assert_cols; apply HABC; ColR).
  assert (HAU : A <> U) by (intro; treat_equalities; Col).
  assert (HEq : T = V) by (assert_cols; apply l6_21 with X Y A D; Col; ColR); subst; assumption.
  }

  {
  assert (HNC : ~ Col T B'' Y) by (intro; apply HXTY; unfold BetS in *; spliter; assert_cols; ColR).
  assert (HCop : coplanar T B B'' Y).
    {
    apply coplanar_pseudo_trans with A B C; assert_cols; Cop.

      {
      exists D; assert_cols; Col5.
      }

      {
      assert (HABD : ~ Col A B D) by (intro; assert_cols; apply HABC; ColR).
      apply coplanar_pseudo_trans with A B D; assert_cols; Cop.
      assert (HTS : two_sides A D B B'').
        {
        apply l9_8_2 with X.

          {
          split; try assumption.
          assert (HAX : A <> X) by (intro; treat_equalities; apply HABC; Col).
          split; try (intro; assert_cols; apply HABC; ColR).
          split; try (intro; assert_cols; apply HABC; ColR).
          exists T; split; Col; Between.
          }

          {
          assert (HADA : Col A D A) by Col.
          assert (HXBA : Col X B A) by (assert_cols; Col).
          rewrite (l9_19 A D X B A HAD HADA HXBA).
          assert (HAX : A <> X) by (intro; treat_equalities; apply HABC; Col).
          split; try (intro; assert_cols; apply HABC; ColR); split; auto.
          }
        }
      destruct HTS as [HDiff [HCol1 [HCol2 [I [HCol3 HBet]]]]];assert_cols; exists I; Col5.
      }
    }
  destruct (HSPP T B B'' B' MB Y) as [I [HCol1 HCol2]]; Cong;
  try (unfold BetS in *; spliter; repeat (split; try Between)).
  exfalso; apply HPar; exists I; split; Col.
  elim (eq_dec_points I B); intro HBI; subst; Col.
  unfold BetS in *; spliter; assert_cols; ColR.
  }
Qed.

Lemma strong_parallel_postulate_implies_inter_dec :
  SPP ->
  decidability_of_intersection.
Proof.
intros HSPP S Q P U.
elim (Col_dec P Q S); intro HPQS; [left; exists P; Col|].
elim (eq_dec_points P U); intro HPU; treat_equalities; [left; exists Q; Col|].
assert (H := midpoint_existence P Q); destruct H as [T [HPTQ HCong1]].
assert (H := symmetric_point_construction S T); destruct H as [R [HRTS HCong2]].
elim (Col_dec P R U); intro HPRU.

  {
  assert (HPar : Par_strict Q S P U).
    {
    apply par_strict_col_par_strict with R; Col.
    apply par_not_col_strict with P; Col.
    apply l12_17 with T; assert_diffs; Col; split; Between; Cong.
    }
  destruct HPar as [H1 [H2 [H3 H]]].
  right; intro HI; apply H.
  destruct HI as [I [HCol1 HCol2]]; exists I; Col.
  }

  {
  assert (H : BetS R T S); try (clear HRTS; rename H into HRTS).
    {
    split; Between.
    split; try (intro; treat_equalities; assert_cols; Col).
    }
  assert (H : BetS P T Q); try (clear HPTQ; rename H into HPTQ).
    {
    split; Col.
    split; try (intro; treat_equalities; Col).
    }
  assert (HI := HSPP P Q R S T U); destruct HI as [I [HCol1 HCol2]]; Cong;
  try (left; exists I; Col); apply all_coplanar.
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
    assert (HCase1 : one_side P R S U -> one_side P S R U ->
                     exists I : Tpoint, Col S Q I /\ Col P U I).
      {
      apply euclid_5_implies_strong_parallel_postulate_aux with T; Col.
      }
    assert (HCase2 : one_side P R' S U -> one_side P S R' U ->
                     exists I : Tpoint, Col S Q I /\ Col P U I).
      {
      assert (HCop' : coplanar P Q' R' U).
        {
        apply coplanar_pseudo_trans with P Q R; Cop;
        try (intro; apply BetSEq in HPTQ; apply BetSEq in HRTS;
             spliter; assert_cols; apply HPQS; ColR).
        assert (HTS : two_sides P Q R Q').
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
        }
      intros HOS1 HOS2; destruct (euclid_5_implies_strong_parallel_postulate_aux HE5 P Q' R' S T' U)
      as [I [HQ'SI HPUI]]; Cong; show_distinct Q' S; Col; exists I; assert_cols; split; ColR.
      }
    destruct (symmetric_point_construction U P) as [U' HU'].
    assert (HCop' : coplanar P Q R U').
      {
      apply coplanar_pseudo_trans with P R U; assert_cols; Cop.
      }
    assert (HCase3 : one_side P R S U' -> one_side P S R U' ->
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
    assert (HCase4 : one_side P R' S U' -> one_side P S R' U' ->
                    exists I : Tpoint, Col S Q I /\ Col P U I).
      {
      assert (HCop'' : coplanar P Q' R' U').
        {
        apply coplanar_pseudo_trans with P Q R; Cop;
        try (intro; apply BetSEq in HPTQ; apply BetSEq in HRTS;
             spliter; assert_cols; apply HPQS; ColR).
        assert (HTS : two_sides P Q R Q').
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
    clear HCop'; assert (HTS : two_sides P S R R').
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
    assert (HMid : is_midpoint P R R').
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
    assert (H : coplanar P R S U); try (clear HCop; rename H into HCop).
      {
      apply coplanar_pseudo_trans with P Q R; Cop;
      try (intro; apply BetSEq in HPTQ; apply BetSEq in HRTS;
           spliter; assert_cols; apply HPQS; ColR).
      exists T; left; unfold BetS in *; spliter; assert_cols; Col.
      }
    elim (coplanar_side_dec P R R' S U U'); Col; apply BetSEq in HPTQ;
    apply BetSEq in HRTS; apply BetSEq in HPT'Q'; apply BetSEq in HR'T'S;
    spliter; assert_cols;
    try (intro; apply HPQS; ColR); try (intro; apply HNC; ColR); intuition.
    }
  }
Qed.

Lemma tarski_s_euclid_implies_euclid_5 :
  tarski_s_parallel_postulate ->
  euclid_5.
Proof.
intros HT P Q R S T U HPTQ HRTS HQUR HNC HCong1 HCong2.
destruct (symmetric_point_construction R P) as [V HMid].
assert (Hc1 : Bet V P R) by (unfold is_midpoint in *; spliter; Between).
assert (Hc2 : Bet Q U R) by (unfold BetS in *; spliter; Between).
destruct (inner_pasch V Q R P U) as [W [HPWQ HUWV]]; Col; clear Hc1; clear Hc2.
assert (HPW : P <> W).
  {
  intro; treat_equalities.
  assert (P <> V).
    {
    intro; treat_equalities; apply HNC; unfold BetS in *; spliter; assert_cols; ColR.
    }
  apply HNC; apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
  spliter; assert_cols; ColR.
  }
destruct (HT P V U W Q) as [X [Y [HPVX [HPUY HXQY]]]]; Between.
assert (HPar : Par_strict Q S P R).
  {
  apply par_not_col_strict with P; Col.
  assert_diffs; unfold BetS in *; spliter;
  apply l12_17 with T; try split; Cong; Between.
  }
assert (HTS : two_sides Q S P Y).
  {
  apply l9_8_2 with X.

    {
    assert_diffs; split; Col.
    assert (P <> R)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    assert (P <> X)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    assert (~ Col X Q S).
      {
      apply par_strict_not_col_2 with P.
      apply par_strict_symmetry; apply par_strict_col_par_strict with R; Col.
      unfold BetS in *; unfold is_midpoint in *; spliter;
      assert_diffs; assert_cols; ColR.
      }
    repeat split; try (exists Q); Col.
    intro HCol.
    assert (Q = Y)
      by (apply l6_21 with Q S X Q; try (intro; treat_equalities); Col).
    treat_equalities.
    assert (Q = U).
      {
      apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
      spliter; apply l6_21 with Q P R Q; Col.
      apply par_strict_not_col_2 with S; Par.
      }
    treat_equalities; unfold BetS in *; spliter; Col.
    }

    {
    assert (P <> R)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    assert (P <> V)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    assert (P <> X)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    apply l12_6; apply par_strict_right_comm;
    apply par_strict_col_par_strict with R; Col.
    assert_cols; ColR.
    }
  }
destruct HTS as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]];
clear Hc1; clear Hc2; clear Hc3; exists I.
assert (HPUI : BetS P U I).
 {
  assert (P <> Y)  by (intro; treat_equalities; Col).
  assert (HPUI : Col P U I) by (assert_cols; ColR).
  split.

    {
    elim HPUI; clear HPUI; intro HPUI; Col.
    elim HPUI; clear HPUI; intro HPUI; exfalso.

      {
      assert (HFalse : two_sides Q S P U).
        {
        assert_diffs; split; Col.
        split; Col.
        split; try (exists I; split; Col; Between).
        intro.
        assert (Q = U).
          {
          apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
          spliter; apply l6_21 with S Q R Q; Col.
          apply par_strict_not_col_1 with P; Par.
          }
        treat_equalities; unfold BetS in *; spliter; intuition.
        }
      apply l9_9 in HFalse; apply HFalse.
      apply one_side_transitivity with R.

        {
        apply l12_6; Col.
        }

        {
        apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
        spliter; assert_diffs; assert_cols; apply l9_19 with Q; Col.
        repeat split; Col.
        apply par_strict_not_col_1 with P; Par.
        }
      }

      {
      assert (HFalse : two_sides P R I U).
        {
        split; try (intro; treat_equalities; apply par_strict_distinct in HPar;
                    spliter; Col).
        split; try (intro; apply HPar; exists I; Col).
        split; try (exists P; split; Col; Between).
        intro.
        assert (R = U).
          {
          unfold BetS in *; spliter; apply l6_21 with P R Q U; Col.
          apply par_strict_not_col_1 with S; Par.
          }
        treat_equalities; unfold BetS in *; spliter; intuition.
        }
      apply l9_9 in HFalse; apply HFalse.
      apply one_side_transitivity with Q.

        {
        apply l12_6; apply par_strict_right_comm;
        apply par_strict_col_par_strict with S; Par; Col.
        intro; treat_equalities;
        apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR; spliter;
        apply HNC; assert_cols; ColR.
        }

        {
        assert (HPar':= HPar); apply par_strict_distinct in HPar.
        apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
        spliter; assert_diffs; assert_cols; apply l9_19 with R; Col.
        repeat split; Between.
        apply par_strict_not_col_3 with S; Par.
        }
      }
    }

    {
    split; try (intro; treat_equalities; apply par_strict_not_col_3 in HPar;
                apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
                spliter; assert_cols; Col).
    try (intro; treat_equalities; Col).
    assert (Q = U).
      {
      apply l6_21 with S Q R Q; Col.
      intro; apply HNC; ColR.
      }
    treat_equalities; unfold BetS in *; spliter; intuition.
    }
 }
split; Col.
assert (HTS : two_sides Q R S I).
  {
  apply l9_8_2 with P.

    {
    apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
    apply BetSEq in HPUI; spliter; assert_diffs; split; Col.
    assert_cols; repeat split; try (exists U; Col).
    intro; apply HNC; ColR.
    intro; apply par_strict_not_col_4 in HPar; apply HPar; ColR.
    }

    {
    apply l12_6.
    apply par_not_col_strict with P; Col;
    try (intro; apply par_strict_not_col_3 in HPar; Col).
    apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
    assert_diffs; spliter;
    apply l12_17 with T; try split; Cong; Between.
    }
  }
split.

  {
  elim HCol; intro HSQI; Between.
  assert (HFalse := HTS).
  apply l9_9 in HFalse; exfalso; apply HFalse.
  apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
  spliter; apply l9_19 with Q; Col.
  apply par_strict_not_col_4 in HPar; split; Col.
  unfold two_sides in HTS; spliter; assert_diffs; repeat split; elim HSQI; Between.
  }

  {
  assert (HFalse := HTS); unfold two_sides in HTS; spliter;
  assert_diffs; repeat split; Col; intro; treat_equalities;
  assert (HTS := not_two_sides_id S Q R); Col.
  }
Qed.

Lemma strong_parallel_postulate_SPP : strong_parallel_postulate <-> SPP.
Proof.
unfold strong_parallel_postulate; unfold SPP.
split; intros; try apply H with R T; auto; apply all_coplanar.
Qed.

End Euclid_2.