Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.

Context `{T2D:Tarski_2D}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom :
  weak_inverse_projection_postulate -> bachmann_s_lotschnittaxiom.
Proof.
intro hrap.
cut (forall A1 A2 B1 B2 C1 C2 D1 D2,
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        ~ Col A1 A2 D1 -> ~ Col B1 B2 C1 ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).

  {
  clear hrap; intro lotschnitt.
  intros P Q R P1 R1 HPQ HQR HPerQ HPerP HPerR.
  destruct (eq_dec_points P P1).
    subst; exists R; Col.
  destruct (eq_dec_points R R1).
    subst; exists P; Col.
  assert (HNCol : ~ Col P Q R) by (apply per_not_col; auto).
  destruct (lotschnitt P Q Q R P P1 R R1) as [S [HS1 HS2]]; Col; Perp.
  exists S; auto.
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
  assert (HNCol5 : ~ Col Q C1 C2) by (apply par_not_col with B1 B2; trivial).
  assert (HNCol6 : ~ Col Q D1 D2) by (apply par_not_col with A1 A2; trivial).
  assert (P <> Q) by (intro; subst; contradiction).
  assert (Q <> R) by (intro; subst; contradiction).
  assert (Per P Q R) by (apply HQ3; trivial).
  assert (HNCol7 : ~ Col P Q R) by (apply per_not_col; trivial).
  destruct (angle_bisector P Q R) as [M [HM1 HM2]]; auto.
  assert (HSuma : SumA P Q M P Q M P Q R).
    assert_diffs; apply conga3_suma__suma with P Q M M Q R P Q R; CongA; SumA.
  assert (HAcute : Acute P Q M).
  { apply nbet_isi_suma__acute with P Q R; auto.
      intro HBet; apply HNCol7; Col.
    destruct (isi_dec P Q M P Q M); trivial.
    assert_diffs.
    exfalso; apply (lea__nlta P Q M P Q R).
      exists M; split; CongA.
    apply obtuse_per__lta; trivial.
    apply nisi__obtuse; auto.
  }

  assert (HC3 : exists C3, Col C1 C2 C3 /\ OS P Q R C3).
  { destruct (diff_col_ex3 C1 C2 P) as [C0]; Col; spliter.
    destruct (not_par_same_side P Q C0 P P R) as [C3 []]; Col.
      intro; apply HNCol5; ColR.
    exists C3; split; trivial; ColR.
  }
  destruct HC3 as [C3 [HCol1 HOS1]].
  destruct (hrap P Q M P Q R P C3) as [S [HS1 HS2]]; trivial.
    apply out_trivial; auto.
    assert_diffs; auto.
    apply HP3; Col.

  assert (HD3 : exists D3, Col D1 D2 D3 /\ OS R Q P D3).
  { destruct (diff_col_ex3 D1 D2 R) as [D0]; Col; spliter.
    destruct (not_par_same_side R Q D0 R R P) as [D3 []]; Col.
      intro; apply HNCol6; ColR.
    exists D3; split; trivial; ColR.
  }
  destruct HD3 as [D3 [HCol2 HOS2]].
  destruct (hrap R Q M R Q P R D3) as [T [HT1 HT2]]; Perp.
    apply (acute_conga__acute P Q M); CongA.
    assert_diffs; apply conga3_suma__suma with P Q M P Q M P Q R; CongA.
    apply out_trivial; auto.
    assert_diffs; auto.
    apply HR3; Col.

  assert (HOut : Out Q S T) by (apply l6_7 with M; trivial; apply l6_6; assumption).
  assert (HCol3 : Col C1 C2 S) by (assert_diffs; ColR).
  assert (HCol4 : Col D1 D2 T) by (assert_diffs; ColR).
  destruct (Col_dec C1 C2 T).
    exists T; Col.
  destruct (Col_dec D1 D2 S).
    exists S; Col.
  destruct HOut as [HSQ [HTQ [HBet|HBet]]].
  - assert (HTS : TS C1 C2 R T).
      apply l9_8_2 with Q.
      repeat split; Col; exists S; Col.
      apply l12_6, par_strict_col2_par_strict with B1 B2; Par; Col.
    assert_diffs.
    destruct HTS as [_ [_ [I [HI1 HI2]]]].
    exists I; split; ColR.
  - assert (HTS : TS D1 D2 P S).
      apply l9_8_2 with Q.
      repeat split; Col; exists T; Col.
      apply l12_6, par_strict_col2_par_strict with A1 A2; Par; Col.
    assert_diffs.
    destruct HTS as [_ [_ [I [HI1 HI2]]]].
    exists I; split; ColR.
  }
Qed.

End weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.