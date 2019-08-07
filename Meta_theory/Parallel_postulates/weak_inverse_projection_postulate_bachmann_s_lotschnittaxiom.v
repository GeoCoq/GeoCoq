Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux :
  weak_inverse_projection_postulate -> forall A1 A2 B1 B2 C1 C2 Q P R M,
  Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Col A1 A2 Q -> Col B1 B2 Q ->
  Col A1 A2 P -> Col C1 C2 P -> Col B1 B2 R ->
  Coplanar Q P R C1 -> Coplanar Q P R C2 -> ~ Col Q P R ->
  InAngle M P Q R -> CongA M Q P M Q R ->
  Par_strict B1 B2 C1 C2 /\ exists S, Out Q M S /\ Col C1 C2 S.
Proof.
intro hrap.
intros A1 A2 B1 B2 C1 C2 Q P R M HPerpAB HPerpAC.
intros HCol1 HCol2 HCol3 HCol4 HCol5 HCop1 HCop2 HNC HM1 HM2.
assert_diffs.
assert (HNCol1 : ~ Col A1 A2 R) by (intro; apply HNC, (col3 A1 A2); auto).
assert (HNCol2 : ~ Col B1 B2 P) by (intro; apply HNC, (col3 B1 B2); auto).
assert (HPar : Par_strict B1 B2 C1 C2).
  {
  apply par_not_col_strict with P; Col.
  assert (Col A1 P Q /\ Col A2 P Q /\ Col B1 R Q /\ Col B2 R Q)
    by (repeat split; [apply col_transitivity_1 with A2|apply (col_transitivity_2 A1)
                      |apply col_transitivity_1 with B2|apply (col_transitivity_2 B1)]; auto).
  spliter.
  assert (Coplanar Q P R A1) by Cop.
  assert (Coplanar Q P R A2) by Cop.
  assert (Coplanar Q P R B1) by Cop.
  assert (Coplanar Q P R B2) by Cop.
  apply l12_9 with A1 A2; Perp; apply coplanar_pseudo_trans with Q P R; assumption.
  }
split; [assumption|].
assert (HNCol3 : ~ Col Q C1 C2) by (apply par_not_col with B1 B2; Par; Col).
assert (Per P Q R).
  {
  apply perp_per_2, perp_col2 with A1 A2; Col;
  apply perp_sym, perp_col2 with B1 B2; Col; Perp.
  }
assert (HSuma : SumA P Q M P Q M P Q R).
  assert_diffs; apply conga3_suma__suma with P Q M M Q R P Q R; CongA; SumA.
assert (HAcute : Acute P Q M).
{ apply nbet_sams_suma__acute with P Q R; auto.
    intro; apply HNC; Col.
  assert (LeA P Q M P Q R) by Lea.
  apply sams_lea2__sams with P Q R P Q R; SumA.
}
assert (HC3 : exists C3, Col C1 C2 C3 /\ OS P Q R C3).
{ destruct (diff_col_ex3 C1 C2 P) as [C0]; Col; spliter.
  destruct (cop_not_par_same_side P Q C0 P P R) as [C3 []]; Col.
    intro; apply HNCol3; ColR.
    apply coplanar_perm_1, col_cop2__cop with C1 C2; Col; Cop.
  exists C3; split; [ColR|assumption].
}
destruct HC3 as [C3 [HCol6 HOS]].
destruct (hrap P Q M P Q R P C3) as [S [HS1 HS2]]; trivial;
  [apply out_trivial; auto|apply os_distincts in HOS; spliter; auto|
  |apply coplanar_trans_1 with R; Col; Cop|].
{ assert (HP := HPerpAC); destruct HP as [P' [_ [_ [HP1 [HP2 HP3]]]]].
  assert (P = P'); [|treat_equalities; apply HP3; Col].
  elim (perp_not_col2 _ _ _ _ HPerpAC); intro;
  [apply l6_21 with A1 A2 C1 C2|apply l6_21 with A1 A2 C2 C1]; Col.
}
exists S; split; [assumption|ColR].
Qed.

Lemma weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom :
  weak_inverse_projection_postulate -> bachmann_s_lotschnittaxiom.
Proof.
intro hrap.
apply bachmann_s_lotschnittaxiom_aux.
intros A1 A2 B1 B2 C1 C2 D1 D2 Q P R HQP HQR HPerpAB HPerpAC HPerpBD.
intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4.
assert (HNC : ~ Col P Q R).
  apply per_not_col; auto; apply perp_per_1, (perp_col4 A1 A2 B1 B2); auto.
destruct (angle_bisector P Q R) as [M [HM1 HM2]]; auto.
assert (HSuma : SumA P Q M P Q M P Q R).
  assert_diffs; apply conga3_suma__suma with P Q M M Q R P Q R; CongA; SumA.
assert (HAcute : Acute P Q M).
  {
  apply nbet_sams_suma__acute with P Q R; auto.
    intro; apply HNC; Col.
  assert (LeA P Q M P Q R) by Lea.
  assert (Per P Q R)
    by (apply perp_per_2, perp_col2 with A1 A2; Col; apply perp_sym, perp_col2 with B1 B2; Col; Perp).
  apply sams_lea2__sams with P Q R P Q R; SumA.
  }
destruct (weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux
    hrap A1 A2 B1 B2 C1 C2 Q P R M) as [HParB [S [HS1 HS2]]]; Col.
destruct (weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux
    hrap B1 B2 A1 A2 D1 D2 Q R P M) as [HParA [T [HT1 HT2]]]; [trivial..|]; [Perp|Cop..|Col| |CongA|].
  apply l11_24, HM1.
destruct (col_dec C1 C2 T).
  exists T; split; Col.
destruct (col_dec D1 D2 S).
  exists S; split; Col.
assert (HOut : Out Q S T) by (apply l6_7 with M; Out).
clear dependent M.
destruct HOut as [HSQ [HTQ [HBet|HBet]]].
- assert (HTS : TS C1 C2 R T).
  { apply l9_8_2 with Q.
      repeat split; [apply par_not_col with B1 B2; Par| |exists S; split]; Col.
    apply l12_6, par_strict_col2_par_strict with B1 B2; Par; Col.
  }
  destruct HTS as [_ [_ [I [HI1 HI2]]]].
  assert (T <> R).
    intro; treat_equalities; Col.
  exists I; split; ColR.
- assert (HTS : TS D1 D2 P S).
  { apply l9_8_2 with Q.
      repeat split; [apply par_not_col with A1 A2; Par| |exists T; split]; Col.
    apply l12_6, par_strict_col2_par_strict with A1 A2; Par; Col.
  }
  destruct HTS as [_ [_ [I [HI1 HI2]]]].
  assert (P <> S).
    intro; treat_equalities; Col.
  exists I; split; ColR.
Qed.

End weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.