Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Main.Tarski_dev.Ch12_parallel.

Section bachmann_s_lotschnittaxiom_variant.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bachmann_s_lotschnittaxiom_aux : bachmann_s_lotschnittaxiom <->
  forall A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD, IAB <> IAC -> IAB <> IBD ->
  Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
  Col A1 A2 IAB -> Col B1 B2 IAB -> Col A1 A2 IAC ->
  Col C1 C2 IAC -> Col B1 B2 IBD -> Col D1 D2 IBD ->
  Coplanar IAB IAC IBD C1 -> Coplanar IAB IAC IBD C2 ->
  Coplanar IAB IAC IBD D1 -> Coplanar IAB IAC IBD D2 ->
  exists I, Col C1 C2 I /\ Col D1 D2 I.
Proof.
  split.
  - intros bla A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD Hd Hd' HPerpAB HPerpAC HPerpBD.
    intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4.
    assert (Col IAB IAC A1) by ColR.
    assert (Col IAB IAC A2) by ColR.
    assert (Col IAB IBD B1) by ColR.
    assert (Col IAB IBD B2) by ColR.
    assert (Coplanar IAB IAC IBD A1) by Cop.
    assert (Coplanar IAB IAC IBD A2) by Cop.
    assert (Coplanar IAB IAC IBD B1) by Cop.
    assert (Coplanar IAB IAC IBD B2) by Cop.
    assert (Per IAC IAB IBD) by (apply perp_per_1, (perp_col4 A1 A2 B1 B2); auto).
    assert (HNC1 : ~ Col IAC IAB IBD) by (apply per_not_col; auto).
    assert (HParA : Par_strict A1 A2 D1 D2).
      {
      clear dependent C1; clear dependent C2;
      apply par_not_col_strict with IBD; Col.
        apply l12_9 with B1 B2; Perp; CopR.
      intro; apply HNC1; ColR.
      }
    assert (HParB : Par_strict B1 B2 C1 C2).
      {
      clear dependent D1; clear dependent D2;
      apply par_not_col_strict with IAC; Col.
        apply l12_9 with A1 A2; Perp; CopR.
      intro; apply HNC1; ColR.
      }
    assert (HPQ : IAC <> IAB) by (assert_diffs; auto).
    assert (HQR : IAB <> IBD) by (assert_diffs; auto).
    destruct (diff_col_ex3 C1 C2 IAC) as [P1 [HC1P1 [HC2P1 [HPP1 HCP1]]]]; Col.
    destruct (diff_col_ex3 D1 D2 IBD) as [R1 [HD1R1 [HD2R1 [HRR1 HDR1]]]]; Col.
    assert_diffs.
    destruct (bla IAC IAB IBD P1 R1) as [I [HI1 HI2]]; auto.
      apply perp_per_1, (perp_col4 A1 A2 C1 C2); Col.
      apply perp_per_1, (perp_col4 B1 B2 D1 D2); Col.
      apply col_cop2__cop with C1 C2; Cop.
      apply col_cop2__cop with D1 D2; Cop.
    exists I.
    split; ColR.

  - intros lotschnitt P Q R P1 R1 HPQ HQR HPerQ HPerP HPerR HCop1 HCop2.
    destruct (eq_dec_points P P1).
      subst; exists R; Col.
    destruct (eq_dec_points R R1).
      subst; exists P; Col.
    destruct (lotschnitt P Q Q R P P1 R R1 Q P R) as [S [HS1 HS2]]; Col; Perp; Cop.
    exists S; split; assumption.
Qed.

End bachmann_s_lotschnittaxiom_variant.
