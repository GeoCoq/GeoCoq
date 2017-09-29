Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.

Context `{T2D:Tarski_2D}.

Lemma bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle :
  bachmann_s_lotschnittaxiom -> weak_triangle_circumscription_principle.
Proof.
intros HP.
cut (forall A1 A2 B1 B2 C1 C2 D1 D2,
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        ~ Col A1 A2 D1 -> ~ Col B1 B2 C1 ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).

  {
  clear HP; intros HP A B C A1 A2 B1 B2 HNC HPer HPerpB1 HPerpB2.
  destruct (HP B C A C A1 A2 B1 B2) as [I [? ?]]; try (exists I; Col);
  try solve[apply perp_right_comm; apply per_perp; assert_diffs; Perp];
  try solve[apply perp_sym; apply perp_bisect_perp; auto].

    {
    assert (HPar : Par B1 B2 B C).
      {
      apply l12_9 with A C;
      [apply perp_bisect_perp; auto|
       apply perp_right_comm;apply per_perp; assert_diffs; Perp].
      }
    intro H; apply (not_strict_par _ _ _ _ B1) in HPar; Col.
    destruct HPar as [HC1 HC2];
    destruct HPerpB2 as [[[X [HMid HC3]] [HPerp|?]] HF]; auto.
    assert (C = X); [|treat_equalities; intuition].
    elim (perp_not_col2 B1 B2 C A); Perp; intro;
    [apply l6_21 with B1 B2 C A|apply l6_21 with B1 B2 A C]; Col.
    }

    {
    assert (HPar : Par A1 A2 A C).
      {
      apply l12_9 with B C;
      [apply perp_bisect_perp; auto|
       apply perp_right_comm;apply per_perp; assert_diffs; Perp].
      }
    intro H; apply (not_strict_par _ _ _ _ A1) in HPar; Col.
    destruct HPar as [HC1 HC2];
    destruct HPerpB1 as [[[X [HMid HC3]] [HPerp|?]] HF]; auto.
    assert (C = X); [|treat_equalities; intuition].
    elim (perp_not_col2 A1 A2 C B); Perp; intro;
    [apply l6_21 with A1 A2 C B|apply l6_21 with A1 A2 B C]; Col.
    }
  }

  {
  rename HP into bla.
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
  destruct (bla P Q R P1 R1) as [I [HI1 HI2]]; auto.
    apply HP3; Col.
    apply HR3; Col.
  exists I.
  split; assert_diffs; ColR.
  }
Qed.

End bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.