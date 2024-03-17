Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Main.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Main.Annexes.perp_bisect.
Require Import GeoCoq.Main.Tarski_dev.Ch11_angles.

Section bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle :
  bachmann_s_lotschnittaxiom -> weak_triangle_circumscription_principle.
Proof.
rewrite bachmann_s_lotschnittaxiom_aux.
intros HP A B C A1 A2 B1 B2 HNC HPer.
intros HPerpB1 HPerpB2 HCop1 HCop2 HCop3 HCop4.
destruct (perp_bisect_perp _ _ _ _ HPerpB1) as [A3 [HA [_ [HCol1 [HCol2 _]]]]].
destruct (perp_bisect_perp _ _ _ _ HPerpB2) as [B3 [HB [_ [HCol3 [HCol4 _]]]]].
assert_diffs.
destruct (HP B C A C A1 A2 B1 B2 C A3 B3) as [I [? ?]];
  [..|exists I; split; auto]; Col; Perp; [| |CopR..].
- assert (HC' := HPerpB1).
  destruct HC' as [[[C' [HMid HCol]] _] _].
  intro; treat_equalities; assert_diffs.
  assert (C = C'); [|treat_equalities; auto].
  elim (perp_not_col2 _ _ _ _ (perp_bisect_perp _ _ _ _ HPerpB1)); intro HNC';
  [apply l6_21 with A1 A2 B C|apply l6_21 with A1 A2 C B]; Col.

- assert (HC' := HPerpB2).
  destruct HC' as [[[C' [HMid HCol]] _] _].
  intro; treat_equalities; assert_diffs.
  assert (C = C'); [|treat_equalities; auto].
  elim (perp_not_col2 _ _ _ _ (perp_bisect_perp _ _ _ _ HPerpB2)); intro HNC';
  [apply l6_21 with B1 B2 A C|apply l6_21 with B1 B2 C A]; Col.
Qed.

End bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.
