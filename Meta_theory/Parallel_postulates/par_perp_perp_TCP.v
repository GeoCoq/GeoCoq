Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section par_perp_perp_TCP.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma par_perp_perp_implies_perp_bisect_existence :
  perpendicular_transversal_postulate ->
  forall A B, A <> B -> exists P, exists Q, Perp_bisect P Q A B.
Proof.
intros HPTP A B HDiff.
assert (HM := midpoint_existence A B); destruct HM as [M HM].
assert(HP' := l6_25 A B HDiff); destruct HP' as [P' HP'].
assert(HQ' := l8_18_existence A B P' HP'); clear HP'.
destruct HQ' as [Q' [Hc HP'Q']]; clear Hc.
assert (HPQ := parallel_existence P' Q' M).
destruct HPQ as [P [Q [HDiff' [HPar HCol]]]]; try (assert_diffs; assumption).
exists P; exists Q; unfold Perp_bisect.
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
Qed.

End par_perp_perp_TCP.
