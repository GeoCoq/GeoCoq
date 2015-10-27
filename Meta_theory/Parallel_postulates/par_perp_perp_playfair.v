Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section par_perp_perp_playfair.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

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

End par_perp_perp_playfair.