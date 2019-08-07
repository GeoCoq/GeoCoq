Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section par_perp_perp_playfair.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma par_perp_perp_implies_playfair :
  perpendicular_transversal_postulate ->
  playfair_s_postulate.
Proof.
intro HPTP; intros A1 A2 B1 B2 C1 C2 P HPar1 HCol1.
revert C1 C2.
cut (forall C1 C2, P <> C1 -> Par A1 A2 C1 C2 -> Col P C1 C2 -> Col C1 B1 B2 /\ Col C2 B1 B2).
  {
  intros Haux C1 C2.
  elim (eq_dec_points P C1); auto.
  intro HC1.
  elim (eq_dec_points P C2); intros HC2 HPar2 HCol2.
    subst; split; assumption.
  elim (Haux C2 C1); Col; Par.
  }
intros C1 C2 HDiff HPar2 HCol2.
elim (col_dec A1 A2 P); intro HCol.

  {
  elim HPar1; clear HPar1; intro HPar1.
    exfalso; apply HPar1; exists P; split; Col.
  elim HPar2; clear HPar2; intro HPar2.
    exfalso; apply HPar2; exists P; split; Col.
  destruct HPar1 as [_ [HDiff2 [HCol3 HCol4]]];
  destruct HPar2 as [HDiff1 [HDiff3 [HCol5 HCol6]]].
  split; ColR.
  }

  {
  assert(HI := l8_18_existence A1 A2 P HCol); destruct HI as [I [HCol' HPerp]].
  assert (HCop1 : Coplanar B1 B2 P I) by (apply col__coplanar; Col).
  assert (HCop2 : Coplanar C1 C2 P I) by (apply col__coplanar; Col).
  assert (HPerp1 := HPTP A1 A2 B1 B2 P I HPar1 HPerp HCop1).
  assert (HPerp2 := HPTP A1 A2 C1 C2 P I HPar2 HPerp HCop2).
  assert (HCop3 : Coplanar A1 A2 P B1)
    by (assert_diffs; apply coplanar_perm_1, col_cop__cop with B2;
        Col; apply par__coplanar, HPar1).
  assert (HCop4 : Coplanar A1 A2 P B2)
    by (assert_diffs; apply coplanar_perm_1, col_cop__cop with B1;
        Col; apply coplanar_perm_1, par__coplanar, HPar1).
  assert (HCop5 : Coplanar A1 A2 P C1)
    by (assert_diffs; apply coplanar_perm_1, col_cop__cop with C2;
        Col; apply par__coplanar, HPar2).
  assert (HCop6 : Coplanar A1 A2 P I) by Cop.
  assert (Perp P C1 P I)
    by (apply perp_left_comm, perp_col with C2; Col).
  assert (Col P C1 B1).
    {
    elim (eq_dec_points P B1); intro HPB1; [subst; Col|].
    apply cop_perp2__col with P I; [CopR|assumption|].
    apply perp_left_comm, perp_col with B2; Col.
    }
  assert (Col P C1 B2).
    {
    elim (eq_dec_points P B2); intro HPB2; [subst; Col|].
    apply cop_perp2__col with P I; [CopR|assumption|].
    apply perp_left_comm, perp_col with B1; Col; Perp.
    }
  split; apply (col3 P C1); Col.
  }
Qed.

End par_perp_perp_playfair.