Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Ch11_angles.

Section weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom :
  weak_triangle_circumscription_principle -> bachmann_s_lotschnittaxiom.
Proof.
intro HP.
apply bachmann_s_lotschnittaxiom_aux.
intros A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD Hd1 Hd2 HPerp1 HPerp2 HPerp3.
intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4.
destruct (symmetric_point_construction IAB IAC) as [E HE].
destruct (symmetric_point_construction IAB IBD) as [F HF].
assert_diffs.
assert (HPerp4 : Perp E IAB IAB F).
  {
  apply perp_col0 with B1 B2; [apply perp_col0 with A1 A2|..]; ColR.
  }
assert (~ Col IAC IAB IBD).
  apply per_not_col; auto; apply per_col with F; Col; apply l8_2, per_col with E; Perp; Col.
assert (Coplanar E F IAB D1) by CopR.
assert (Coplanar E F IAB D2) by CopR.
assert (Coplanar E F IAB C1) by CopR.
assert (Coplanar E F IAB C2) by CopR.
destruct (HP E F IAB D1 D2 C1 C2) as [I [HC7 HC8]]; auto;
[apply not_col_permutation_1, perp_not_col| |split..|exists I; split; Col]; Perp; split.
  exists IBD; split; auto.
  left; apply perp_col0 with B1 B2; ColR.
  exists IAC; split; auto.
  left; apply perp_col0 with A1 A2; ColR.
Qed.

End weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.