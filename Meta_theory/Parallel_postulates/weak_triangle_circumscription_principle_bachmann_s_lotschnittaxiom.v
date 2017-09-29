Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.

Context `{TD:Tarski_2D}.

Lemma weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom :
  weak_triangle_circumscription_principle -> bachmann_s_lotschnittaxiom.
Proof.
intro HP.
cut (forall A1 A2 B1 B2 C1 C2 D1 D2,
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        ~ Col A1 A2 D1 -> ~ Col B1 B2 C1 ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).

  {
  intros lotschnitt P Q R P1 R1 HPQ HQR HPerQ HPerP HPerR.
  destruct (eq_dec_points P P1).
    subst; exists R; Col.
  destruct (eq_dec_points R R1).
    subst; exists P; Col.
  assert (HNCol : ~ Col P Q R) by (apply per_not_col; auto).
  destruct (lotschnitt P Q Q R P P1 R R1) as [S [HS1 HS2]]; Col; Perp.
  exists S; auto.
  }

  {
  intros A1 A2 B1 B2 C1 C2 D1 D2 HPerp1 HPerp2 HPerp3 HNC1 HNC2.
  destruct (perp_inter_perp_in_n A1 A2 B1 B2) as [AB [HC1 [HC2 _]]]; Perp.
  destruct (perp_inter_perp_in_n A1 A2 C1 C2) as [AC [HC3 [HC4 _]]]; Perp.
  destruct (perp_inter_perp_in_n B1 B2 D1 D2) as [BD [HC5 [HC6 _]]]; Perp.
  destruct (symmetric_point_construction AB AC) as [E HE].
  destruct (symmetric_point_construction AB BD) as [F HF].
  assert (HPerp4 : Perp E AB AB F).
    {
    assert (E <> AB).
      {
      intro; treat_equalities; apply HNC2;
      apply not_strict_par1 with C2 AC; Col.
      apply l12_9 with A1 A2; Perp.
      }
    assert (AB <> F).
      {
      intro; treat_equalities; apply HNC1;
      apply not_strict_par1 with D2 BD; Col.
      apply l12_9 with B1 B2; Perp.
      }
    apply perp_col0 with B1 B2; try (apply perp_col0 with A1 A2); Col;
    assert_diffs; assert_cols; ColR.
    }
  destruct (HP E F AB D1 D2 C1 C2) as [I [HC7 HC8]]; try (exists I; Col);
  try (apply not_col_permutation_1; apply perp_not_col); try apply perp_per_1;
  try solve[assert_diffs; Perp]; split; [|assert_diffs| |assert_diffs]; auto;
  split; [exists BD; split; Col| |exists AC; split; Col|]; left;
  [apply perp_col0 with B1 B2|apply perp_col0 with A1 A2];
  assert_diffs; Col; ColR.
  }
Qed.

End weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.