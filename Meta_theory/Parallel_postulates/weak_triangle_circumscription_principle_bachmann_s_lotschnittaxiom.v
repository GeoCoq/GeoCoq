Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.

Context `{TD:Tarski_2D}.

Lemma weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom :
  weak_triangle_circumscription_principle -> bachmann_s_lotschnittaxiom.
Proof.
intros HP A1 A2 B1 B2 C1 C2 D1 D2 HPerp1 HPerp2 HPerp3 HNC1 HNC2.
destruct (perp_inter_perp_in_n A1 A2 B1 B2) as [AB [HC1 [HC2 _]]]; Perp.
destruct (perp_inter_perp_in_n A1 A2 C1 C2) as [AC [HC3 [HC4 _]]]; Perp.
destruct (perp_inter_perp_in_n B1 B2 D1 D2) as [BD [HC5 [HC6 _]]]; Perp.
destruct (symmetric_point_construction AB AC) as [E HE].
destruct (symmetric_point_construction AB BD) as [F HF].
assert (HPerp4 : Perp E AB AB F).
  {
  assert (E <> AB).
    {
    intro; treat_equalities; apply HNC2; apply not_strict_par1 with C2 AC; Col.
    apply l12_9 with A1 A2; Perp.
    }
  assert (AB <> F).
    {
    intro; treat_equalities; apply HNC1; apply not_strict_par1 with D2 BD; Col.
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
Qed.

End weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.