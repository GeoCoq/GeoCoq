Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.

Context `{T2D:Tarski_2D}.

Lemma bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle :
  bachmann_s_lotschnittaxiom -> weak_triangle_circumscription_principle.
Proof.
intros HP A B C A1 A2 B1 B2 HNC HPer HPerpB1 HPerpB2.
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
Qed.

End bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.