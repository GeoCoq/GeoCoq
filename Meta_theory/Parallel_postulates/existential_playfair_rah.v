Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section existential_playfair_rah.

Context `{T2D:Tarski_2D}.

Lemma existential_playfair__rah :
  existential_playfair_s_postulate ->
  postulate_of_right_saccheri_quadrilaterals.
Proof.
intro HP; destruct HP as [A1 [A2 [P [HNC1 HP]]]].
destruct (l8_18_existence A1 A2 P) as [Q [HCcol1 HPerp1]]; Col.
destruct (perp_exists P Q P) as [R HPerp2]; [assert_diffs; auto|].
assert (HPar1 : Par A1 A2 P R) by (apply l12_9 with P Q; Perp).
assert (HNC2 : Par_strict A1 A2 P R)
  by (apply par_not_col_strict with P; Col).
apply par_strict_not_col_4 in HNC2.
destruct (l8_18_existence A1 A2 R) as [S [HCcol2 HPerp3]]; Col.
assert (HPar2 : Par P Q R S) by (apply l12_9 with A1 A2; Perp).
assert (HNC3 : ~ Col P Q R) by (apply perp_not_col; Perp).
assert (HNC4 : Par_strict P Q R S)
  by (apply par_not_col_strict with R; Col).
apply par_strict_not_col_3 in HNC4.
destruct (l8_18_existence R S P) as [R' [HCcol3 HPerp4]]; Col.
assert (HPar3 : Par A1 A2 P R') by (apply l12_9 with R S; Perp).
destruct (HP P R P R') as [_ HCol4]; Col.
assert (R = R') by (apply l6_21 with P R S R; assert_diffs; Col).
treat_equalities; rewrite <- (lam_per__rah P Q S R).

  {
  apply perp_in_per_1 with S S; apply l8_14_2_1b_bis; Col.
  apply perp_sym; apply perp_col0 with A1 A2; Col.
  assert (H : Par_strict P Q R S) by (apply par_not_col_strict with R; Col).
  apply par_strict_not_col_2 in H; assert_diffs; auto.
  }

  {
  assert (H : Par_strict P Q R S) by (apply par_not_col_strict with R; Col).
  apply par_strict_not_col_2 in H.
  repeat try (split; [intro; treat_equalities; assert_diffs; intuition|]).
  split;[apply perp_in_per_1 with P P; apply l8_14_2_1b_bis; Col|
         split;[apply perp_in_per_1 with R R; apply l8_14_2_1b_bis; Col|
                apply perp_in_per_1 with Q Q; apply l8_14_2_1b_bis; Col]];
  Perp; apply perp_col0 with A1 A2; assert_diffs; Col.
  }
Qed.

End existential_playfair_rah.