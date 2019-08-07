Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.rah_thales_postulate.
Require Import GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_weak_triangle_circumscription_principle.
Require Import GeoCoq.Meta_theory.Parallel_postulates.thales_postulate_thales_converse_postulate.
Require Import GeoCoq.Meta_theory.Parallel_postulates.weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section universal_posidonius_postulate_perpendicular_transversal_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma universal_posidonius_postulate__perpendicular_transversal_postulate_aux :
  universal_posidonius_postulate -> forall E F G H R P,
  Perp E G R P -> Coplanar F H P R -> Col E G R -> Saccheri E F H G ->
  Perp F H P R.
Proof.
intros HP E F G H R P HPerp HCop HCol HSacc.
assert (HPerp1 : Perp E G E F) by (apply perp_sym, sac__perp1214 with H, HSacc).
assert (HPar : Par_strict E G F H) by (apply sac__pars1423, HSacc).
assert_diffs.
assert (HRAH : postulate_of_right_saccheri_quadrilaterals).
  {
  destruct (midpoint_existence E G) as [M1 HM1].
  destruct (midpoint_existence F H) as [M2 HM2].
  assert (HLamb := mid2_sac__lam6521 _ _ _ _ _ _ HSacc HM2 HM1).
  unfold Lambert in HLamb; spliter.
  assert (Saccheri M1 M2 F E).
    {
    repeat split; Perp.
      apply cong_symmetry, cong_left_commutativity, HP with E G F H; Col; Par.
      apply perp_col2 with E M1; Perp; Col.
    apply l12_6, (par_strict_col4__par_strict E G F H); Col.
    }
  apply per_sac__rah with M1 M2 F E; auto.
  }
destruct (eq_dec_points E R) as [|HER].
  {
  subst R.
  assert (Col F P E) by (apply (cop_per2__col G); Perp; CopR).
  apply perp_sym, perp_left_comm, perp_col with F; Col.
  apply per_perp; auto; apply HRAH with G, HSacc.
  }
assert (HP' : forall A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD, IAB <> IAC -> IAB <> IBD ->
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        Col A1 A2 IAB -> Col B1 B2 IAB ->
        Col A1 A2 IAC -> Col C1 C2 IAC ->
        Col B1 B2 IBD -> Col D1 D2 IBD ->
        Coplanar IAB IAC IBD C1 -> Coplanar IAB IAC IBD C2 ->
        Coplanar IAB IAC IBD D1 -> Coplanar IAB IAC IBD D2 ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).
  {
  apply bachmann_s_lotschnittaxiom_aux.
  apply weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom.
  apply thales_converse_postulate__weak_triangle_circumscription_principle.
  apply thales_postulate__thales_converse_postulate.
  apply rah__thales_postulate; assumption.
  }
assert (Coplanar F H E R) by (apply col_cop__cop with G; Col; Cop).
assert (~ Col F H R) by (intro; apply HPar; exists R; split; Col).
destruct (HP' E G E F P R F H E R F) as [S [HC7 HC8]]; Col; [Perp| |CopR|Cop..|].
  apply HRAH in HSacc; Perp.
assert (S <> R) by (intro; apply HPar; exists R; subst; split; Col).
assert (HSacc2 : Saccheri E F S R).
  {
  repeat split.
    apply per_col with G; Perp; Col.
    apply perp_per_1; apply (perp_col4 E G R P); Col.
    apply cong_right_commutativity, HP with E G F H; Col; Par.
    apply perp_sym, perp_col with P; Perp; Col.
  apply l12_6, par_strict_col_par_strict with H; Col;
  [|apply par_strict_symmetry, par_strict_col_par_strict with G; Col; Par].
  intro; treat_equalities.
  assert (~ Col G E F) by (apply per_not_col; Perp).
  assert (Col E P R) by (apply col_cop2_perp2__col with F E G; Perp; Col; Cop).
  apply HER, l6_21 with E G F E; ColR.
  }
assert_diffs.
apply perp_col with S; Col.
assert (Hd := HSacc2).
apply sac_distincts in Hd; spliter.
apply perp_sym, perp_comm, perp_col with S; Col.
apply per_perp; auto.
apply HRAH with E, sac_perm, HSacc2.
Qed.


Lemma universal_posidonius_postulate__perpendicular_transversal_postulate :
  universal_posidonius_postulate -> perpendicular_transversal_postulate.
Proof.
intros HP A B C D P Q HPar.
revert P Q.
cut (forall P Q, Perp A B P Q -> Coplanar C D P Q -> ~ Col A B P -> Perp C D P Q).
  {
  intros Haux P Q HPerp HCop.
  destruct (perp_not_col2 A B P Q HPerp); [|apply perp_right_comm]; apply Haux; Perp; Cop.
  }
intros P Q HPerp HCop HNCol.
assert (HH := HPar).
destruct HH as [HPars|]; [|spliter; apply (perp_col2 A B); auto; ColR].
assert (HH := HPerp); destruct HH as [R HR];
apply perp_in_col in HR; destruct HR as [HR1 HR2].
destruct (l8_18_existence A B C) as [E [HE1 HE2]].
  apply par_strict_not_col_1 with D, HPars.
destruct (l8_18_existence A B D) as [G [HG1 HG2]].
  apply par_strict_not_col_4 with C, HPars.
assert (E <> G).
  {
  intro; subst G.
  assert (Col C D E) by (apply col_cop2_perp2__col with E A B; [Perp..|Col|Cop|Cop]).
  apply HPars; exists E; split; Col.
  }
assert (Saccheri E C D G).
  {
  repeat split.
    apply perp_per_1, perp_col0 with A B; Perp.
    apply perp_per_1, perp_col2 with A B; Perp.
    apply cong_right_commutativity, HP with A B C D; Perp; Col.
  apply l12_6, par_strict_symmetry, par_strict_col2_par_strict with A B; Par.
  }
assert (P <> Q) by (apply perp_distinct in HPerp; apply HPerp).
apply perp_sym, perp_col with R; Col.
apply perp_sym.
assert (P <> R) by (intro; subst; apply HNCol, HR1).
apply par_distinct in HPar; spliter.
apply universal_posidonius_postulate__perpendicular_transversal_postulate_aux with E G; trivial.
  apply perp_col2 with A B; Col; apply perp_sym, perp_left_comm, perp_col with Q; Perp.
  apply col_cop__cop with Q; trivial.
  apply (col3 A B); auto.
Qed.

End universal_posidonius_postulate_perpendicular_transversal_postulate.