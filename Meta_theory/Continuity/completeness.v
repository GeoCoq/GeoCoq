Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_2.
Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_3.
Require Import GeoCoq.Meta_theory.Continuity.grad.

Section Extension.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma line_extension_symmetry : forall {Tm : Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q, line_extension f P Q -> line_extension f Q P.
Proof.
  intros Tm f P Q [HPQ [fInj [fBet fCong]]].
  repeat split; auto; intro; intros; [apply fInj|apply fBet|apply fCong]; Col.
Qed.

Lemma line_extension_stability : forall {Tm: Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q R,
  Col P Q R -> P <> R -> line_extension f P Q -> line_extension f P R.
Proof.
  intros Tm f P Q R HCol HPR [HPQ [fInj [fBet fCong]]].
  repeat split; auto; intro; intros;
    [apply fInj|apply fBet|apply fCong]; trivial; apply col_transitivity_1 with R; Col.
Qed.

Lemma line_extension_reverse_bet : forall {Tm: Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q, line_extension f P Q ->
  forall A B C, Col P Q A -> Col P Q B -> Col P Q C -> Bet (f A) (f B) (f C) -> Bet A B C.
Proof.
  intros Tm f P Q [HPQ [fInj [fBet fCong]]] A B C HA HB HC HBet.
  assert (HCol : Col A B C) by (apply (col3 P Q); assumption).
  destruct HCol as [|[HBet'|HBet']]; trivial;
  [assert (B = C)|assert (A = B)]; try (subst B; Between);
  apply fInj; trivial;
  [apply between_equality with (f A)|apply between_equality with (f C)]; Between.
Qed.

Lemma pres_bet_line__col : forall {Tm: Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q, P <> Q -> pres_bet_line f P Q ->
  forall A B C, Col P Q A -> Col P Q B -> Col P Q C -> Col (f A) (f B) (f C).
Proof.
  intros Tm f P Q HPQ fBet A B C HA HB HC.
  destruct (col3 P Q A B C) as [HBet|[HBet|HBet]]; trivial; apply fBet in HBet; Col.
Qed.

Lemma col2_diff_inj_line__diff : forall {Tm: Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q, inj_line f P Q ->
  forall A B, Col P Q A -> Col P Q B -> A <> B -> f A <> f B.
Proof.
  intros Tm f P Q finj A B HA HB HAB Habs.
  apply HAB, finj; assumption.
Qed.

Lemma extension__line_extension : forall {Tm: Tarski_neutral_dimensionless}
  (f : @Tpoint Tn -> @Tpoint Tm) P Q,
  P <> Q -> extension f -> line_extension f P Q.
Proof.
  unfold extension, inj, pres_bet, pres_cong, line_extension, inj_line, pres_bet_line, pres_cong_line.
  intros Tm f P Q HPQ fext; spliter.
  repeat split; auto.
Qed.

Lemma extension_reverse_bet : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  (f : @Tpoint Tn -> @Tpoint Tm),
  extension f ->
  forall A B C, Bet (f A) (f B) (f C) -> Bet A B C.
Proof.
  intros Tm Tm2 f [finj [fBet fCong]] A B C HBet.
  destruct (eq_dec_points (f A) (f B)) as [Heq|].
    apply finj in Heq; subst; Between.
  destruct (segment_construction A B B C) as [D [HD1 HD2]].
  assert (C = D); [|subst; auto].
  apply finj.
  apply between_cong_3 with (f A) (f B); Cong.
Qed.

Lemma extension_reverse_col : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  (f : @Tpoint Tn -> @Tpoint Tm),
  extension f ->
  forall A B C, Col (f A) (f B) (f C) -> Col A B C.
Proof.
  unfold Col.
  intros Tm Tm2 f fext A B C HCol.
  assert (fBetInv := extension_reverse_bet f fext).
  destruct HCol as [|[|]]; auto.
Qed.

End Extension.

(** The following section is inspired by Theorem 32 of Hilbert's Foundations of Geometry (10th edition).
    It deduces completeness of a 2 or 3-dimensional space from completeness of lines.
    The original proof is due to Paul Bernays. *)

Section Completeness.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma line_completeness_aux : line_completeness ->
  forall (Tm: Tarski_neutral_dimensionless)
  (Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm)
  (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  extension f ->
  forall A P Q R, ~ Col P Q R -> Coplanar (f P) (f Q) (f R) A ->
    exists B, Coplanar P Q R B /\ f B = A.
Proof.
  intros lc Tm Tm2 f archi fext A P Q R HNCol HCop.
  assert (fext' := fext).
  assert (Haux : forall X Y, X <> Y -> line_extension f X Y).
    intros; apply extension__line_extension; assumption.
  unfold extension, inj, pres_bet, pres_cong in fext'; spliter.
  destruct (@midpoint_existence Tn TnEQD P Q) as [S HS].
  assert_diffs.
  destruct (col_dec (f R) (f S) A).
  { assert (HB : exists B, Col R S B /\ f B = A).
      assert (R <> S) by (intro; subst; apply HNCol; Col).
      apply lc; auto.
    destruct HB as [B []].
    exists B; split; [exists S; left; split|]; Col.
  }
  destruct (col_dec (f P) (f Q) A).
  { assert (HB : exists B, Col P Q B /\ f B = A) by (apply lc; auto).
    destruct HB as [B []].
    exists B; split; Cop.
  }
  destruct (hilbert_s_version_of_pasch (f P) (f Q) (f R) A (f S)) as [X [HX1 HX2]]; trivial.
    repeat split; Between.
  assert (HY : exists Y, Coplanar P Q R Y /\ f Y = X).
  { destruct HX2 as [[]|[]];
      [assert (HY : exists Y, Col P R Y /\ f Y = X)|assert (HY : exists Y, Col Q R Y /\ f Y = X)];
      try apply lc; Col;
      destruct HY as [Y []]; exists Y; split; Cop.
  }
  destruct HY as [Y []].
  subst X.
  assert (S <> Y).
  { intro; treat_equalities.
    apply HNCol.
    apply (extension_reverse_col f); auto.
    assert (Bet P S Q) by Between.
    assert (Bet (f P) (f S) (f Q)) by auto.
    destruct HX2 as [[HBet []]|[HBet []]];
      [|apply col_permutation_4]; apply (col_transitivity_2 (f S)); Col.
  }
  assert (HB : exists B, Col S Y B /\ f B = A) by (apply lc; Col).
  destruct HB as [B []].
  exists B.
  split; [apply col_cop2__cop with S Y|]; Cop.
Qed.

Lemma line_completeness__completeness_for_planes : line_completeness -> completeness_for_planes.
Proof.
  intros lc Tm Tm2 M f archi fext A.
  assert (HB : exists B, Coplanar PA PB PC B /\ f B = A).
    apply line_completeness_aux; trivial; [exact lower_dim|apply all_coplanar].
  destruct HB as [B []].
  exists B; assumption.
Qed.

Lemma line_completeness__completeness_for_3d_spaces :
  (exists P Q R S, ~ Coplanar P Q R S) ->
  line_completeness -> completeness_for_3d_spaces.
Proof.
  intros [P [Q [R [S HNCop]]]] lc Tm Tm2 M f archi fext A.
  assert (~ Col P Q R) by (apply ncop__ncol with S, HNCop).
  assert (Haux : forall X, (exists B, Coplanar P Q X B /\ f B = A) -> exists B, f B = A).
    intros X [B []]; exists B; assumption.
  destruct (col_dec (f P) (f Q) A).
    apply (Haux R), line_completeness_aux; Cop.
  assert (pi : plane_intersection_axiom).
  { cut upper_dim_3_axiom.
      apply upper_dim_3_equivalent_axioms; simpl; tauto.
    unfold upper_dim_3_axiom; exact upper_dim_3.
  }
  destruct (pi (f P) (f Q) A (f P) (f R) (f S) (f P)) as [X [HX1 [HX2 HX3]]]; Cop.
  assert (HY : exists Y, Coplanar P R S Y /\ f Y = X).
    apply line_completeness_aux; trivial; apply ncop__ncol with Q; Cop.
  destruct HY as [Y []]; subst.
  apply (Haux Y), line_completeness_aux; Cop.
  intro.
  apply HNCop.
  apply coplanar_perm_16, col_cop__cop with Y; Col; Cop.
  intro; subst; apply HX3; reflexivity.
Qed.

End Completeness.

(** In the following section, we prove that our formalizations of
    Hilbert's axiom of completeness
    are always true in spaces with dimension respectively greater than 2 and 3.
    The next one states the contrapositive lemmas. *)

Section Dimension.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma extension_to_plane__plane : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  {M : Tarski_2D Tm2}
  (f : @Tpoint Tn -> @Tpoint Tm),
  extension f ->
  @upper_dim_axiom Tn.
Proof.
  intros Tm Tm2 M f fext A B C P Q HPQ H1 H2 H3.
  apply (extension_reverse_col f); trivial.
  unfold extension, inj, pres_cong in fext; spliter.
  unfold Col; apply upper_dim with (f P) (f Q); auto.
Qed.

Lemma nupper_dim__completeness_for_planes : ~ upper_dim_axiom -> completeness_for_planes.
Proof.
  intros lowerdim Tm Tm2 M f archi fext A.
  exfalso; apply lowerdim.
  apply extension_to_plane__plane with f; trivial.
Qed.

Lemma extension_to_3d__upper_dim_3 : forall {Tm: Tarski_neutral_dimensionless}
  {Tm2 : Tarski_neutral_dimensionless_with_decidable_point_equality Tm}
  {M : Tarski_3D Tm2}
  (f : @Tpoint Tn -> @Tpoint Tm),
  extension f ->
  @upper_dim_3_axiom Tn.
Proof.
  intros Tm Tm2 M f fext A B C P Q R; intros.
  apply (extension_reverse_col f); trivial.
  unfold extension, inj, pres_cong in fext; spliter.
  unfold Col; apply upper_dim_3 with (f P) (f Q) (f R); auto.
Qed.

Lemma nupper_dim_3__completeness_for_3d_spaces : ~ upper_dim_3_axiom -> completeness_for_3d_spaces.
Proof.
  intros lowerdim Tm Tm2 M f archi fext A.
  exfalso; apply lowerdim.
  apply extension_to_3d__upper_dim_3 with f; trivial.
Qed.

End Dimension.

Section Dimension'.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma ncompleteness_for_planes__upper_dim : ~ completeness_for_planes -> upper_dim_axiom.
Proof.
  intro nc.
  apply upper_dim_stab.
  intro nupper.
  apply nc, (nupper_dim__completeness_for_planes nupper).
Qed.

Lemma ncompleteness_for_3d_spaces__upper_dim_3 : ~ completeness_for_3d_spaces -> upper_dim_3_axiom.
Proof.
  intro nc.
  apply upper_dim_3_stab.
  intro nupper.
  apply nc, (nupper_dim_3__completeness_for_3d_spaces nupper).
Qed.

End Dimension'.

(** In the following section, we prove that Hilbert's axiom of line completeness
    is always true in non-archimedean spaces. *)

Section Archimedes.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma archimedes_aux : forall P Q,
  (forall R S, Bet P Q R -> Bet P Q S -> Q <> R -> Reach Q R Q S) -> archimedes_axiom.
Proof.
  intros P Q Haux A B C D HAB.
  destruct (segment_construction P Q A B) as [R []].
  destruct (segment_construction P Q C D) as [S []].
  destruct (Haux R S) as [R' [HGrad HLe]]; Col.
    intro; treat_equalities; auto.
  assert (Bet Q R R') by (apply grad__bet, HGrad).
  assert (HB' : Le A B Q R') by (apply le_transitivity with Q R; Le).
  apply l5_5_1 in HB'.
  destruct HB' as [B' []].
  exists B'; split.
    apply (grad2__grad456 Q R R'), bet_cong2_grad__grad2; trivial.
    apply l4_3_1 with Q A; Cong.
  apply (l5_6 Q S Q R'); Cong.
Qed.

Lemma not_archimedes__line_completeness : ~ archimedes_axiom -> line_completeness.
Proof.
  intros narchi Tm Tm2 P Q f archi Hf.
  assert (Hf' := Hf).
  destruct Hf' as [HPQ [finj [fBet fCong]]].
  assert (Haux := col2_diff_inj_line__diff f P Q finj).
  exfalso.
  apply narchi, (archimedes_aux P Q).
  intros R S HR HS HQR.
  remember (f Q) as Q'.
  remember (f R) as R'.
  remember (f S) as S'.
  destruct (archi Q' R' Q' S') as [R0' [HGrad HLe]].
    subst; intro; apply HQR, finj; Col.
  assert (HBet : Bet Q' S' R0').
  { destruct (eq_dec_points Q S); [subst; Between|].
    apply l6_13_1; trivial.
    apply l6_7 with R'; subst.
      apply l6_2 with (f P); Col; apply fBet; Between; Col.
    apply bet_out; Col; apply grad__bet, HGrad.
  }
  clear HLe.
  revert S S' HeqS' HS HBet.
  induction HGrad; intros; subst.
  { exists R; split; [apply grad_init|].
    apply bet__le1213, (line_extension_reverse_bet f P Q); Col.
  }
  rename C into C0'.
  destruct (eq_dec_points Q S).
    subst; exists R; split; [apply grad_init|apply le_trivial].
  assert (Hd : Bet (f Q) (f S) C0' \/ Bet (f Q) C0' (f S)).
  { destruct (eq_dec_points C0' (f Q)); [subst; Between|].
    apply l6_7 with C'.
      apply bet_out; Col.
    apply l6_6, bet_out; Col.
  }
  destruct Hd; [apply IHHGrad with (f S); trivial|].
  assert (HS0 : exists S0, Bet Q S0 S /\ Cong S S0 Q R).
  { apply segment_reverse, (line_extension_reverse_bet f P Q); Col.
    apply between_exchange4 with C0'; Between.
  }
  destruct HS0 as [S0 []].
  assert (S <> S0) by (intro; treat_equalities; auto).
  assert (HC0 : Reach Q R Q S0).
  { assert (Bet P Q S0) by (apply between_inner_transitivity with S; assumption).
    apply IHHGrad with (f S0); trivial.
    apply between_inner_transitivity with (f S); Col.
    destruct (eq_dec_points C0' (f S)); [subst; Between|].
    apply between_symmetry, l6_13_1.
      apply bet2__out with (f Q); try apply between_symmetry; Col.
    apply (l5_6 (f S) C0' C0' C').
      apply le_left_comm, bet__le1213, (between_exchange3 (f Q)); assumption.
      Cong.
      apply cong_symmetry, cong_transitivity with (f Q) (f R); Col.
  }
  clear IHHGrad.
  destruct HC0 as [C0 []].
  destruct (segment_construction Q C0 Q R) as [C []].
  exists C; split; [apply grad_stab with C0; Cong|].
  apply bet__le1213.
  destruct (eq_dec_points Q S0).
  { subst S0; assert (R = S) by (apply (between_cong_3 P Q); Cong).
    treat_equalities; apply between_exchange4 with C0; Between.
  }
  assert (Bet Q S0 C0).
  { apply l6_13_1; trivial.
    apply l6_7 with S; [Out|].
    apply l6_7 with R.
      apply l6_2 with P; Between.
      apply bet_out; Between.
  }
  apply outer_transitivity_between2 with S0; auto.
  assert (Bet Q S0 C) by (apply between_exchange4 with C0; assumption).
  apply l6_13_1.
    apply l6_2 with Q; Between; intro; treat_equalities; auto.
  apply le_right_comm; exists C0; split.
    apply between_inner_transitivity with Q; Between.
    apply cong_transitivity with  Q R; Cong.
Qed.

End Archimedes.
