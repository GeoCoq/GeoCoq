Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section Archimedes.

Context `{T2D:Tarski_2D}.

(** C is on the graduation based on [AB] *)
Inductive Grad : Tpoint -> Tpoint -> Tpoint -> Prop :=
  | grad_init : forall A B, Grad A B B
  | grad_stab : forall A B C C', Grad A B C -> Bet A C C' -> Cong A B C C' -> Grad A B C'.

Definition Reach A B C D := exists B', Grad A B B' /\ Le C D A B'.

Definition archimedes_postulate := forall A B C D, A <> B -> Reach A B C D.

(** There exists n such that AC = n times AB and DF = n times DE *)
Inductive Grad2 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop :=
  | grad2_init : forall A B D E, Grad2 A B B D E E
  | grad2_stab : forall A B C C' D E F F', Grad2 A B C D E F ->
                   Bet A C C' -> Cong A B C C' ->
                   Bet D F F' -> Cong D E F F' ->
                   Grad2 A B C' D E F'.

(** Graduation based on the powers of 2 *)
Inductive GradExp : Tpoint -> Tpoint -> Tpoint -> Prop :=
  | gradexp_init : forall A B, GradExp A B B
  | gradexp_stab : forall A B C C', GradExp A B C -> Bet A C C' -> Cong A C C C' -> GradExp A B C'.

Inductive GradExp2 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop :=
  | gradexp2_init : forall A B D E, GradExp2 A B B D E E
  | gradexp2_stab : forall A B C C' D E F F', GradExp2 A B C D E F ->
                   Bet A C C' -> Cong A C C C' ->
                   Bet D F F' -> Cong D F F F' ->
                   GradExp2 A B C' D E F'.


Lemma grad__bet : forall A B C, Grad A B C -> Bet A B C.
Proof.
  intros A B C HG.
  elim HG; clear HG A B C; [Between|eBetween].
Qed.

Lemma grad_neq__neq13 : forall A B C, Grad A B C -> A <> B -> A <> C.
Proof.
  intros A B C HG HAB Heq.
  subst C.
  apply HAB.
  apply between_identity, grad__bet; trivial.
Qed.

Lemma grad_neq__neq12 : forall A B C, Grad A B C -> A <> C -> A <> B.
Proof.
  intros A B C HG.
  elim HG; clear HG A B C; intros; intro; treat_equalities.
    auto.
  apply H0; auto.
Qed.

Lemma grad112__eq : forall A B, Grad A A B -> A = B.
Proof.
  intros A B HG.
  assert (HA' : exists A', A' = A /\ Grad A A' B) by (exists A; auto).
  destruct HA' as [A' [Heq HG']].
  clear HG.
  revert Heq.
  elim HG'; auto.
  clear HG' A B A'.
  intros; treat_equalities; auto.
Qed.

Lemma grad121__eq : forall A B, Grad A B A -> A = B.
Proof.
  intros A B HG.
  apply between_identity, grad__bet; trivial.
Qed.

Lemma grad__le : forall A B C, Grad A B C -> Le A B A C.
Proof.
  intros.
  apply grad__bet in H.
  apply l5_12_a in H; spliter; auto.
Qed.

Lemma grad2__grad123 : forall A B C D E F, Grad2 A B C D E F -> Grad A B C.
Proof.
  intros A B C D E F.
  induction 1.
    apply grad_init.
    apply (grad_stab _ _ C); auto.
Qed.

Lemma grad2__grad456 : forall A B C D E F, Grad2 A B C D E F -> Grad D E F.
Proof.
  intros A B C D E F.
  induction 1.
    apply grad_init.
    apply (grad_stab _ _ F); auto.
Qed.

Lemma grad_sum : forall A B C D E, Grad A B C -> Grad A B D -> Bet A C E -> Cong A D C E ->
  Grad A B E.
Proof.
  intros A B C D E HGC HGD.
  elim (eq_dec_points A B).
  { intros; subst B.
    assert(A = C) by (apply grad112__eq; trivial).
    assert(A = D) by (apply grad112__eq; trivial).
    treat_equalities; trivial.
  }
  intro HAB.
  revert E.
  induction HGD.
    intro E; apply grad_stab; trivial.
  rename C0 into D; rename C' into D'.
  intros E' HBet' HCong'.
  destruct(segment_construction A C A D) as [E [HBet HCong]].
  assert (HBet1 : Bet A B C) by (apply grad__bet; trivial).
  assert (HBet2 : Bet A B D) by (apply grad__bet; trivial).
  assert(HBet3 : Bet C E E').
  { apply l6_13_1.
      assert_diffs; apply l6_2 with A; Between.
    apply (cong_preserves_le A D A D'); Cong.
    apply bet__le1213; trivial.
  }
  apply grad_stab with E; auto with cong; eBetween.
  apply cong_transitivity with D D'; auto.
  apply l4_3_1 with A C; Cong.
Qed.

Lemma gradexp__grad : forall A B C, GradExp A B C -> Grad A B C.
Proof.
  induction 1.
    apply grad_init.
  apply grad_sum with C C; auto.
Qed.

Lemma gradexp_le__reach : forall A B C D B', GradExp A B B' -> Le C D A B' -> Reach A B C D.
Proof.
  intros A B C D B' HGE HLe.
  exists B'; split; trivial.
  apply gradexp__grad; trivial.
Qed.

Lemma grad__ex_gradexp_le : forall A B C, Grad A B C -> exists D, GradExp A B D /\ Le A C A D.
Proof.
  intros A B C.
  induction 1.
    exists B; split; Le; apply gradexp_init.
  destruct IHGrad as [D [HGE HLe]].
  destruct (segment_construction A D A D) as [D' [HBet HCong]].
  exists D'; split.
    apply gradexp_stab with D; Cong.
  apply bet2_le2__le1346 with C D; Le.
  apply gradexp__grad, grad__bet in HGE.
  apply cong_preserves_le with A B A D; Cong; Le.
Qed.

Lemma reach__ex_gradexp_le : forall A B C D, Reach A B C D ->
  exists B', GradExp A B B' /\ Le C D A B'.
Proof.
  intros A B C D HR.
  destruct HR as [B0 [HG HLe]].
  destruct (grad__ex_gradexp_le A B B0 HG) as [B' [HG2 HLe2]].
  exists B'; split; trivial.
  apply le_transitivity with A B0; trivial.
Qed.

Lemma gradexp2__gradexp123 : forall A B C D E F, GradExp2 A B C D E F -> GradExp A B C.
Proof.
  intros A B C D E F.
  induction 1.
    apply gradexp_init.
  apply (gradexp_stab _ _ C); auto.
Qed.

Lemma gradexp2__gradexp456 : forall A B C D E F, GradExp2 A B C D E F -> GradExp D E F.
Proof.
  intros A B C D E F.
  induction 1.
    apply gradexp_init.
  apply (gradexp_stab _ _ F); auto.
Qed.

(** for every m, there exists n such that A0Dm = A0An - E0En = n(A0A1 - E0E1) (m=n) *)
Lemma t22_18_aux1 : forall A0 A1 E0 E1 D1 D,
  Bet A0 D1 A1 -> Cong E0 E1 A1 D1 ->
  Grad A0 D1 D ->
  exists A E, Grad2 A0 A1 A E0 E1 E /\ Cong E0 E A D /\ Bet A0 D A.
Proof.
  intros A0 A1 E0 E1 D1 D HBet HCong HG.
  induction HG.
    exists A1; exists E1; repeat split; auto; apply grad2_init.
  rename A into A0.
  rename B into C1.
  destruct IHHG as [A [E [HG2 [HCong2 HBet2]]]]; auto.
  destruct (segment_construction A0 A A0 A1) as [A' [HBet3 HCong3]].
  destruct (segment_construction E0 E E0 E1) as [E' [HBet4 HCong4]].
  exists A'; exists E'.
  assert(HBet5 : Bet A0 C' A').
  { assert(HBet5 : Bet A0 C A') by eBetween.
    assert(Bet C C' A'); [|eBetween].
    apply grad2__grad123 in HG2.
    apply grad__bet in HG.
    apply grad__bet in HG2.
    elim(eq_dec_points A0 C).
      intro; treat_equalities; Between.
    intro.
    elim(eq_dec_points C C').
      intro; treat_equalities; Between.
    intro.
    elim(eq_dec_points A' C).
      intro; subst A'; assert (A=C) by (apply (between_equality _ _ A0); Between); treat_equalities; Between.
    intro.
    apply l6_13_1.
      destruct (l6_2 C' A' A0 C); Between.
    apply (le_transitivity _ _ A A').
      apply (cong_preserves_le A0 C1 A0 A1); Cong; exists C1; split; Cong.
    destruct(l5_12_a C A A'); eBetween.
  }
  repeat split; auto.
    apply grad2_stab with A E; eCong.
  assert (HD : Le E0 E1 A A').
    apply (cong_preserves_le E0 E1 A1 A0); Cong; exists C1; split; Between.
  destruct HD as [D [HBet6 HCong6]].
  apply (cong_transitivity _ _ C D).
    apply (l2_11 _ E _ _ A); eCong; eBetween.
  assert (Bet C D A') by eBetween.
  apply (l4_3 _ _ A' _ _ C); Cong; eBetween.
  apply (cong_transitivity _ _ A0 C1); Cong.
  apply cong_left_commutativity; apply (l4_3 _ _ A _ _ A1); Between; eCong.
Qed.

(** for every n, B0Bn is lower than or equal to n times B0B1 *)
Lemma t22_18_aux2 : forall A0 A1 B0 B1 A B E,
  Saccheri A0 B0 B1 A1 ->
  Grad2 A0 A1 A B0 B1 E -> Saccheri A0 B0 B A -> Le B0 B B0 E.
Proof.
  intros A0 A1 B0 B1 A B E HSac1 HG.
  revert B.
  induction HG; rename A into A0; rename B into A1; rename D into B0; rename E into B1.
  { intros B HSac.
    assert(B = B1); [|subst B; Le].
    assert(Hdiff := sac_distincts A0 B0 B1 A1 HSac1); unfold Saccheri in *; spliter.
    apply (l6_11_uniqueness A1 A0 B0 B1); Cong; [|apply out_trivial; auto].
    apply (col_one_side_out _ A0).
      apply col_permutation_2; apply (per_per_col _ _ A0); Perp.
    apply (one_side_transitivity _ _ _ B0); Side.
  }
  rename C into A; rename F into E; rename C' into A'; rename F' into E'.
  intros B' HSac'.
  assert (A0 <> A).
  { intro; treat_equalities.
    assert (A0 = A1) by (apply between_identity, grad__bet, (grad2__grad123 _ _ _ B0 B1 E); auto).
    treat_equalities.
    apply sac_distincts in HSac1; spliter; auto.
  }
  assert (HB : exists B, Saccheri A0 B0 B A).
  { clear dependent A'; clear dependent B'; clear IHHG.
    apply grad2__grad123 in HG.
    apply grad__bet in HG.
    destruct (l10_15 A0 A1 A B0) as [P [HPerp HOS]]; Col.
      assert (HH := sac__ncol124 A0 B0 B1 A1); Col.
    destruct (l6_11_existence A A0 B0 P) as [B [HOut Hcong5]].
      assert_diffs; auto.
      assert(Hdiff := sac_distincts A0 B0 B1 A1 HSac1); spliter; auto.
    exists B.
    unfold Saccheri in *; spliter; assert_diffs.
    repeat split; Cong.
    - apply (per_col _ _ A1); Col.
    - apply perp_per_2; auto.
      apply (perp_col1 _ _ _ P); Col.
      apply perp_comm; apply (perp_col _ A1); Col.
    - apply invert_one_side.
      apply (out_out_one_side _ _ _ P); [|apply l6_6; auto].
      apply invert_one_side.
      apply (col_one_side _ A1); Col.
  }
  destruct HB as [B HSac].
  assert (HLe := HSac).
  apply IHHG in HLe; auto.
  clear IHHG.
  destruct (segment_construction B0 B E E') as [C [HBet HCong]].
  assert (Cong B0 B1 B B').
    apply (cong2_sac2__cong A0 B0 B1 A1 A _ _ A'); auto; [|unfold Saccheri in *; spliter; Cong].
    apply sac2__sac with A0 B0; auto.
    intro; treat_equalities; apply sac_distincts in HSac1; spliter; auto.
  apply (le_transitivity _ _ B0 C).
    apply (triangle_inequality B0 B B' C); eCong.
  apply (bet2_le2__le1346 _ B _ _ E); Le.
Qed.

Lemma t22_18 : archimedes_postulate ->
 forall A0 B0 B1 A1, Saccheri A0 B0 B1 A1 -> ~ Lt B0 B1 A1 A0.
Proof.
  intros Harchi A0 B0 B1 A1 HSac.
  intro Hlt.
  destruct Hlt as [Hle HNcong].
  destruct Hle as [D1 [Hbet Hcong]].
  destruct (segment_construction A0 D1 A0 B0) as [C0 [Hbet2 Hcong2]].
  destruct (segment_construction A0 C0 A0 B0) as [C [Hbet3 Hcong3]].
  assert(H : forall D, Grad A0 D1 D -> Lt A0 D A0 C).
  { intros D HG.
    destruct (t22_18_aux1 A0 A1 B0 B1 D1 D) as [A [E [HG2 [Hcong4 Hbet4]]]]; Between.
    assert (Hbet5 := grad2__grad123 A0 A1 A B0 B1 E HG2).
    apply grad__bet in Hbet5.
    destruct (l10_15 A0 A1 A B0) as [P [HPerp HOS]].
      Col.
      assert (H := sac__ncol124 A0 B0 B1 A1); Col.
    destruct (l6_11_existence A A0 B0 P) as [B [HOut Hcong5]].
      assert_diffs; auto.
      assert(Hdiff := sac_distincts A0 B0 B1 A1 HSac); spliter; auto.
    assert(HSac2 : Saccheri A0 B0 B A).
    { unfold Saccheri in *; spliter; assert_diffs; assert(A0 <> A) by (intro; treat_equalities; auto).
      repeat split; Cong.
      - apply (per_col _ _ A1); Col.
      - apply perp_per_2; auto.
        apply (perp_col1 _ _ _ P); Col.
        apply perp_comm; apply (perp_col _ A1); Col.
      - apply invert_one_side.
        apply (out_out_one_side _ _ _ P); [|apply l6_6; auto].
        apply invert_one_side.
        apply (col_one_side _ A1); Col.
    }
    assert(HLe : Le B0 B B0 E) by (apply (t22_18_aux2 A0 A1 B0 B1 A); auto).
    assert (HLe2 : Le B0 B A A0).
      apply (le_transitivity _ _ B0 E); auto.
      apply (cong_preserves_le A D A A0); Cong.
      destruct (l5_12_a A D A0); Between.
    assert (HLe2' := HLe2).
    destruct HLe2' as [Q [Hbet6 Hcong6]].
    apply (le1234_lt__lt _ _ A0 Q).
      apply (bet2_le2__le1245 _ _ A _ _ A); Between; Le.
      apply (cong_preserves_le B0 B B0 E); Cong.
    clear dependent D; clear dependent E.
    destruct (l6_11_existence A0 A0 B0 A) as [B0' [HOut2 Hcong4]]; 
      try (assert_diffs; intro; treat_equalities; auto).
    destruct (segment_construction A0 B0' B0 B) as [B' [Hbet7 Hcong7]].
    destruct (segment_construction B0' B' B A) as [A' [Hbet8 Hcong8]].
    assert (Le A0 A A0 A'). (** A0A' = A0B0 + B0B + BA *)
    { destruct (segment_construction A0 B0' B0 A) as [B'' [Hbet9 Hcong9]].
      apply (le_transitivity _ _ A0 B'').
        apply (triangle_inequality_2 _ B0 _ _ B0'); Cong.
      apply (bet2_le2__le1346 _ B0' _ _ B0'); Le.
        apply (outer_transitivity_between _ _ B'); auto.
        intro; treat_equalities; apply sac_distincts in HSac2; spliter; auto.
      apply (cong_preserves_le B0 A B0' A'); Cong.
      apply (triangle_inequality_2 _ B _ _ B'); Cong.
    }
    assert (HLe3 : Le B0 B A' B0').
      apply (cong_preserves_le B0' B' B0' A'); Cong; destruct (l5_12_a B0' B' A'); auto.
    destruct HLe3 as [Q' [Hbet9 Hcong9]].
    assert (HBet10 : Bet A0 B0' A').
      apply sac_distincts in HSac2; spliter; assert_diffs.
      apply (outer_transitivity_between _ _ B'); Between.
    apply (le1234_lt__lt _ _ A0 Q').
      apply (bet2_le2__le1245 _ _ A' _ _ A); eBetween.
      apply cong__le; apply (cong_transitivity _ _ B0 B); Cong.
    assert (Cong B0' Q' A0 B0).
    { apply (cong_transitivity _ _ A B); Cong.
      apply (cong_transitivity _ _ A' B'); Cong.
      assert(Hcong10 : Cong B0' B' A' Q') by (apply (cong_transitivity _ _ B0 B); auto).
      elim(bet_dec B0' Q' B').
        intro; apply (l4_3 _ _ B' _ _ Q'); Cong; eBetween.
      intro HNBet.
      apply sac_distincts in HSac2; spliter; assert_diffs.
      assert (Q' <> B0') by (intro; apply HNBet; Between).
      assert (A' <> B0') by (intro; treat_equalities; auto).
      assert (HOut3 : Out B0' B' Q').
       apply (l6_7 _ _ A'); [| apply l6_6]; apply bet_out; Between.
      assert (Hbet11 : Bet B0' B' Q').
        apply out2__bet; auto.
        apply not_bet_out; Col.
      apply (l2_11 _ B' _ _ Q'); Cong; eBetween.
    }
    assert (Hbet10 : Bet A0 D1 C) by eBetween.
    apply (cong2_lt__lt D1 C A0 C); Cong; [split|].
      destruct (l5_12_a A0 D1 C); auto.
      intro; assert (D1 = A0) by (apply (between_cong C); Between; Cong); treat_equalities; Cong.
    apply (l2_11 _ C0 _ _ B0'); eBetween; eCong.
  }
  unfold archimedes_postulate in *.
  specialize Harchi with A0 D1 A0 C.
  destruct Harchi as [D [HG Hle]].
    intro; treat_equalities; auto.
  assert(HLt := HG).
  apply H in HLt.
  apply grad__le in HG.
  apply (le__nlt A0 C A0 D); auto.
Qed.

Lemma t22_19 : archimedes_postulate -> forall A B C D, Saccheri A B C D -> ~ Obtuse A B C.
Proof.
  intros archi A B C D HSac HObt.
  assert (H := t22_18 archi _ _ _ _ (sac_perm _ _ _ _ HSac)).
  apply H.
  apply lt_left_comm, obtuse_sac__lt; auto.
Qed.

Lemma archi__obtuse_case_elimination : archimedes_postulate -> ~ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros archi obtuse.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  absurd(Obtuse A B C).
    apply t22_19 with D; trivial.
    apply obtuse with D; trivial.
Qed.

Lemma archi__acute_or_right : archimedes_postulate ->
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros archi.
  destruct saccheri_s_three_hypotheses as [Ha|[Hr|Ho]]; auto.
  exfalso; apply archi__obtuse_case_elimination in archi; auto.
Qed.


Lemma t22_23_aux : forall A B C M N L, ~ Col A M N -> Per B C A -> A <> C -> Midpoint M A B ->
  Per M N A -> Col A C N -> Midpoint M N L -> Bet A N C /\ Lambert N L B C /\ Cong B L A N.
Proof.
  intros A B C M N L HNCol HPerC HAC HM HPerN HColN HN.
  assert_diffs.
  assert (HBet : Bet A N C) by (apply per23_preserves_bet with M B; Perp; Col; Between).
  destruct (l11_49 A M N B M L) as [HCong1 [HCongA1 HCongA2]]; auto with cong.
    apply l11_14; Between.
  assert(B <> L) by (intro; treat_equalities; auto).
  repeat split; auto with cong.
  - intro; treat_equalities; apply HNCol; ColR.
  - intro; treat_equalities; apply H6.
    apply (l6_21 A M N M); Col.
    apply col_permutation_3, per_per_col with A; Col.
  - apply per_col with A; Col.
    apply l8_2, per_col with M; Col; Perp.
  - apply l8_2, per_col with A; Col.
  - apply l11_17 with M N A; auto.
    apply (out_conga M N A M L B); auto; try (apply out_trivial; auto).
    apply bet_out; Between.
Qed.

Lemma t22_23 : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C M N L, ~ Col A M N -> Per B C A -> A <> C -> Midpoint M A B ->
  Per M N A -> Col A C N -> Midpoint M N L ->
  Bet A N C /\ Le N C A N /\ Le L N B C.
Proof.
  intros HNob A B C M N L HNCol HPerC HAC HM HPerN HColN HN.
  destruct (t22_23_aux A B C M N L) as [HBet [HLam HCong]]; auto.
  split; auto.
  assert (HLBC : ~ Obtuse L B C) by (intro; apply HNob, (lam_obtuse__oah N L B C); trivial).
  assert (Hos1 : OS N L B C) by (apply lam__os; trivial).
  assert (Hos2 : OS N C B L) by (apply lam__os, lam_perm; trivial).
  unfold Lambert in HLam; spliter.
  destruct (angle_partition L B C) as [HAcute | [HPer | HObtuse]]; trivial; [ | | exfalso; auto].
  - split; apply lt__le; [apply (cong2_lt__lt N C B L); Cong | ].
      apply lta_per2_os__lt; Perp; Side; apply lta_left_comm, acute_per__lta; auto.
    apply lt_left_comm, lta_per2_os__lt; Side; apply acute_per__lta; auto.
  - split; apply cong__le; [apply cong_transitivity with B L; trivial | apply cong_left_commutativity];
    apply conga_per2_os__cong; Perp; Side; apply l11_16; Perp.
Qed.

(** for every n, 2^n times B0C0 is lower than or equal to BnCn *)
(** B0 is introduced twice for the induction tactic to work properly *)
Lemma t22_24_aux : ~ hypothesis_of_obtuse_saccheri_quadrilaterals -> forall A B0 B00 C0 B C E, 
  ~ Col A B0 C0 -> Perp A C0 B0 C0 -> B0 = B00 ->
  GradExp2 A B0 B B00 C0 E -> Perp A C0 B C -> Col A C0 C ->
  Le B0 E B C.
Proof.
  intros HNob A B0 B00 C0 B C E HNCol HPerp0 Heq HGE.
  revert C.
  induction HGE; rename B into B0; rename D into B00; rename E into C0; subst B00.
    intros C HPerp HCol; assert (C = C0) by (apply (l8_18_uniqueness A C0 B0); Col); subst C; Le.
  rename C into B; rename C' into B'; rename F into E; rename F' into E'.
  intros C' HPerp' HCol'.
  apply gradexp2__gradexp123, gradexp__grad, grad__bet in HGE.
  destruct (l8_18_existence A C0 B) as [C [HCol HPerp]].
    intro; assert_diffs; apply HNCol; ColR.
  assert (HLe : Le B0 E B C) by (apply IHHGE; trivial).
  clear IHHGE.
  destruct (symmetric_point_construction C B) as [D HD].
  apply le_transitivity with D C.
    apply bet2_le2__le1346 with E B; Between; apply (cong_preserves_le B0 E B C); auto with cong.
  assert (HAC : A <> C).
  { intro; subst C; assert_diffs; assert (A = C0); auto.
    apply (l8_18_uniqueness A C0 B0); Col.
    apply perp_right_comm, perp_col1 with B; Perp; Col.
  }
  assert (HAC' : A <> C').
  { intro; subst C'; assert_diffs; assert (A = C0); auto.
    apply (l8_18_uniqueness A C0 B0); Col.
    apply perp_right_comm, perp_col1 with B'; Perp; ColR.
  }
  assert (HPer : Per A C B) by (apply perp_per_1; auto; apply perp_left_comm, perp_col with C0; trivial).
  destruct (t22_23 HNob A B' C' B C D) as [_ []]; Perp; assert_diffs.
  - apply per_not_col in HPer; Col.
  - apply perp_per_1; auto; apply perp_col1 with C0; Perp.
  - split; auto.
  - ColR.
Qed.

(** for every n, it is possible to get Bn and Cn *) 
Lemma t22_24_aux1 : forall A B0 C0 E, ~ Col A B0 C0 -> Perp A C0 B0 C0 -> GradExp B0 C0 E ->
  exists B C, GradExp2 A B0 B B0 C0 E /\ Perp A C0 B C /\ Col A C0 C.
Proof.
  intros A B0 C0 E HNCol HPerp0 HGE.
  induction HGE; rename A0 into B0; rename B into C0.
    exists B0; exists C0; repeat (split; Col); apply gradexp2_init.
  rename C into E; rename C' into E'.
  destruct IHHGE as [B [C [HGE2 [HPerp HCol]]]]; trivial.
  destruct (segment_construction A B A B) as [B' [HBet HCong]].
  exists B'.
  destruct (l8_18_existence A C0 B') as [C' [HCol' HPerp']].
    apply gradexp2__gradexp123, gradexp__grad, grad__bet in HGE2; intro; assert_diffs; apply HNCol; ColR. 
  exists C'; repeat (split; trivial); apply gradexp2_stab with B E; Cong.
Qed.

Lemma t22_24 : archimedes_postulate -> aristotle_s_postulate.
Proof.
  intros Harchi P Q D A B0 HNCol HACute0.
  destruct (l8_18_existence A D B0) as [C0 [HColD HPerpD]]; Col.
  assert (HAC0 : A <> C0) by (intro; subst C0; apply (acute_not_per D A B0); Perp).
  assert (HNCol0 : ~ Col A B0 C0) by (intro; apply HNCol; ColR).
  assert (HPerp0 := perp_col A D B0 C0 C0 HAC0 HPerpD HColD).
  elim (eq_dec_points P Q); intro HPQ.
  { subst Q; exists C0; exists B0; split; assert_diffs.
      apply l6_6, acute_col_perp__out with B0; trivial; apply acute_sym; trivial.
    split.
      apply out_trivial; auto.
    repeat split; Perp; Le.
    intro; treat_equalities; auto.
  }
  destruct (segment_construction P Q P Q) as [Q' [HBetQ HCongQ]].
  destruct (reach__ex_gradexp_le B0 C0 P Q') as [E [HGE HLe]].
    assert_diffs; apply Harchi; trivial.
  destruct (t22_24_aux1 A B0 C0 E) as [B [C [HGE2 [HPerp HCol]]]]; trivial.
  assert(HOut : Out A B0 B).
    apply gradexp2__gradexp123, gradexp__grad, grad__bet in HGE2; assert_diffs; apply bet_out; auto.
  assert(HAcute : Acute D A B).
    apply (acute_conga__acute D A B0); trivial.
    assert_diffs; apply (out_conga D A B0 D A B0); CongA; apply out_trivial; auto.
  assert (HAC : A <> C) .
    intro; subst C; assert_diffs; apply (acute_not_per D A B); trivial.
    apply perp_per_1; auto; apply perp_col with C0; Col.
  exists C; exists B; split.
    assert_diffs; apply l6_6, acute_col_perp__out with B; [apply acute_sym; trivial|ColR|apply perp_col with C0; Col].
  split; trivial; split.
    apply perp_per_1; auto; apply perp_left_comm, perp_col with C0; trivial.
  apply le3456_lt__lt with P Q'.
  split.
    apply bet__le1213; trivial.
    intro; assert (Q = Q'); treat_equalities; auto.
    apply between_cong with P; trivial.
  apply le_transitivity with B0 E; trivial.
  apply le_right_comm.
  apply t22_24_aux with A B0 C0; trivial.
  apply archi__obtuse_case_elimination; trivial.
Qed.


End Archimedes.