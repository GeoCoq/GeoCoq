Require Export GeoCoq.Tarski_dev.Ch04_col.

Section T5.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l5_1 : forall A B C D,
  A <> B -> Bet A B C -> Bet A B D -> Bet A C D \/ Bet A D C.
Proof.
    intros.
    prolong A D C' C D.
    prolong A C D' C D.
    prolong A C' B' C B.
    prolong A D' B'' D B.
    assert (Cong B C' B'' C).
      apply (l2_11 B D C' B'' D' C).
        apply between_exchange3 with A; Between.
        apply between_inner_transitivity with A; Between.
        Cong.
      apply cong_transitivity with C D; Cong.
    assert (Cong B B' B'' B).
      {
      apply (l2_11 B C' B' B'' C B); Cong.

        {
        assert (Bet A B C'); [|eBetween].
        induction (eq_dec_points B D); [treat_equalities; auto|].
        apply between_symmetry.
        apply outer_transitivity_between2 with D; eBetween.
        }

        {
        induction (eq_dec_points C D'); [treat_equalities; eBetween|].
        apply outer_transitivity_between2 with D'; eBetween.
        }
      }
    assert(B'' =  B').
      apply (construction_uniqueness A B B B''); Cong.
        apply between_exchange4 with D'; Between;
        apply between_exchange4 with C; Between.
      apply between_exchange4 with C'; Between;
      apply between_exchange4 with D; Between.
    subst B''.
    assert (Bet B C D') by (apply between_exchange3 with A; assumption).
    assert (FSC B C D' C' B' C' D C).
      repeat split; Cong.
        left; apply between_exchange3 with A; Between.
        apply (l2_11 B C D' B' C' D); Cong.
          apply between_symmetry.
          apply between_exchange3 with A; assumption.
        apply cong_transitivity with C D; Cong.
      apply cong_transitivity with C D; Cong.
    induction (eq_dec_points B C).
      subst C; auto.
    assert (Cong D' C' D C) by (eapply l4_16; try apply H13; assumption).
    assert (exists E, Bet C E C' /\ Bet D E D') by (apply inner_pasch with A; Between).
    ex_and H16 E.
    assert (IFSC D E D' C D E D' C') by (unfold IFSC; repeat split; Cong; apply cong_transitivity with C D; Cong).
    assert (IFSC C E C' D C E C' D') by (unfold IFSC; repeat split; Cong; apply cong_transitivity with C D; Cong).
    assert (Cong E C E C') by (eapply l4_2; try apply H18; auto).
    assert (Cong E D E D') by (eapply l4_2; try apply H19; auto).
    induction (eq_dec_points C C').
      subst C'; right; assumption.
    show_distinct C D'.
      auto.
    prolong C' C P C D'.
    prolong D' C R C E.
    prolong P R Q R P.
    assert (FSC D' C R P P C E D').
      repeat split; Col; Cong.
      apply l2_11 with C C; Cong.
      apply between_inner_transitivity with C'; Between.
    assert (Cong R P E D') by (eauto using l4_16).
    assert (Cong R Q E D).
      eapply cong_transitivity.
        apply cong_transitivity with R P; Cong.
      apply cong_transitivity with E D'; Cong.
    assert (FSC D' E D C P R Q C).
      repeat split; Col; Cong.
      eapply (l2_11 D' E D P R Q); Between; Cong.
    assert (Cong D C Q C).
      induction (eq_dec_points D' E).
        unfold IFSC, Cong_3 in *; spliter; treat_equalities; Cong.
      apply l4_16 with D' E P R; assumption.
    assert (Cong C P C Q).
      unfold FSC, Cong_3 in *; spliter.
      apply cong_transitivity with C D; Cong.
      apply cong_transitivity with C D'; Cong.
    show_distinct R C.
      auto.
    assert (Cong D' P D' Q) by (apply (l4_17 R C); unfold Col; Between; Cong).
    assert (Cong B P B Q).
      apply l4_17 with C D'; Col.
    assert (Cong B' P B' Q).
      apply (l4_17 C D'); Cong.
      left.
      apply between_exchange3 with A; assumption.
    assert (Cong C' P C' Q).
      assert (Bet B C' B').
        apply between_exchange3 with A; try assumption.
        apply between_exchange4 with D; try assumption.
      eapply l4_17 with B B'; Cong; Col.
      intro; treat_equalities; auto.
    assert (Cong P P P Q).
      apply l4_17 with C C'; Col.
    treat_equalities.
    left; assumption.
Qed.

Lemma l5_2 : forall A B C D,
  A <> B -> Bet A B C -> Bet A B D -> Bet B C D \/ Bet B D C.
Proof.
    intros.
    assert (Bet A C D \/ Bet A D C) by (eapply l5_1; eauto).
    induction H2.
    left; eBetween.
    right; eBetween.
Qed.

Lemma segment_construction_2 :
  forall A Q B C, A <> Q -> exists X, (Bet Q A X \/ Bet Q X A) /\ Cong Q X B C.
Proof.
    intros.
    prolong A Q A' A Q.
    prolong A' Q X B C.
    exists X.
    show_distinct A' Q.
    solve [intuition].
    split; try assumption.
    eapply (l5_2 A' Q); Between.
Qed.

Lemma l5_3 : forall A B C D,
 Bet A B D -> Bet A C D -> Bet A B C \/ Bet A C B.
Proof.
    intros.
    assert (exists P, Bet D A P /\ A<>P) by  (apply point_construction_different).
    ex_and H1 P.
    assert (Bet P A B) by eBetween.
    assert (Bet P A C) by eBetween.
    apply (l5_2 P);auto.
Qed.

Lemma bet3__bet : forall A B C D E, Bet A B E -> Bet A D E -> Bet B C D -> Bet A C E.
Proof.
    intros.
    destruct (l5_3 A B D E H H0).
      apply between_exchange4 with D; trivial.
      apply between_exchange2 with B; assumption.
    apply between_exchange4 with B; trivial.
    apply between_exchange2 with D; Between.
Qed.

Lemma le_bet : forall A B C D, Le C D A B -> exists X, Bet A X B /\ Cong A X C D.
Proof.
    intros.
    unfold Le in H.
    ex_and H Y.
    exists Y;split;Cong.
Qed.

Lemma l5_5_1 : forall A B C D,
  Le A B C D -> exists x, Bet A B x /\ Cong A x C D.
Proof.
    unfold Le.
    intros.
    ex_and H P.
    prolong A B x P D.
    exists x.
    split.
      assumption.
    eapply l2_11;eauto.
Qed.

Lemma l5_5_2 : forall A B C D,
 (exists x, Bet A B x /\ Cong A x C D) -> Le A B C D.
Proof.
    intros.
    ex_and H P.
    unfold Le.
    assert (exists B' : Tpoint, Bet C B' D /\ Cong_3 A B P C B' D) by (eapply l4_5;auto).
    ex_and H1 y.
    exists y.
    unfold Cong_3 in *;intuition.
Qed.

Lemma l5_6 : forall A B C D A' B' C' D',
 Le A B C D -> Cong A B A' B' -> Cong C D C' D' -> Le A' B' C' D'.
Proof.
    unfold Le.
    intros.
    spliter.
    ex_and H y.
    assert (exists z : Tpoint, Bet C' z D' /\ Cong_3 C y D C' z D') by (eapply l4_5;auto).
    ex_and H3 z.
    exists z.
    split.
      assumption.
    unfold Cong_3 in *; spliter.
    apply cong_transitivity with A B; Cong.
    apply cong_transitivity with C y; assumption.
Qed.

Lemma le_reflexivity : forall A B, Le A B A B.
Proof.
    unfold Le.
    intros.
    exists B.
    split; Between; Cong.
Qed.

Lemma le_transitivity : forall A B C D E F, Le A B C D -> Le C D E F -> Le A B E F.
Proof.
    unfold Le.
    intros.
    ex_and H y.
    ex_and H0 z.
    assert (exists P : Tpoint, Bet E P z /\ Cong_3 C y D E P z) by (eapply l4_5;assumption).
    ex_and H3 P.
    exists P.
    split.
      eBetween.
    unfold Cong_3 in H4; spliter; apply cong_transitivity with C y; Cong.
Qed.

Lemma between_cong : forall A B C, Bet A C B -> Cong A C A B -> C = B.
Proof.
    intros.
    assert (Bet A B C).
    eapply l4_6 with A C B; unfold Cong_3; repeat split; Cong.
    eapply between_equality; eBetween.
Qed.

Lemma cong3_symmetry : forall A B C A' B' C' : Tpoint , Cong_3 A B C A' B' C' -> Cong_3 A' B' C' A B C.
Proof.
    unfold Cong_3.
    intros.
    intuition.
Qed.

Lemma between_cong_2 : forall A B D E, Bet A D B -> Bet A E B -> Cong A D A E -> D = E.
Proof.
    intros.
    apply cong3_bet_eq with A B; unfold Cong_3; repeat split; Cong.
    eapply (l4_2 B E A B B D A B).
    unfold IFSC; repeat split; Cong; Between.
Qed.

Lemma between_cong_3 :
  forall A B D E, A <> B -> Bet A B D -> Bet A B E -> Cong B D B E -> D = E.
Proof.
    intros.
    assert (T:=l5_2 A B D E H H0 H1).
    elim T; intro; clear T.
    apply between_cong with B; Cong.
    symmetry; apply between_cong with B; Cong.
Qed.

Lemma le_anti_symmetry : forall A B C D, Le A B C D -> Le C D A B -> Cong A B C D.
Proof.
    intros.
    assert (exists T, Bet C D T /\ Cong C T A B) by (apply l5_5_1;assumption).
    unfold Le in H.
    ex_and H Y.
    ex_and H1 T.
    assert (Cong C Y C T) by eCong.
    assert (Bet C Y T) by eBetween.
    assert (Y=T) by (eapply between_cong;eauto).
    subst Y.
    assert (T=D) by (eapply between_equality;eBetween).
    subst T.
    Cong.
Qed.

Lemma cong_dec : forall A B C D,
  Cong A B C D \/ ~ Cong A B C D.
Proof.
    intros.
    elim (eq_dec_points A B); intro; subst; elim (eq_dec_points C D); intro; subst.
    left; Cong.
    right; intro; apply H; apply cong_identity with B; Cong.
    right; intro; apply H; apply cong_identity with D; Cong.
    elim (segment_construction_2 B A C D).
    intros D' HD'.
    spliter.
    elim (eq_dec_points B D');intro.
    subst; left; assumption.
    right; intro.
    assert (Cong A D' A B) by CongR.
    elim H1; intro; clear H1.
    assert (B = D') by (apply (between_cong A D' B); Cong).
    subst;intuition.
    assert (D'=B) by (apply (between_cong A B D');assumption).
    subst;intuition.
    intuition.
Qed.

Lemma bet_dec : forall A B C, Bet A B C  \/  ~ Bet A B C.
Proof.
    intros.
    elim (segment_construction A B B C); intros C' HC'.
    spliter.
    elim (eq_dec_points C C'); intro.
    subst; tauto.
    elim (eq_dec_points A B);intro.
    left; subst; Between.
    right; intro; apply H1; apply between_cong_3 with A B; Cong.
Qed.

Lemma col_dec : forall A B C, Col A B C \/ ~ Col A B C.
Proof.
    intros.
    unfold Col.
    elim (bet_dec A B C); intro; elim (bet_dec B C A); intro; elim (bet_dec C A B); intro; tauto.
Qed.


Lemma le_trivial : forall A C D, Le A A C D .
Proof.
    intros.
    unfold Le.
    exists C.
    split; Between; Cong.
Qed.

Lemma le_cases : forall A B C D, Le A B C D \/ Le C D A B.
Proof.
    intros.
    induction(eq_dec_points A B).
      subst B; left; apply le_trivial.
    assert (exists X : Tpoint, (Bet A B X \/ Bet A X B) /\ Cong A X C D) by (eapply (segment_construction_2 B A C D);auto).
    ex_and H0 X.
    induction H0.
      left; apply l5_5_2; exists X; split; assumption.
    right; unfold Le; exists X; split; Cong.
Qed.

Lemma le_zero : forall A B C, Le A B C C -> A=B.
Proof.
    intros.
    assert (Le C C A B) by apply le_trivial.
    assert (Cong A B C C) by (apply le_anti_symmetry;assumption).
    treat_equalities;auto.
Qed.

Lemma le_diff : forall A B C D, A <> B -> Le A B C D -> C <> D.
Proof.
  intros A B C D HAB HLe Heq.
  subst D; apply HAB, le_zero with C; assumption.
Qed.

Lemma lt_diff : forall A B C D, Lt A B C D -> C <> D.
Proof.
  intros A B C D HLt Heq.
  subst D.
  destruct HLt as [HLe HNCong].
  assert (A = B) by (apply le_zero with C; assumption).
  subst B; Cong.
Qed.

Lemma bet_cong_eq :
 forall A B C D,
  Bet A B C ->
  Bet A C D ->
  Cong B C A D ->
  C = D /\ A = B.
Proof.
    intros.
    assert(C = D).
      assert(Le A C A D) by (eapply l5_5_2; exists D; split; Cong).
      assert(Le C B C A) by (eapply l5_5_2; exists A; split; Between; Cong).
      assert(Cong A C A D) by (eapply le_anti_symmetry; try assumption; apply l5_6 with C B C A; Cong).
      apply between_cong with A; assumption.
    split; try assumption.
    subst D; apply sym_equal.
    eapply (between_cong C); Between; Cong.
Qed.

Lemma cong__le : forall A B C D, Cong A B C D -> Le A B C D.
Proof.
  intros A B C D H.
  exists D.
  split.
  Between.
  Cong.
Qed.

Lemma cong__le3412 : forall A B C D, Cong A B C D -> Le C D A B.
Proof.
  intros A B C D HCong.
  apply cong__le.
  Cong.
Qed.

Lemma le1221 : forall A B, Le A B B A.
Proof.
  intros A B.
  apply cong__le; Cong.
Qed.

Lemma le_left_comm : forall A B C D, Le A B C D -> Le B A C D.
Proof.
  intros A B C D Hle.
  apply (le_transitivity _ _ A B); auto.
  apply le1221; auto.
Qed.

Lemma le_right_comm : forall A B C D, Le A B C D -> Le A B D C.
Proof.
  intros A B C D Hle.
  apply (le_transitivity _ _ C D); auto.
  apply le1221; auto.
Qed.

Lemma le_comm : forall A B C D, Le A B C D -> Le B A D C.
Proof.
  intros.
  apply le_left_comm.
  apply le_right_comm.
  assumption.
Qed.

Lemma ge_left_comm : forall A B C D, Ge A B C D -> Ge B A C D.
Proof.
    intros.
    unfold Ge in *.
    apply le_right_comm.
    assumption.
Qed.

Lemma ge_right_comm : forall A B C D, Ge A B C D -> Ge A B D C.
Proof.
    intros.
    unfold Ge in *.
    apply le_left_comm.
    assumption.
Qed.

Lemma ge_comm :  forall A B C D, Ge A B C D -> Ge B A D C.
Proof.
    intros.
    apply ge_left_comm.
    apply ge_right_comm.
    assumption.
Qed.

Lemma lt_right_comm : forall A B C D, Lt A B C D -> Lt A B D C.
Proof.
    intros.
    unfold Lt in *.
    spliter.
    split.
      apply le_right_comm.
      assumption.
    intro.
    apply H0.
    apply cong_right_commutativity.
    assumption.
Qed.

Lemma lt_left_comm : forall A B  C D, Lt A B C D -> Lt B A C D.
Proof.
    intros.
    unfold Lt in *.
    spliter.
    split.
      unfold Le in *.
      ex_and H P.
      exists P.
      apply cong_left_commutativity in H1.
      split; assumption.
    intro.
    apply H0.
    apply cong_left_commutativity.
    assumption.
Qed.

Lemma lt_comm : forall A B  C D, Lt A B C D -> Lt B A D C.
Proof.
    intros.
    apply lt_left_comm.
    apply lt_right_comm.
    assumption.
Qed.

Lemma gt_left_comm : forall A B C D, Gt A B C D -> Gt B A C D.
Proof.
    intros.
    unfold Gt in *.
    apply lt_right_comm.
    assumption.
Qed.

Lemma gt_right_comm : forall A B C D, Gt A B C D -> Gt A B D C.
Proof.
    intros.
    unfold Gt in *.
    apply lt_left_comm.
    assumption.
Qed.

Lemma gt_comm : forall A B C D, Gt A B C D -> Gt B A D C.
Proof.
    intros.
    apply gt_left_comm.
    apply gt_right_comm.
    assumption.
Qed.

Lemma cong2_lt__lt : forall A B C D A' B' C' D',
 Lt A B C D -> Cong A B A' B' -> Cong C D C' D' -> Lt A' B' C' D'.
Proof.
  intros A B C D A' B' C' D' Hlt HCong1 HCong2.
  destruct Hlt as [Hle HNCong].
  split.
  apply (l5_6 A B C D); auto.
  intro.
  apply HNCong.
  apply (cong_transitivity _ _ A' B'); auto.
  apply (cong_transitivity _ _ C' D'); Cong.
Qed.

Lemma fourth_point : forall A B C P, A <> B -> B <> C -> Col A B P -> Bet A B C ->
  Bet P A B \/ Bet A P B \/ Bet B P C \/ Bet B C P.
Proof.
    intros.
    induction H1.
      assert(HH:= l5_2 A B C P H H2 H1).
      right; right.
      induction HH.
        right; auto.
      left; auto.
    induction H1.
      right; left.
      Between.
    left; auto.
Qed.

Lemma third_point : forall A B P, Col A B P -> Bet P A B \/ Bet A P B \/ Bet A B P.
Proof.
    intros.
    induction H.
      right; right.
      auto.
    induction H.
      right; left.
      Between.
    left.
    auto.
Qed.

Lemma l5_12_a : forall A B C, Bet A B C -> Le A B A C /\ Le B C A C.
Proof.
    intros.
    split.
      unfold Le.
      exists B; split.
        assumption.
      apply cong_reflexivity.
    apply le_comm.
    unfold Le.
    exists B.
    split.
      apply between_symmetry.
      assumption.
    apply cong_reflexivity.
Qed.

Lemma bet__le1213 : forall A B C, Bet A B C -> Le A B A C.
Proof.
    intros A B C HBet.
    destruct (l5_12_a A B C HBet); trivial.
Qed.

Lemma bet__le2313 : forall A B C, Bet A B C -> Le B C A C.
Proof.
    intros A B C HBet.
    destruct (l5_12_a A B C HBet); trivial.
Qed.

Lemma bet__lt1213 : forall A B C, B <> C -> Bet A B C -> Lt A B A C.
Proof.
    intros A B C HBC HBet.
    split.
      apply bet__le1213; trivial.
    intro.
    apply HBC, between_cong with A; trivial.
Qed.

Lemma bet__lt2313 : forall A B C, A <> B -> Bet A B C -> Lt B C A C.
Proof.
    intros; apply lt_comm, bet__lt1213; Between.
Qed.

Lemma l5_12_b : forall A B C, Col A B C -> Le A B A C -> Le B C A C -> Bet A B C.
Proof.
    intros.
    unfold Col in H.
    induction H.
      assumption.
    induction H.
      assert(Le B C B A /\ Le C A B A).
        apply l5_12_a.
          assumption.
      spliter.
      assert(Cong A B A C).
        apply le_anti_symmetry.
          assumption.
        apply le_comm.
        assumption.
      assert(C = B).
        eapply between_cong.
          apply between_symmetry.
          apply H.
        apply cong_symmetry.
        assumption.
      subst B.
      apply between_trivial.
    assert(Le B A B C /\ Le A C B C).
      apply l5_12_a.
        apply between_symmetry.
        assumption.
    spliter.
    assert(Cong B C A C).
      apply le_anti_symmetry.
        assumption.
      assumption.
    assert(A = B).
      eapply between_cong.
        apply H.
      apply cong_symmetry.
      apply cong_commutativity.
      assumption.
    subst A.
    apply between_symmetry.
    apply between_trivial.
Qed.

Lemma bet_le_eq : forall A B C, Bet A B C -> Le A C B C -> A = B.
Proof.
    intros.
    assert(Le C B C A).
      eapply l5_5_2.
      exists A.
      split.
        apply between_symmetry.
        assumption.
      apply cong_reflexivity.
    assert(Cong A C B C).
      apply le_anti_symmetry.
        assumption.
      apply le_comm.
      assumption.
    apply sym_equal.
    eapply between_cong.
      apply between_symmetry.
      apply H.
    apply cong_commutativity.
    apply cong_symmetry.
    assumption.
Qed.

Lemma or_lt_cong_gt : forall A B C D, Lt A B C D \/ Gt A B C D \/ Cong A B C D.
Proof.
    intros.
    assert(HH:= le_cases A B C D).
    induction HH.
      induction(cong_dec A B C D).
        right; right.
        assumption.
      left.
      unfold Lt.
      split; assumption.
    induction(cong_dec A B C D).
      right; right.
      assumption.
    right; left.
    unfold Gt.
    unfold Lt.
    split.
      assumption.
    intro.
    apply H0.
    apply cong_symmetry.
    assumption.
Qed.

Lemma lt__le : forall A B C D, Lt A B C D -> Le A B C D.
Proof.
    intros A B C D Hlt.
    destruct Hlt.
    assumption.
Qed.

Lemma le1234_lt__lt : forall A B C D E F, Le A B C D -> Lt C D E F -> Lt A B E F.
Proof.
    intros A B C D E F Hle Hlt.
    destruct Hlt as [Hle' HNCong].
    split.
      apply (le_transitivity _ _ C D); auto.
    intro.
    apply HNCong.
    apply le_anti_symmetry; auto.
    apply (l5_6 A B C D); Cong.
Qed.

Lemma le3456_lt__lt : forall A B C D E F, Lt A B C D -> Le C D E F -> Lt A B E F.
Proof.
    intros A B C D E F Hlt Hle.
    destruct Hlt as [Hle' HNCong].
    split.
      apply (le_transitivity _ _ C D); auto.
    intro.
    apply HNCong.
    apply le_anti_symmetry; auto.
    apply (l5_6 C D E F); Cong.
Qed.

Lemma lt_transitivity : forall A B C D E F, Lt A B C D -> Lt C D E F -> Lt A B E F.
Proof.
    intros A B C D E F HLt1 HLt2.
    apply le1234_lt__lt with C D; try (apply lt__le); assumption.
Qed.

Lemma not_and_lt : forall A B C D, ~ (Lt A B C D /\ Lt C D A B).
Proof.
    intros A B C D.
    intro HInter.
    destruct HInter as [[Hle HNCong] []].
    apply HNCong.
    apply le_anti_symmetry; assumption.
Qed.

Lemma nlt : forall A B, ~ Lt A B A B.
Proof.
    intros A B Hlt.
    apply (not_and_lt A B A B).
    split; assumption.
Qed.

Lemma le__nlt : forall A B C D, Le A B C D -> ~ Lt C D A B.
Proof.
    intros A B C D HLe HLt.
    apply (not_and_lt A B C D); split; auto.
    split; auto.
    unfold Lt in *; spliter; auto with cong.
Qed.

Lemma cong__nlt : forall A B C D,
 Cong A B C D -> ~ Lt A B C D.
Proof.
    intros P Q R S H.
    apply le__nlt.
    unfold Le.
    exists Q; split; Cong; Between.
Qed.

Lemma nlt__le : forall A B C D, ~ Lt A B C D -> Le C D A B.
Proof.
    intros A B C D HNLt.
    destruct (le_cases A B C D); trivial.
    destruct (cong_dec C D A B).
      apply cong__le; assumption.
    exfalso.
    apply HNLt.
    split; Cong.
Qed.

Lemma lt__nle : forall A B C D, Lt A B C D -> ~ Le C D A B.
Proof.
    intros A B C D HLt HLe.
    revert HLt.
    apply le__nlt; assumption.
Qed.

Lemma nle__lt : forall A B C D, ~ Le A B C D -> Lt C D A B.
Proof.
    intros A B C D HNLe.
    destruct (le_cases A B C D).
      contradiction.
    split; trivial.
    intro.
    apply HNLe.
    apply cong__le; Cong.
Qed.

Lemma lt1123 : forall A B C, B<>C -> Lt A A B C.
Proof.
intros.
split.
apply le_trivial.
intro.
treat_equalities.
intuition.
Qed.

Lemma bet2_le2__le : forall O o A B a b, Bet a o b -> Bet A O B -> Le o a O A -> Le o b O B -> Le a b A B.
Proof.
intros.
induction(eq_dec_points A O).
treat_equalities; auto.
assert (o=a). 
apply le_zero with A;auto.
subst;auto.
induction(eq_dec_points B O).
treat_equalities;auto.
assert (o=b). 
apply le_zero with B;auto.
subst;auto using le_left_comm, le_right_comm.


assert(HH:= segment_construction A O b o).
ex_and HH b'.
assert(HH:= segment_construction B O a o).
ex_and HH a'.

unfold Le in H1.
ex_and H1 a''.

assert(a' = a'').
{
  apply(construction_uniqueness B O a o a' a'' H4);
  eBetween.
  Cong.
}
treat_equalities.

assert(Le B a' B A).
{
  unfold Le.
  exists a'.
  split; eBetween; Cong.
}

unfold Le in H2.
ex_and H2 b''.

assert(b' = b'').
{
  apply(construction_uniqueness A O b o b' b'' H3);
  eBetween.
  Cong.
}

treat_equalities.

assert(Le a' b' a' B).
{
  unfold Le.
  exists b'.
  split; eBetween; Cong.
}

assert(Le a' b' A B).
{
  apply(le_transitivity a' b' a' B A B); auto using le_left_comm, le_right_comm.
}

apply(l5_6 a' b' A B a b A B); Cong.
apply (l2_11 a' O b' a o b);
eBetween; Cong.
Qed.

Lemma Le_cases : forall A B C D, Le A B C D \/ Le B A C D \/ Le A B D C \/ Le B A D C -> Le A B C D.
Proof.
    intros A B C D [|[|[|]]]; [|apply le_left_comm|apply le_right_comm|apply le_comm]; assumption.
Qed.

Lemma Lt_cases : forall A B C D, Lt A B C D \/ Lt B A C D \/ Lt A B D C \/ Lt B A D C -> Lt A B C D.
Proof.
    intros A B C D [|[|[|]]]; [|apply lt_left_comm|apply lt_right_comm|apply lt_comm]; assumption.
Qed.

End T5.

#[global]
Hint Resolve le_reflexivity le_anti_symmetry le_trivial le_zero cong__le cong__le3412
             le1221 le_left_comm le_right_comm le_comm lt__le bet__le1213 bet__le2313
             lt_left_comm lt_right_comm lt_comm bet__lt1213 bet__lt2313 lt1123 : le.

Ltac Le := auto with le.
