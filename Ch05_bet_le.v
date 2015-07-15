Require Export Ch04_col.

Section T5.

Context `{M:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma l5_1 : forall A B C D,
 A<>B -> Bet A B C -> Bet A B D -> Bet A C D \/ Bet A D C.
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
    assert (Cong B B' B'' B) by (apply (l2_11 B C' B' B'' C B); eBetween; Cong).
    assert(B'' =  B').
      apply (construction_unicity A B B B''); try Cong.
        apply between_exchange4 with D'; Between; apply between_exchange4 with C; Between.
      apply between_exchange4 with C'; Between; apply between_exchange4 with D; Between.
    subst B''.
    assert (FSC B C D' C' B' C' D C).
      unfold FSC.
      repeat split; unfold Col; try Cong.
        left; apply between_exchange3 with A; Between.
        apply (l2_11 B C D' B' C' D); Cong.
          apply between_exchange3 with A; assumption.
          apply between_symmetry.
          apply between_exchange3 with A; assumption.
        apply cong_transitivity with C D; Cong.
      apply cong_transitivity with C D; Cong.
    induction (eq_dec_points B C).
      subst C; auto.
    assert (Cong D' C' D C) by (eapply l4_16; try apply H12; assumption).
    assert (exists E, Bet C E C' /\ Bet D E D') by (apply inner_pasch with A; Between).
    ex_and H15 E.
    assert (IFSC D E D' C D E D' C') by (unfold IFSC; repeat split; Cong; apply cong_transitivity with C D; Cong).
    assert (IFSC C E C' D C E C' D') by (unfold IFSC; repeat split; Cong; apply cong_transitivity with C D; Cong).
    assert (Cong E C E C') by (eapply l4_2;apply H17).
    assert (Cong E D E D') by (eapply l4_2;apply H18).
    induction (eq_dec_points C C').
      subst C'; right; assumption.
    show_distinct C D'; intuition.
    prolong C' C P C D'.
    prolong D' C R C E.
    prolong P R Q R P.
    assert (FSC D' C R P P C E D').
      unfold FSC.
      unfold Cong_3.
      assert_cols.
      repeat split; Cong.
      apply l2_11 with C C; Cong.
      apply between_inner_transitivity with C'; Between.
    assert (Cong R P E D') by (eauto using l4_16).
    assert (Cong R Q E D).
      eapply cong_transitivity.
        apply cong_transitivity with R P; Cong.
      apply cong_transitivity with E D'; Cong.
    assert (FSC D' E D C P R Q C).
      unfold FSC.
      repeat split; Cong.
        unfold Col; Between.
      eapply (l2_11 D' E D P R Q); Between; Cong.
    assert (Cong D C Q C).
      induction (eq_dec_points D' E).
        unfold FSC, IFSC, Cong_3 in *; spliter; treat_equalities; Cong.
      apply l4_16 with D' E P R; assumption.
    assert (Cong C P C Q).
      unfold FSC in *;unfold Cong_3 in *.
      spliter.
      apply cong_transitivity with C D.
        apply cong_transitivity with C D'; Cong.
      Cong.
    show_distinct R C.
      intuition.
    assert (Cong D' P D' Q) by (apply (l4_17 R C); unfold Col; Between; Cong).
    assert (Cong B P B Q).
      apply l4_17 with C D'; try assumption.
      unfold Col; right;right.
      apply between_exchange3 with A; assumption.
    assert (Cong B' P B' Q).
      eapply (l4_17 C D'); Cong.
      unfold Col; left.
      apply between_exchange3 with A; assumption.
    assert (Cong C' P C' Q).
      induction(eq_dec_points B B').
        subst B'.
        unfold IFSC,FSC, Cong_3 in *.
        spliter.
        clean_duplicated_hyps.
        clean_trivial_hyps.
        apply l4_17 with C D'; try assumption.
        unfold Col; left.
        apply between_exchange3 with A; try assumption.
        apply between_exchange4 with B; try assumption.
        apply between_exchange4 with D; assumption.
      eapply l4_17 with B B'; Cong.
      unfold Col; right; left.
      apply between_symmetry.
      apply between_exchange3 with A; try assumption.
      apply between_exchange4 with D; assumption.
    assert (Cong P P P Q).
      apply l4_17 with C C'; try assumption.
      unfold Col; right; right.
      apply between_symmetry; assumption.
    unfold IFSC,FSC, Cong_3 in *; spliter.
    treat_equalities.
    Between.
Qed.

Lemma l5_2 : forall A B C D,
 A<>B -> Bet A B C -> Bet A B D -> Bet B C D \/ Bet B D C.
Proof.
    intros.
    assert (Bet A C D \/ Bet A D C) by (eapply l5_1; eauto).
    induction H2.
      left; eBetween.
    right; eBetween.
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

Definition le := fun A B C D =>
   exists y, Bet C y D /\ Cong A B C y.

Definition ge := fun A B C D => le C D A B.

Lemma l5_5_1 : forall A B C D,
  le A B C D -> exists x, Bet A B x /\ Cong A x C D.
Proof.
    unfold le.
    intros.
    ex_and H P.
    prolong A B x P D.
    exists x.
    split.
      assumption.
    eapply l2_11;eauto.
Qed.

Lemma l5_5_2 : forall A B C D,
 (exists x, Bet A B x /\ Cong A x C D) -> le A B C D.
Proof.
    intros.
    ex_and H P.
    unfold le.
    assert (exists B' : Tpoint, Bet C B' D /\ Cong_3 A B P C B' D) by (eapply l4_5;auto).
    ex_and H1 y.
    exists y.
    unfold Cong_3 in *;intuition.
Qed.

Lemma l5_6 : forall A B C D A' B' C' D',
 le A B C D /\ Cong A B A' B' /\ Cong C D C' D' -> le A' B' C' D'.
Proof.
    unfold le.
    intros.
    spliter.
    ex_and H y.
    assert (exists z : Tpoint, Bet C' z D' /\ Cong_3 C y D C' z D') by (eapply l4_5;auto).
    ex_and H3 z.
    exists z.
    split.
      assumption.
    unfold Cong_3 in *; spliter.
    apply cong_transitivity with A B; try Cong.
    apply cong_transitivity with C y; assumption.
Qed.

Lemma le_reflexivity : forall A B, le A B A B.
Proof.
    unfold le.
    intros.
    exists B.
    split; Between; Cong.
Qed.

Lemma le_transitivity : forall A B C D E F, le A B C D -> le C D E F -> le A B E F .
Proof.
    unfold le.
    intros.
    ex_and H y.
    ex_and H0 z.
    assert (exists P : Tpoint, Bet E P z /\ Cong_3 C y D E P z) by (eapply l4_5;assumption).
    ex_and H3 P.
    exists P.
    split.
      eBetween.
    unfold Cong_3 in H4; spliter; eCong.
Qed.

Lemma between_cong : forall A B C, Bet A C B -> Cong A C A B -> C=B.
Proof.
    intros.
    assert (Bet A B C).
      eapply l4_6 with A C B; unfold Cong_3; repeat split;Cong.
    eapply between_egality;eBetween.
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

Lemma between_cong_3 : forall A B D E, A <> B -> Bet A B D -> Bet A B E -> Cong B D B E -> D = E.
Proof.
    intros.
    assert (T:=l5_2 A B D E H H0 H1).
    elim T; intro; clear T.
      apply between_cong with B; Cong.
    symmetry; apply between_cong with B; Cong.
Qed.

Lemma le_anti_symmetry : forall A B C D, le A B C D -> le C D A B -> Cong A B C D.
Proof.
    intros.
    assert (exists T, Bet C D T /\ Cong C T A B) by (apply l5_5_1;assumption).
    unfold le in H.
    ex_and H Y.
    ex_and H1 T.
    assert (Cong C Y C T) by eCong.
    assert (Bet C Y T) by eBetween.
    assert (Y=T) by (eapply between_cong;eauto).
    subst Y.
    assert (T=D) by (eapply between_egality;eBetween).
    subst T.
    Cong.
Qed.

Lemma segment_construction_2 : forall A Q B C, A<>Q -> exists X, (Bet Q A X \/ Bet Q X A) /\ Cong Q X B C.
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

Lemma Cong_dec : forall A B C D,
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
      assert (Cong A D' A B) by eCong.
      elim H1; intro; clear H1.
        assert (B = D') by (apply (between_cong A D' B); Cong).
        subst;intuition.
      assert (D'=B) by (apply (between_cong A B D');assumption).
      subst;intuition.
    intuition.
Qed.


Lemma Bet_dec : forall A B C, Bet A B C  \/  ~ Bet A B C.
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


Lemma Col_dec : forall A B C, Col A B C \/ ~ Col A B C.
Proof.
    intros.
    unfold Col.
    elim (Bet_dec A B C); intro; elim (Bet_dec B C A); intro; elim (Bet_dec C A B); intro; tauto.
Qed.


Lemma le_trivial : forall A C D, le A A C D .
Proof.
    intros.
    unfold le.
    exists C.
    split; Between; Cong.
Qed.

Lemma le_cases : forall A B C D, le A B C D \/ le C D A B.
Proof.
    intros.
    induction(eq_dec_points A B).
      subst B; left; apply le_trivial.
    assert (exists X : Tpoint, (Bet A B X \/ Bet A X B) /\ Cong A X C D) by (eapply (segment_construction_2 B A C D);auto).
    ex_and H0 X.
    induction H0.
      left; apply l5_5_2; exists X; split; assumption.
    right; unfold le; exists X; split; Cong.
Qed.

Lemma le_zero : forall A B C, le A B C C -> A=B.
Proof.
    intros.
    assert (le C C A B) by apply le_trivial.
    assert (Cong A B C C) by (apply le_anti_symmetry;assumption).
    treat_equalities;auto.
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
      assert(le A C A D) by (eapply l5_5_2; exists D; split; Cong).
      assert(le C B C A) by (eapply l5_5_2; exists A; split; Between; Cong).
      assert(Cong A C A D) by (eapply le_anti_symmetry; try assumption; apply l5_6 with C B C A; Cong).
      apply between_cong with A; assumption.
    split; try assumption.
    subst D; apply sym_equal.
    eapply (between_cong C); Between; Cong.
Qed.


Definition lt := fun A B C D => le A B C D /\ ~ Cong A B C D.
Definition gt := fun A B C D => lt C D A B.

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

End T5.



