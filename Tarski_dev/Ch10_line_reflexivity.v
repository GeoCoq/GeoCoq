Require Export GeoCoq.Tarski_dev.Ch09_plane.

Section T10.

Context `{M:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Definition is_image_spec P' P A B :=
  (exists X, is_midpoint X P P' /\ Col A B X) /\
  (Perp A B P P' \/ P=P').

Definition is_image P' P A B :=
 (A<>B /\ is_image_spec P' P A B) \/ (A=B /\ is_midpoint A P P').

Lemma ex_sym : forall A B X, exists Y, (Perp A B X Y \/ X = Y) /\
   (exists M, Col A B M /\ is_midpoint M X Y).
Proof.
    intros.
    induction (Col_dec A B X).
      exists X.
      split.
        right.
        reflexivity.
      exists X.
      split.
        assumption.
      apply l7_3_2.
    assert (exists M, Col A B M /\ Perp A B X M).
      apply l8_18_existence.
      assumption.
    ex_and H0 M0.
    double X M0 Z.
    exists Z.
    split.
      left.
      apply perp_sym.
      eapply perp_col.
        intro.
        subst Z.
        apply l7_3 in H2.
        subst X.
        apply perp_distinct in H1.
        spliter.
        absurde.
        apply perp_sym.
        apply H1.
      unfold Col.
      left.
      apply midpoint_bet.
      assumption.
    exists M0.
    split.
      assumption.
    assumption.
Qed.

Lemma is_image_is_image_spec : forall P P' A B, A<>B -> (is_image P' P A B <-> is_image_spec P' P A B).
Proof.
    intros.
    unfold is_image.
    tauto.
Qed.

Require Import Setoid.

Lemma ex_sym1 : forall A B X, A<>B -> exists Y, (Perp A B X Y \/ X = Y) /\
 (exists M, Col A B M /\ is_midpoint M X Y /\ is_image X Y A B).
Proof.
    intros.
    induction (Col_dec A B X).
      exists X.
      split.
        right.
        reflexivity.
      exists X.
      rewrite -> (is_image_is_image_spec) by apply H.
      split.
        assumption.
      split.
        apply l7_3_2.
      unfold is_image_spec.
      split.
        exists X.
        split.
          apply l7_3_2.
        assumption.
      right.
      reflexivity.
    assert (exists M, Col A B M /\ Perp A B X M).
      apply l8_18_existence.
      assumption.
    ex_and H1 M0.
    double X M0 Z.
    exists Z.
    split.
      left.
      apply perp_sym.
      eapply perp_col.
        intro.
        subst Z.
        apply l7_3 in H3.
        subst X.
        apply perp_distinct in H2.
        spliter.
        absurde.
        apply perp_sym.
        apply H2.
      unfold Col.
      left.
      apply midpoint_bet.
      assumption.
    exists M0.
    split.
      assumption.
    split.
      assumption.
    rewrite -> (is_image_is_image_spec) by apply H.
    unfold is_image_spec.
    split.
      exists M0.
      split.
        apply l7_2.
        assumption.
      assumption.
    left.
    apply perp_sym.
    apply perp_left_comm.
    eapply perp_col.
      intro.
      subst X.
      apply l7_3 in H3.
      subst Z.
      apply perp_distinct in H2.
      spliter.
      absurde.
      apply perp_sym.
      apply H2.
    unfold Col.
    left.
    apply midpoint_bet.
    assumption.
Qed.

Lemma l10_2_unicity : forall A B P P1 P2,
 is_image P1 P A B -> is_image P2 P A B -> P1=P2.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst.
      unfold is_image in *.
      induction H.
        intuition.
      induction H0.
        intuition.
      spliter.
      eapply symmetric_point_unicity with P B;auto.
    rewrite -> (is_image_is_image_spec) in * by apply H1.
    unfold is_image_spec in *.
    spliter.
    ex_and H X.
    ex_and H0 Y.
    induction H2; induction H3.
      assert (P <> X).
        intro.
        subst X.
        apply is_midpoint_id in H.
        subst P1.
        apply perp_distinct in H3.
        spliter.
        absurde.
      assert (P <> Y).
        intro.
        subst Y.
        apply is_midpoint_id in H0.
        subst P2.
        apply perp_distinct in H2.
        spliter.
        absurde.
      assert (Perp P X A B).
        eapply perp_col.
          assumption.
          apply perp_sym.
          apply H3.
        unfold Col.
        right; left.
        apply midpoint_bet.
        apply l7_2.
        assumption.
      assert (Perp P Y A B).
        eapply perp_col.
          assumption.
          apply perp_sym.
          apply H2.
        unfold Col.
        right; left.
        apply midpoint_bet.
        apply l7_2.
        assumption.
      induction (eq_dec_points X A).
        subst X.
        assert (~ Col A B P /\ Per P A B).
          eapply l8_16_1.
            assumption.
            apply col_trivial_3.
            apply col_trivial_2.
            auto.
          apply perp_sym.
          assumption.
        spliter.
        assert (Y = A).
          eapply l8_18_unicity.
            apply H10.
            assumption.
            apply perp_sym.
            assumption.
            apply col_trivial_3.
          apply perp_sym.
          assumption.
        subst Y.
        eapply symmetric_point_unicity.
          apply H.
        apply H0.
      assert (~ Col A B P /\ Per P X A).
        eapply l8_16_1.
          assumption.
          assumption.
          apply col_trivial_3.
          auto.
        apply perp_sym.
        assumption.
      spliter.
      assert (Y = X).
        eapply l8_18_unicity.
          apply H11.
          assumption.
          apply perp_sym.
          assumption.
          assumption.
        apply perp_sym.
        assumption.
      subst Y.
      eapply symmetric_point_unicity.
        apply H.
      apply H0.
      subst P1.
      assert (P <> Y).
        intro.
        subst Y.
        apply l7_3 in H.
        subst X.
        apply is_midpoint_id in H0.
        subst P2.
        eapply perp_distinct in H2.
        spliter.
        absurde.
      assert (Perp P Y A B).
        eapply perp_col.
          assumption.
          apply perp_sym.
          apply H2.
        unfold Col.
        right; left.
        apply midpoint_bet.
        apply l7_2.
        assumption.
      apply l7_3 in H.
      subst X.
      induction (eq_dec_points Y A).
        subst Y.
        assert (~ Col A B P /\ Per P A B).
          eapply l8_16_1.
            assumption.
            assumption.
            apply col_trivial_2.
            auto; auto.
          apply perp_sym.
          assumption.
        spliter.
        contradiction.
      assert (~ Col A B P /\ Per P Y A).
        eapply l8_16_1.
          assumption.
          assumption.
          apply col_trivial_3.
          auto.
        apply perp_sym.
        assumption.
      spliter.
      contradiction.
      subst P2.
      assert (P <> X).
        intro.
        subst X.
        apply l7_3 in H0.
        subst Y.
        apply is_midpoint_id in H.
        subst P1.
        eapply perp_distinct in H3.
        spliter.
        absurde.
      assert (Perp P X A B).
        eapply perp_col.
          assumption.
          apply perp_sym.
          apply H3.
        unfold Col.
        right; left.
        apply midpoint_bet.
        apply l7_2.
        assumption.
      apply l7_3 in H0.
      subst Y.
      induction (eq_dec_points X A).
        subst X.
        assert (~ Col A B P /\ Per P A B).
          eapply l8_16_1.
            assumption.
            assumption.
            apply col_trivial_2.
            auto.
          apply perp_sym.
          assumption.
        spliter.
        contradiction.
      assert (~ Col A B P /\ Per P X A).
        eapply l8_16_1.
          assumption.
          assumption.
          apply col_trivial_3.
          auto.
        apply perp_sym.
        assumption.
      spliter.
      contradiction.
    subst P1.
    subst P2.
    reflexivity.
Qed.

Lemma l10_2_existence_spec : forall A B P,
 exists P', is_image_spec P' P A B.
Proof.
    intros.
    induction (Col_dec A B P).
      unfold is_image_spec.
      exists P.
      split.
        exists P.
        split.
          apply l7_3_2.
        assumption.
      right.
      reflexivity.
    assert (exists X, Col A B X /\ Perp A B P X).
      eapply l8_18_existence.
      assumption.
    ex_and H0 X.
    double P X P'.
    exists P'.
    unfold is_image_spec.
    split.
      exists X.
      split; assumption.
    left.
    apply perp_sym.
    eapply perp_col.
      intro.
      subst P'.
      apply l7_3 in H2.
      subst X.
      apply perp_distinct in H1.
      spliter.
      absurde.
      apply perp_sym.
      apply H1.
    unfold Col.
    left.
    apply midpoint_bet.
    assumption.
Qed.

Lemma l10_2_existence : forall A B P,
 exists P', is_image P' P A B.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst B.
      unfold is_image.
      elim (symmetric_point_construction P A).
      intros P'.
      exists P'.
      tauto.
    elim (l10_2_existence_spec A B P).
    intros P'; intros.
    exists P'.
    unfold is_image.
    tauto.
Qed.

Lemma l10_4_spec : forall A B P P',
 is_image_spec P P' A B ->
 is_image_spec P' P A B.
Proof.
    intros.
    unfold is_image_spec in *.
    spliter.
    ex_and H X.
    split.
      exists X.
      split.
        apply l7_2.
        assumption.
      assumption.
    induction H0.
      left.
      apply perp_right_comm.
      assumption.
    auto.
Qed.

Lemma l10_4 : forall A B P P', is_image P P' A B -> is_image P' P A B.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst B.
      unfold is_image in *.
      elim H;intros.
        intuition.
      right.
      spliter.
      split.
        assumption.
      apply l7_2.
      assumption.
    rewrite -> (is_image_is_image_spec) in * by apply H0.
    apply l10_4_spec;auto.
Qed.

Lemma l10_5 : forall A B P P' P'',
 is_image P' P A B ->
 is_image P'' P' A B -> P=P''.
Proof.
    intros.
    induction (eq_dec_points A B).
      unfold is_image in *.
      subst.
      induction H.
        intuition.
      induction H0.
        intuition.
      spliter.
      apply symmetric_point_unicity with P' B.
        apply l7_2.
        assumption.
      assumption.
    rewrite -> (is_image_is_image_spec) in * by apply H1.
    eapply l10_2_unicity.
      eapply l10_4.
      apply is_image_is_image_spec.
        apply H1.
      apply H.
    apply is_image_is_image_spec.
      assumption.
    assumption.
Qed.

Lemma l10_6_unicity : forall A B P P1 P2, is_image P P1 A B -> is_image P P2 A B -> P1 = P2.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst.
      unfold is_image in *.
      induction H.
        intuition.
      induction H0.
        intuition.
      spliter.
      apply symmetric_point_unicity with P B.
        apply l7_2.
        assumption.
      apply l7_2.
      assumption.
    eapply l10_2_unicity.
      apply l10_4.
      apply H.
    apply l10_4.
    assumption.
Qed.

Lemma l10_6_existence_spec : forall A B P', A<>B -> exists P, is_image_spec P' P A B.
Proof.
    intros.
    assert (exists P, is_image_spec P P' A B).
      eapply l10_2_existence_spec.
    ex_and H0 P.
    exists P.
    apply l10_4_spec.
    assumption.
Qed.

Lemma l10_6_existence : forall A B P', exists P, is_image P' P A B.
Proof.
    intros.
    assert (exists P, is_image P P' A B).
      eapply l10_2_existence.
    ex_and H P.
    exists P.
    apply l10_4.
    assumption.
Qed.

Lemma l10_7 : forall A B P P' Q Q',
 is_image P' P A B -> is_image Q' Q A B ->
  P'=Q' -> P = Q.
Proof.
    intros.
    subst Q'.
    eapply l10_2_unicity.
      apply l10_4.
      apply H.
    apply l10_4.
    assumption.
Qed.

Lemma l10_8 : forall A B P, is_image P P A B -> Col P A B.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst;Col.
    unfold is_image in H.
    unfold is_image_spec in H.
    induction H.
      spliter.
      ex_and H1 X.
      apply l7_3 in H1.
      subst X.
      Col.
    spliter. subst. Col.
Qed.


(** Here we need the assumption that A<>B *)
Lemma is_image_col_cong : forall A B P P' X, A<>B ->
 is_image P P' A B -> Col A B X -> Cong P X P' X.
Proof.
    intros.
    rewrite is_image_is_image_spec in H0 by apply H.
    unfold is_image_spec in *.
    spliter.
    ex_and H0 M0.
    induction H2.
      assert (HH:= H2).
      apply perp_distinct in HH.
      spliter.
      induction (eq_dec_points M0 X).
        subst X.
        unfold is_midpoint in *.
        spliter.
        Cong.
      assert (Perp M0 X P' P).
        eapply perp_col2;eauto.
      assert(~ Col A B P /\ Per P M0 X).
        eapply l8_16_1.
          assumption.
          assumption.
          assumption.
          auto.
        apply perp_sym.
        eapply perp_col.
          intro.
          subst P.
          apply l7_2 in H0.
          apply is_midpoint_id in H0.
          subst P'.
          absurde.
          apply perp_left_comm.
          apply perp_sym.
          apply H2; eapply perp_left_comm.
        unfold Col.
        right; left.
        apply midpoint_bet.
        assumption.
      spliter.
      eapply l8_2 in H9.
      unfold Per in H9.
      ex_and H9 P0.
      assert (P0 = P').
        eapply symmetric_point_unicity.
          apply H9.
        apply l7_2.
        assumption.
      subst P0.
      apply cong_commutativity.
      assumption.
    subst P'.
    apply cong_reflexivity.
Qed.

Lemma is_image_spec_col_cong : forall A B P P' X,
 is_image_spec P P' A B -> Col A B X -> Cong P X P' X.
Proof.
    intros.
    unfold is_image_spec in *.
    spliter.
    ex_and H M0.
    induction H1.
      assert (HH:= H1).
      apply perp_distinct in HH.
      spliter.
      induction (eq_dec_points M0 X).
        subst X.
        unfold is_midpoint in *.
        spliter.
        Cong.
      assert (Perp M0 X P' P) by (eauto using perp_col2).
      assert(~ Col A B P /\ Per P M0 X).
        eapply l8_16_1.
          assumption.
          assumption.
          assumption.
          auto.
        apply perp_sym.
        eapply perp_col.
          intro.
          subst P.
          apply l7_2 in H.
          apply is_midpoint_id in H.
          subst P'.
          absurde.
          apply perp_left_comm.
          apply perp_sym.
          apply H1; eapply perp_left_comm.
        unfold Col.
        right; left.
        apply midpoint_bet.
        assumption.
      spliter.
      eapply l8_2 in H8.
      unfold Per in H8.
      ex_and H8 P0.
      assert (P0 = P').
        eapply symmetric_point_unicity.
          apply H8.
        apply l7_2.
        assumption.
      subst P0.
      Cong.
    subst.
    Cong.
Qed.

Lemma image_id : forall A B T T',
  A<>B ->
  Col A B T ->
  is_image T T' A B ->
  T = T'.
Proof.
    intros.
    rewrite is_image_is_image_spec in H1 by apply H.
    unfold is_image_spec in H1.
    spliter.
    ex_and H1 X.
    induction H2.
      assert (A <> B /\ T' <> T).
        apply perp_distinct in H2.
        spliter.
        split; assumption.
      spliter.
      induction (eq_dec_points A X).
        subst X.
        assert (Perp A B T' A).
          apply perp_sym.
          eapply perp_col.
            intro.
            subst T'.
            apply is_midpoint_id in H1.
            subst A.
            absurde.
            apply perp_sym.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          apply l7_2.
          assumption.
        assert (~ Col  A T' B).
          apply perp_not_col.
          apply perp_comm.
          apply perp_sym.
          assumption.
        assert (A = T).
          apply l6_21 with A T' B T; assert_cols; Col.
          intro; treat_equalities; Col.
        subst A.
        apply l7_2 in H1.
        apply is_midpoint_id in H1.
        subst T'.
        absurde.
      induction (eq_dec_points B X).
        subst X.
        assert (Perp A B T' B).
          apply perp_sym.
          eapply perp_col.
            intro.
            subst T'.
            apply is_midpoint_id in H1.
            subst B.
            absurde.
            apply perp_sym.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          apply l7_2.
          assumption.
        assert (~ Col  B T' A).
          apply perp_not_col.
          apply perp_left_comm.
          apply perp_sym.
          assumption.
        assert (B = T).
          eapply l6_21.
            apply H8.
            apply H4.
            apply col_trivial_3.
            unfold Col.
            right; right.
            apply midpoint_bet.
            apply l7_2.
            apply H1.
            apply col_trivial_2.
            assumption.
        subst B.
        apply l7_2 in H1.
        apply is_midpoint_id in H1.
        subst T'.
        absurde.
      assert (Col A X T) by ColR.
      assert (Perp A B T' X).
        apply perp_sym.
        eapply perp_col.
          intro.
          subst T'.
          apply is_midpoint_id in H1.
          subst X.
          absurde.
          apply perp_sym.
          apply H2.
        assert_cols.
        Col.
      assert (~ Col  X T' A).
        apply perp_not_col.
        apply perp_left_comm.
        apply perp_sym.
        eapply perp_col.
          assumption.
          apply H9.
        assumption.
      assert (X = T).
        eapply l6_21.
          apply H10.
          apply H6.
          apply col_trivial_3.
          unfold Col.
          right; right.
          apply midpoint_bet.
          apply l7_2.
          apply H1.
          apply col_trivial_2.
          assumption.
      subst X.
      apply l7_2 in H1.
      apply is_midpoint_id in H1.
      subst T'.
      absurde.
    subst T'.
    reflexivity.
Qed.

Lemma osym_not_col : forall A B P P',
 is_image P P' A B ->
 ~ Col A B P -> ~ Col A B P'.
Proof.
    intros.
    unfold is_image in *.
    induction H.
      spliter.
      assert ( HH:= H1).
      unfold is_image_spec in HH.
      spliter.
      ex_and H2 T.
      intro.
      induction H3.
        assert (P'=P).
          eapply image_id.
            apply H.
            assumption.
          apply l10_4.
          apply is_image_is_image_spec.
            assumption.
          assumption.
        subst P'.
        apply perp_distinct in H3.
        spliter.
        absurde.
      apply H0.
      subst P'.
      assumption.
    spliter. subst. Col5.
Qed.

Lemma midpoint_preserves_image : forall A B P P' Q Q' M,
 A <> B -> Col A B M -> is_image P P' A B ->
 is_midpoint M P Q -> is_midpoint M P' Q' -> is_image Q Q' A B.
Proof.
    intros.
    rewrite is_image_is_image_spec in * by apply H.
    assert (HH1:=H1).
    unfold is_image_spec in H1.
    spliter.
    ex_and H1 X.
    induction H4.
      double X M0 Y.
      assert (is_midpoint Y Q Q').
        eapply symmetry_preserves_midpoint.
          apply H2.
          apply H6.
          apply H3.
        apply l7_2.
        apply H1.
      assert (P <> P').
        intro.
        subst P'.
        apply perp_distinct in H4.
        spliter.
        absurde.
      assert (Q <> Q').
        intro.
        subst Q'.
        apply l7_3 in H7.
        subst Q.
        assert (P=P').
          eapply l7_9.
            apply H2.
          apply H3.
        subst P'.
        apply perp_distinct in H4.
        spliter.
        absurde.
      split.
        exists Y.
        split.
          apply l7_2.
          apply H7.
        induction (eq_dec_points X Y).
          subst Y.
          assumption.
        assert_diffs.
        ColR.
      left.
      assert(Per M0 Y Q).
        unfold Per.
        exists Q'.
        split.
          assumption.
        unfold is_midpoint in *.
        spliter.
        eapply cong_transitivity.
          apply cong_symmetry.
          apply H14.
        apply cong_symmetry.
        eapply cong_transitivity.
          apply cong_symmetry.
          apply H13.
        eapply is_image_col_cong.
          apply H.
          apply l10_4.
          apply is_image_is_image_spec.
            assumption.
          apply HH1.
        assumption.
      induction (eq_dec_points X Y).
        subst Y.
        apply l7_3 in H6.
        subst X.
        apply perp_sym.
        eapply perp_col.
          auto.
          apply perp_left_comm.
          eapply perp_col.
            2:apply perp_sym.
            2:apply H4.
            intro.
            subst Q'.
            apply l7_3 in H3.
            subst P'.
            apply is_midpoint_id in H1.
            subst P.
            absurde.
          eapply (col_transitivity_2 M0).
            intro.
            subst P'.
            apply is_midpoint_id in H1.
            subst P.
            absurde.
            unfold Col.
            right; right.
            apply midpoint_bet.
            apply l7_2.
            assumption.
          unfold Col.
          right; right.
          apply midpoint_bet.
          apply l7_2.
          assumption.
        eapply (col_transitivity_2 M0).
          intro.
          subst Q'.
          apply l7_2 in H7.
          apply is_midpoint_id in H7.
          subst Q.
          absurde.
          unfold Col.
          right; right.
          apply midpoint_bet.
          assumption.
        unfold Col.
        right; right.
        apply midpoint_bet.
        assumption.
      apply per_perp_in in H10.
        apply perp_in_perp in H10.
        induction H10.
          apply perp_distinct in H10.
          spliter.
          absurde.
        apply perp_comm.
        apply perp_sym.
        eapply perp_col.
          assumption.
          apply perp_comm.
          eapply (perp_col  Y Q).
            intro.
            subst Q.
            apply perp_distinct in H10.
            spliter.
            absurde.
            apply perp_sym.
            induction (eq_dec_points A M0).
              subst A.
              apply perp_left_comm.
              eapply (perp_col _ M0).
                auto.
                apply perp_left_comm.
                eapply (perp_col _ Y).
                  assumption.
                  assumption.
                induction (eq_dec_points M0 X).
                  subst X.
                  apply is_midpoint_id in H6.
                  subst M0.
                  apply col_trivial_1.
                eapply (col_transitivity_1 _ X).
                  assumption.
                  unfold Col.
                  right; right.
                  apply midpoint_bet.
                  apply l7_2.
                  assumption.
                apply col_permutation_5.
                assumption.
              apply col_trivial_2.
            induction (eq_dec_points B M0).
              subst M0.
              apply perp_left_comm.
              apply (perp_col _ Y).
                auto.
                assumption.
              induction (eq_dec_points B X).
                subst X.
                apply is_midpoint_id in H6.
                subst Y.
                absurde.
              eapply col_transitivity_1.
                apply H13.
                unfold Col.
                right; right.
                apply midpoint_bet.
                apply l7_2.
                assumption.
              apply col_permutation_1.
              assumption.
            eapply perp_col.
              assumption.
              apply perp_left_comm.
              eapply (perp_col M0 Y).
                auto.
                assumption.
              assert(Col B X M0).
                eapply col_transitivity_2.
                  apply H.
                  assumption.
                assumption.
              induction (eq_dec_points M0 X).
                subst X.
                apply is_midpoint_id in H6.
                contradiction.
              assert(Col B Y M0).
                apply col_permutation_1.
                eapply (col_transitivity_2  X).
                  auto.
                  apply col_permutation_1.
                  assumption.
                unfold Col.
                left.
                apply midpoint_bet.
                assumption.
              eapply (col_transitivity_1 _ B).
                auto.
                apply col_permutation_2.
                assumption.
              apply col_permutation_3.
              apply H0.
            apply col_permutation_5.
            apply H0.
          apply col_trivial_2.
        unfold Col.
        left.
        apply midpoint_bet.
        apply H7.
        intro.
        subst Y.
        apply l7_2 in H6.
        apply is_midpoint_id in H6.
        subst X.
        absurde.
      intro.
      subst Q.
      apply is_midpoint_id in H7.
      subst Q'.
      absurde.
    subst P'.
    apply l7_3 in H1.
    subst P.
    assert(Q = Q').
      eapply l7_9.
        apply l7_2.
        apply H2.
      apply l7_2.
      apply H3.
    subst Q'.
    split.
      exists Q.
      split.
        apply l7_3_2.
      induction (eq_dec_points M0 X).
        subst X.
        assert(M0=Q).
          apply is_midpoint_id.
          assumption.
        subst Q.
        assumption.
      ColR.
    right.
    reflexivity.
Qed.


Definition is_image_spec_in M P' P A B :=
  (is_midpoint M P P' /\ Col A B M) /\ (Perp A B P P' \/ P=P').

Definition is_image_spec_in_gen M P' P A B :=
 (A <> B /\ is_image_spec_in M P' P A B) \/ (A=B /\ A=M /\ is_midpoint M P P').

Lemma image_in_is_image_spec :
 forall M A B P P',
  is_image_spec_in M P P' A B -> is_image_spec P P' A B.
Proof.
    intros.
    unfold is_image_spec_in in H.
    spliter.
    unfold is_image_spec.
    split.
      exists M0.
      split; assumption.
    assumption.
Qed.

Lemma image_in_gen_is_image : forall M A B P P',
 is_image_spec_in_gen M P P' A B  -> is_image P P' A B.
Proof.
    intros.
    unfold is_image_spec_in_gen in H.
    induction H.
      spliter.
      apply image_in_is_image_spec in H0.
      unfold is_image.
      tauto.
    spliter.
    subst.
    subst.
    unfold is_image.
    right.
    auto.
Qed.

Lemma image_image_in : forall A B P P' M,
 P <> P'-> is_image_spec P P' A B -> Col A B M -> Col P M P' ->
 is_image_spec_in M P P' A B.
Proof.
    intros.
    unfold is_image_spec_in.
    split.
      split.
        assert(HH:=H0).
        unfold is_image_spec in H0.
        spliter.
        ex_and H0 M'.
        induction H3.
          assert (Perp P M' A B).
            eapply perp_col.
              intro.
              subst P.
              apply l7_2 in H0.
              apply is_midpoint_id in H0.
              subst P'.
              apply perp_distinct in H3.
              spliter.
              absurde.
              apply perp_sym.
              apply perp_right_comm.
              apply H3.
            unfold Col.
            right; left.
            apply midpoint_bet.
            assumption.
          assert (M'=M0).
            eapply l6_21.
              2: apply H.
              2: apply H4.
              induction (eq_dec_points A M').
                subst M'.
                assert (~ Col A B P /\ Per P A B).
                  eapply l8_16_1.
                    apply perp_distinct in H3.
                    spliter.
                    assumption.
                    apply col_trivial_3.
                    apply col_trivial_2.
                    apply perp_distinct in H3.
                    spliter.
                    auto.
                  apply perp_sym.
                  assumption.
                spliter.
                intro.
                apply H6.
                assumption.
              assert (~ Col A B P /\ Per P M' A).
                eapply l8_16_1.
                  apply perp_distinct in H3.
                  spliter.
                  assumption.
                  assumption.
                  apply col_trivial_3.
                  assumption.
                apply perp_sym.
                assumption.
              spliter.
              intro.
              apply H7.
              assumption.
              assumption.
              unfold Col.
              right; left.
              apply midpoint_bet.
              apply H0.
              apply col_permutation_5.
              assumption.
            apply perp_distinct in H3.
            spliter.
            auto.
          subst M'.
          assumption.
        subst P'.
        absurde.
      assumption.
    assert (HH:=H0).
    unfold is_image_spec in H0.
    spliter.
    induction H3.
      left.
      assumption.
    right.
    assumption.
Qed.

Lemma image_in_col0 : forall A B P P' Y : Tpoint,
 is_image_spec_in Y P P' A B -> Col P P' Y.
Proof.
    intros.
    unfold is_image_spec_in in *.
    spliter.
    assert_cols.
    Col.
Qed.

Lemma is_image_spec_rev : forall P P' A B, is_image_spec P P' A B -> is_image_spec P P' B A.
Proof.
    unfold is_image_spec.
    intros.
    spliter.
    split.
      ex_and H M0.
      exists M0.
      split.
        assumption.
      apply col_permutation_4.
      assumption.
    induction H0.
      left.
      apply perp_left_comm.
      assumption.
    right.
    assumption.
Qed.

Lemma is_image_rev : forall P P' A B,
 is_image P P' A B -> is_image P P' B A.
Proof.
    intros.
    unfold is_image in *.
    induction H.
      spliter.
      left.
      split.
        auto.
      apply is_image_spec_rev.
      assumption.
    right.
    spliter. subst. tauto.
Qed.

(* TODO move *)
Lemma per_double_cong : forall A B C C',
 Per A B C -> is_midpoint B C C' -> Cong A C A C'.
Proof.
    intros.
    unfold Per in H.
    ex_and H C''.
    assert (C' = C'').
      eapply l7_9.
        apply l7_2.
        apply H0.
      apply l7_2.
      assumption.
    subst C''.
    assumption.
Qed.

Lemma midpoint_preserves_per : forall A B C A1 B1 C1 M,
 Per A B C ->
 is_midpoint M A A1 ->
 is_midpoint M B B1 ->
 is_midpoint M C C1 ->
 Per A1 B1 C1.
Proof.
    intros.
    unfold Per in *.
    ex_and H C'.
    double C' M0 C1'.
    exists C1'.
    split.
      eapply symmetry_preserves_midpoint.
        apply H2.
        apply H1.
        apply H4.
      assumption.
    eapply l7_16.
      apply H0.
      apply H2.
      apply H0.
      apply H4.
    assumption.
Qed.


(* TODO move chapter 8 *)
Lemma col_per_perp : forall A B C D,
 A <> B -> B <> C -> D <> B -> D <> C ->
 Col B C D -> Per A B C -> Perp C D A B.
Proof.
    intros.
    apply per_perp_in in H4.
      apply perp_in_perp in H4.
      induction H4.
        apply perp_distinct in H4.
        spliter.
        absurde.
      eapply (perp_col _ B).
        auto.
        apply perp_sym.
        apply perp_right_comm.
        assumption.
      apply col_permutation_4.
      assumption.
      assumption.
    assumption.
Qed.

Lemma image_col : forall A B X, Col A B X -> is_image_spec X X A B.
Proof.
    intros.
    unfold is_image_spec.
    split.
      exists X.
      split.
        apply l7_3_2.
      assumption.
    right.
    reflexivity.
Qed.

Lemma is_image_spec_triv : forall A B, is_image_spec A A B B.
Proof.
    intros.
    apply image_col.
    Col.
Qed.

Lemma is_image_spec_dec :
  forall A B C D, is_image_spec A B C D \/ ~ is_image_spec A B C D.
Proof.
    intros.
    elim (eq_dec_points C D); intro HCD.
      subst.
      elim (eq_dec_points A B); intro HAB.
        subst.
        left.
        apply is_image_spec_triv.
      right.
      intro H.
      unfold is_image_spec in *.
      destruct H as [H HFalse].
      elim HFalse; clear HFalse; intro HFalse.
        apply perp_distinct in HFalse.
        intuition.
      intuition.
    elim (l10_6_existence_spec C D A HCD); intros B' HB'.
    elim (eq_dec_points B B'); intro HBB'.
      subst.
      tauto.
    right.
    intro H.
    apply HBB'.
    apply l10_6_unicity with C D A.
      unfold is_image.
      tauto.
    unfold is_image.
    tauto.
Qed.

Lemma l10_14 : forall P P' A B, P <> P' -> A <> B ->
 is_image P P' A B -> two_sides A B P P'.
Proof.
    intros.
    rewrite is_image_is_image_spec in H1 by apply H0.
    unfold is_image_spec in H1.
    spliter.
    ex_and H1 M0.
    induction H2.
      assert (P <> M0).
        intro.
        subst P.
        apply l7_2 in H1.
        apply is_midpoint_id in H1.
        subst P'.
        absurde.
      induction (eq_dec_points A M0).
        subst A.
        assert (Perp M0 B P M0).
          apply perp_sym.
          eapply (perp_col _ P').
            assumption.
            apply perp_sym.
            apply perp_right_comm.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        assert (Perp_in M0 M0 B P M0).
          eapply perp_perp_in.
          assumption.
        assert(Per B M0 P).
          eapply perp_in_per.
          apply perp_in_comm.
          assumption.
        assert (B <> M0).
          intro.
          repeat split.
          subst B.
          apply perp_distinct in H2.
          spliter.
          absurde.
        assert (~Col B M0 P).
          eapply per_not_col.
            assumption.
            auto.
          assumption.
        repeat split.
          auto.
          intro.
          apply H9.
          Col.
          intro.
          apply H9.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ P').
            intro.
            subst P'.
            apply is_midpoint_id in H1.
            subst P.
            absurde.
            unfold Col.
            right; right.
            apply midpoint_bet.
            apply l7_2.
            assumption.
          apply col_permutation_4.
          assumption.
        exists M0.
        split.
          apply col_trivial_1.
        apply midpoint_bet.
        apply l7_2.
        assumption.
      induction (eq_dec_points B M0).
        subst B.
        assert (Perp M0 A P M0).
          apply perp_sym.
          eapply (perp_col _ P').
            assumption.
            apply perp_sym.
            apply perp_comm.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        assert (Perp_in M0 M0 A P M0).
          eapply perp_perp_in.
          assumption.
        assert(Per A M0 P).
          eapply perp_in_per.
          apply perp_in_comm.
          assumption.
        repeat split.
          assumption.
          assert (~Col A M0 P).
            eapply per_not_col.
              assumption.
              auto.
            assumption.
          intro.
          apply H9.
          apply col_permutation_1.
          assumption.
          intro.
          assert (Col M0 A P).
            eapply (col_transitivity_1 _ P').
              intro.
              subst P'.
              apply is_midpoint_id in H1.
              subst P.
              absurde.
              apply col_permutation_2.
              assumption.
            unfold Col.
            right; right.
            apply midpoint_bet.
            apply l7_2.
            assumption.
          eapply (per_not_col ).
            3: apply H8.
            assumption.
            auto.
          apply col_permutation_4.
          assumption.
        exists M0.
        split.
          apply col_trivial_3.
        apply midpoint_bet.
        apply l7_2.
        assumption.
      repeat split.
        apply perp_distinct in H2.
        spliter.
        assumption.
        assert(Perp  P M0 A B).
          eapply perp_col.
            assumption.
            apply perp_sym.
            apply perp_right_comm.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        assert (~ Col M0 P A).
          apply perp_not_col.
          apply perp_sym.
          eapply perp_col.
            assumption.
            apply perp_sym.
            apply perp_left_comm.
            apply H7.
          assumption.
        intro.
        apply H8.
        apply col_permutation_1.
        eapply col_transitivity_1.
          apply perp_distinct in H2.
          spliter.
          apply H2.
          assumption.
        apply col_permutation_1.
        assumption.
        assert(Perp  P' M0 A B).
          eapply perp_col.
            intro.
            subst P'.
            apply is_midpoint_id in H1.
            subst P.
            absurde.
            apply perp_sym.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          apply l7_2.
          assumption.
        assert (~ Col M0 P' A).
          apply perp_not_col.
          apply perp_sym.
          eapply perp_col.
            assumption.
            apply perp_sym.
            apply perp_left_comm.
            apply H7.
          assumption.
        intro.
        apply H8.
        apply col_permutation_1.
        eapply col_transitivity_1.
          apply perp_distinct in H2.
          spliter.
          apply H2.
          assumption.
        apply col_permutation_1.
        assumption.
      exists M0.
      split.
        apply col_permutation_2.
        assumption.
      apply midpoint_bet.
      apply l7_2.
      assumption.
    subst P'.
    absurde.
Qed.

Lemma l10_15 : forall A B C P,
 Col A B C -> ~ Col A B P ->
 exists Q, Perp A B Q C /\ one_side A B P Q.
Proof.
    intros.
    assert (A<>B).
      intro;subst.
      Col.
    assert (exists X , two_sides A B P X).
      apply l9_10.
        assumption.
      intro.
      apply H0.
      apply col_permutation_1.
      assumption.
    ex_elim H2 X.
    induction (eq_dec_points A C).
      subst C.
      assert (exists Q, exists T, Perp A B Q A /\ Col A B T /\ Bet X T Q).
        apply l8_21.
        assumption.
      ex_elim H2 Q.
      ex_and H4 T.
      exists Q.
      split.
        assumption.
      eapply l9_8_1.
        apply H3.
      unfold two_sides.
      repeat split.
        assumption.
        apply perp_not_col in H2.
        intro.
        apply H2.
        apply col_permutation_1.
        assumption.
        unfold two_sides in H3.
        spliter.
        assumption.
      exists T.
      split.
        apply col_permutation_2.
        assumption.
      apply between_symmetry.
      assumption.
    assert (exists Q, exists T, Perp C A Q C /\ Col C A T /\ Bet X T Q).
      apply l8_21.
      auto.
    ex_elim H4 Q.
    ex_and H5 T.
    exists Q.
    split.
      eapply perp_col.
        assumption.
        apply perp_left_comm.
        apply H4.
      apply col_permutation_5.
      assumption.
    eapply l9_8_1.
      apply H3.
    unfold two_sides.
    repeat split.
      assumption.
      eapply perp_not_col in H4.
      intro.
      apply H4.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H1.
        apply col_permutation_1.
        assumption.
      assumption.
      unfold two_sides in H3.
      spliter.
      assumption.
    exists T.
    split.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H2.
        apply col_permutation_5.
        assumption.
      apply col_permutation_4.
      assumption.
    apply between_symmetry.
    assumption.
Qed.

Lemma not_col_exists : forall A B, A <> B -> exists P, ~Col A B P.
Proof.
    intros.
    assert(HH:= ex_col2 A B).
    ex_and HH C.
    assert(HH:=l8_21 A B C H).
    ex_and HH P.
    ex_and H3 T.
    apply perp_not_col in H3.
    exists P.
    assumption.
Qed.

Lemma perp_exists : forall O A B, A <> B -> exists X, Perp O X A B.
Proof.
    intros.
    assert(HH:=not_col_exists A B H).
    ex_and HH Q.
    induction(Col_dec O A B).
      assert(exists P, Perp A B P O /\ one_side A B Q P).
        apply(l10_15 A B O Q ).
          Col.
        auto.
      ex_and H2 P.
      exists P.
      apply perp_sym.
      apply perp_right_comm.
      auto.
    assert(exists P : Tpoint, Col A B P /\ Perp A B O P).
      apply (l8_18_existence A B O).
      intro.
      apply H1.
      Col.
    ex_and H2 P.
    exists P.
    apply perp_sym.
    auto.
Qed.

End T10.