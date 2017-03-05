Require Export GeoCoq.Meta_theory.Dimension_axioms.upper_dim.

Section T10_2D.

Context `{T2D:Tarski_2D}.

Lemma all_coplanar : forall A B C D, Coplanar A B C D.
Proof.
apply upper_dim_implies_all_coplanar;
unfold upper_dim_axiom; apply upper_dim.
Qed.

Lemma per_per_col : forall A B C X, Per A X C -> X <> C -> Per B X C -> Col A B X.
Proof.
intros. apply cop_per_per_col with C; auto; apply all_coplanar.
Qed.

Lemma perp_perp_col : forall X Y Z A B,
 Perp X Y A B -> Perp X Z A B -> Col X Y Z.
Proof.
    intros.
    induction(Col_dec A B X).
      induction(eq_dec_points X A).
        subst A.
        assert(X <> B).
          apply perp_distinct in H.
          spliter.
          assumption.
        apply perp_right_comm in H.
        apply perp_perp_in in H.
        apply perp_in_comm in H.
        apply perp_in_per in H.
        apply perp_right_comm in H0.
        apply perp_perp_in in H0.
        apply perp_in_comm in H0.
        apply perp_in_per in H0.
        apply col_permutation_2.
        eapply (per_per_col).
          apply H.
          assumption.
        assumption.
      assert(Perp A X X Y ).
        eapply perp_col.
          auto.
          apply perp_sym.
          apply H.
        assumption.
      assert(Perp A X X Z).
        eapply perp_col.
          auto.
          apply perp_sym.
          apply H0.
        assumption.
      apply col_permutation_2.
      eapply (per_per_col _ _ A).
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        apply perp_sym.
        eapply perp_col.
          auto.
          apply perp_sym.
          apply H.
        assumption.
        assumption.
      apply perp_in_per.
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_sym.
      eapply perp_col.
        auto.
        apply perp_sym.
        apply H0.
      assumption.
    assert(HH0:=H).
    assert(HH1:=H0).
    unfold Perp in H.
    unfold Perp in H0.
    ex_and H Y0.
    ex_and H0 Z0.
    assert(HH2:=H).
    assert(HH3:=H2).
    apply perp_in_col in H.
    apply perp_in_col in H2.
    spliter.
    assert(Perp X Y0 A B).
      eapply perp_col.
        intro.
        subst Y0.
        contradiction.
        apply HH0.
      assumption.
    assert(Perp X Z0 A B).
      eapply perp_col.
        intro.
        subst Z0.
        contradiction.
        apply HH1.
      assumption.
    assert(Y0 = Z0).
      eapply l8_18_uniqueness.
        apply H1.
        assumption.
        apply perp_sym.
        assumption.
        assumption.
      apply perp_sym.
      assumption.
    subst Z0.
    eapply (col_transitivity_1 _ Y0).
      intro.
      subst Y0.
      contradiction.
      Col.
    Col.
Qed.

(* TODO add coplanar assumption, this is false in 3D. *)
Lemma image_in_col : forall A B P P' Q Q' M,
 ReflectL_at M P P' A B -> ReflectL_at M Q Q' A B ->
 Col M P Q.
Proof.
    intros.
    assert(ReflectL P P' A B).
      eapply (image_in_is_image_spec M).
      assumption.
    assert(ReflectL Q Q' A B).
      eapply (image_in_is_image_spec M).
      assumption.
    unfold ReflectL_at in *.
    spliter.
    induction H3.
      induction H5.
        induction (eq_dec_points A M).
          subst M.
          assert (Per B A P).
            unfold Per.
            exists P'.
            split.
              apply l7_2.
              assumption.
            apply cong_commutativity.
            eapply is_image_spec_col_cong with A B;Col.
          assert (Per B A Q).
            unfold Per.
            exists Q'.
            split.
              apply l7_2.
              assumption.
            apply cong_commutativity.
            eapply is_image_spec_col_cong with A B;Col.
          apply col_permutation_2.

          eapply per_per_col.
            apply l8_2.
            apply H7.
            apply perp_distinct in H3.
            spliter.
            assumption.
          apply l8_2.
          assumption.
        assert (Per A M P).
          unfold Per.
          exists P'.
          split.
            apply l7_2.
            assumption.
          apply cong_commutativity.
          eapply is_image_spec_col_cong.
            apply H1.
          Col.
        assert (Per A M Q).
          unfold Per.
          exists Q'.
          split.
            apply l7_2.
            assumption.
          apply cong_commutativity.
          eapply is_image_spec_col_cong.
            apply H2.
          apply col_trivial_3.
        apply col_permutation_2.
        eapply per_per_col.
          apply l8_2.
          apply H8.
          auto.
        apply l8_2.
        assumption.
      subst P'.
      apply l7_3 in H.
      subst P.
      Col.
    subst Q'.
    apply l7_3 in H0.
    subst Q.
    Col.
Qed.

Lemma l10_10_spec : forall A B P Q P' Q',
 A<>B -> ReflectL P' P A B -> ReflectL Q' Q A B ->
 Cong P Q P' Q'.
Proof.
    intros.
    assert(HH0 := H0).
    assert(HH1 := H1 ).
    unfold ReflectL in H0.
    unfold ReflectL in H1.
    spliter.
    ex_and H0 X.
    ex_and H1 Y.
    assert (exists M, Midpoint M X Y).
      apply midpoint_existence.
    ex_elim H6 M0.
    double P M0 P''.
    double Q M0 Q''.
    double P' M0 P'''.
    apply cong_commutativity.
    induction H3.
      induction H2.
        assert (ReflectL P'' P''' A B).
          apply is_image_is_image_spec .
            assumption.
          eapply (midpoint_preserves_image ) with P P' M0.
            assumption.
            induction (eq_dec_points X Y).
              subst Y.
              apply l7_3 in H7.
              subst X.
              assumption.
            assert_cols.
            ColR.
            apply l10_4.
            apply is_image_is_image_spec;auto.
            assumption.
          assumption.
        assert(P'' <> P''').
          intro.
          subst P'''.
          assert( P' = P).
            eapply l7_9.
              apply H9.
            assumption.
          subst P'.
          apply perp_distinct in H3.
          spliter.
          absurde.
        assert (Midpoint Y P'' P''') by (eauto using symmetry_preserves_midpoint).
        assert (Cong P'' Y P''' Y) by (unfold Midpoint in *; spliter; Cong).
        assert (Cong Q Y Q' Y) by (unfold Midpoint in *;spliter; Cong).
        assert (Col P'' Y Q).
          apply col_permutation_2.
          eapply image_in_col.
            eapply image_image_in.
              apply perp_distinct in H2.
              spliter.
              apply H15.
              apply l10_4_spec.
              apply HH1.
              assumption.
            unfold Col.
            left.
            apply midpoint_bet.
            assumption.
          eapply (image_image_in _ _ _ P''').
            assumption.
            assumption.
            assumption.
          unfold Col.
          left.
          apply midpoint_bet.
          assumption.
        eapply (l4_16 P'' Y Q P P''' Y Q' P').
          repeat split.
            assumption.
            assumption.
            unfold Col in H15.
            induction H15.
              assert(Bet P''' Y Q').
                eapply (l7_15).
                  apply H12.
                  apply l7_3_2.
                  apply H1.
                assumption.
              eapply l2_11.
                apply H15.
                apply H16.
                assumption.
              apply cong_commutativity.
              assumption.
            induction H15.
              assert (Bet Y Q' P''').
                eapply (l7_15).
                  apply l7_3_2.
                  apply H1.
                  apply H12.
                assumption.
              eapply l4_3.
                apply between_symmetry.
                apply H15.
                apply between_symmetry.
                apply H16.
                assumption.
              assumption.
            apply between_symmetry in H15.
            assert (Bet Y P''' Q').
              eapply (l7_15).
                apply l7_3_2.
                apply H12.
                apply H1.
              assumption.
            apply cong_commutativity.
            eapply l4_3.
              apply between_symmetry.
              apply H15.
              apply between_symmetry.
              apply H16.
              assumption.
            assumption.
            apply cong_commutativity.
            assumption.
            assert (Cong P Y P' Y).
              eapply is_image_spec_col_cong.
                eapply l10_4_spec.
                apply HH0.
              assumption.
            assert (Cong P P'' P' P''').
              induction(eq_dec_points X Y).
                subst Y.
                eapply l2_11.
                  apply midpoint_bet.
                  apply H6.
                  apply H9.
                  apply l7_3 in H7.
                  subst X.
                  assumption.
                apply l7_3 in H7.
                subst X.
                eapply cong_transitivity.
                  unfold Midpoint in H6.
                  spliter.
                  apply cong_symmetry.
                  apply H7.
                eapply cong_transitivity.
                  apply H16.
                unfold Midpoint in H9.
                spliter.
                assumption.
              eapply l2_11.
                apply H6.
                apply H9.
                (* pas besoin de deployer ???*)
                eapply is_image_spec_col_cong.
                  apply l10_4_spec.
                  apply HH0.
                unfold Midpoint in H7.
                spliter.
                ColR.
              apply cong_commutativity.
              eapply is_image_spec_col_cong.
                apply H10.
              ColR.
            apply cong_commutativity.
            assumption.
          apply cong_commutativity.
          eapply is_image_spec_col_cong.
            apply l10_4_spec.
            apply HH0.
          assumption.
        intro.
        subst P''.
        apply cong_symmetry in H13.
        apply cong_identity in H13.
        subst P'''.
        absurde.
      subst Q'.
      apply l7_3 in H1.
      subst Q.
      apply cong_commutativity.
      eapply is_image_spec_col_cong.
        (* apply H. *)
        apply l10_4_spec.
        apply HH0.
      assumption.
    subst P'.
    apply l7_3 in H0.
    subst P.
    eapply is_image_spec_col_cong.
      apply l10_4_spec.
      apply HH1.
    assumption.
Qed.

Lemma l10_10 : forall A B P Q P' Q',
  Reflect P' P A B -> Reflect Q' Q A B ->
 Cong P Q P' Q'.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst.
      unfold Reflect in *.
      induction H.
        intuition.
      induction H0.
        intuition.
      spliter.
      apply l7_13 with B; apply l7_2;auto.
    apply l10_10_spec with A B;try apply -> is_image_is_image_spec;assumption.
Qed.

Lemma image_preserves_bet : forall A B C A' B' C' X Y,
   X <> Y ->
  ReflectL A A' X Y -> ReflectL B B' X Y -> ReflectL C C' X Y ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    eapply l4_6.
      apply H3.
    unfold Cong_3.
    repeat split; eapply l10_10_spec.
      apply H.
      apply l10_4_spec.
      assumption.
      apply l10_4_spec; assumption.
      apply H.
      apply l10_4_spec.
      assumption.
      apply l10_4_spec.
      assumption.
      apply H.
      apply l10_4_spec.
      assumption.
    apply l10_4_spec.
    assumption.
Qed.

Lemma image_gen_preserves_bet : forall A B C A' B' C' X Y,
   X <> Y ->
  Reflect A A' X Y ->
  Reflect B B' X Y ->
  Reflect C C' X Y ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    eapply image_preserves_bet;try apply is_image_is_image_spec; eauto.
Qed.

Lemma image_preserves_col : forall A B C A' B' C' X Y,
   X <> Y ->
  ReflectL A A' X Y -> ReflectL B B' X Y -> ReflectL C C' X Y ->
  Col A B C ->
  Col A' B' C'.
Proof.
    intros.
    destruct H3 as [HBet|[HBet|HBet]]; [|apply col_permutation_2|apply col_permutation_1];
    apply bet_col; eapply image_preserves_bet; eauto.
Qed.

Lemma image_gen_preserves_col : forall A B C A' B' C' X Y,
   X <> Y ->
  Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  Col A B C ->
  Col A' B' C'.
Proof.
    intros.
    apply image_preserves_col with A B C X Y; try (apply is_image_is_image_spec); auto.
Qed.

Lemma image_gen_preserves_ncol : forall A B C A' B' C' X Y,
   X <> Y ->
  Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  ~ Col A B C ->
  ~ Col A' B' C'.
Proof.
    intros.
    intro.
    apply H3, image_gen_preserves_col with A' B' C' X Y; try (apply l10_4); assumption.
Qed.

Lemma image_gen_preserves_inter : forall A B C D I A' B' C' D' I' X Y,
  X <> Y ->
  Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y -> Reflect D D' X Y ->
  ~ Col A B C -> C <> D ->
  Col A B I -> Col C D I -> Col A' B' I' -> Col C' D' I' ->
  Reflect I I' X Y.
Proof.
    intros.
    destruct (l10_6_existence X Y I) as [I0 HI0]; trivial.
    assert (I' = I0); [|subst; assumption].
    apply (l6_21 A' B' C' D'); trivial.
      apply image_gen_preserves_ncol with A B C X Y; assumption.
      intro; subst D'; apply H5, l10_2_uniqueness with X Y C'; assumption.
      apply image_gen_preserves_col with A B I X Y; assumption.
      apply image_gen_preserves_col with C D I X Y; assumption.
Qed.

Lemma intersection_with_image_gen : forall A B C A' B' X Y,
  X <> Y ->
  Reflect A A' X Y -> Reflect B B' X Y ->
  ~ Col A B A' -> Col A B C -> Col A' B' C ->
  Col C X Y.
Proof.
    intros.
    apply l10_8.
    assert (Reflect A' A X Y) by (apply l10_4; assumption).
    assert (~ Col A' B' A) by (apply image_gen_preserves_ncol with A B A' X Y; trivial).
    assert_diffs.
    apply image_gen_preserves_inter with A B A' B' A' B' A B; trivial.
    apply l10_4; assumption.
Qed.

Lemma image_preserves_midpoint :
 forall A B C A' B' C' X Y, X <> Y ->
 ReflectL A A' X Y -> ReflectL B B' X Y -> ReflectL C C' X Y ->
 Midpoint A B C ->
 Midpoint A' B' C'.
Proof.
    intros.
    unfold Midpoint in *.
    spliter.
    repeat split.
      eapply image_preserves_bet.
        apply H.
        apply H1.
        apply H0.
        apply H2.
      assumption.
    eapply cong_transitivity.
      eapply l10_10_spec.
        apply H.
        apply H1.
      apply H0.
    eapply cong_transitivity.
      apply H4.
    eapply l10_10_spec.
      apply H.
      apply l10_4_spec.
      apply H0.
    apply l10_4_spec.
    apply H2.
Qed.


Lemma image_preserves_per : forall A B C A' B' C' X Y,
  X <> Y ->
 ReflectL A A' X Y -> ReflectL B B' X Y -> ReflectL C C' X Y ->
 Per A B C ->
 Per A' B' C'.
Proof.
    intros.
    double C B C1.
    assert (exists C1', ReflectL C1 C1' X Y).
      apply l10_6_existence_spec.
      assumption.
    ex_and H5 C1'.
    unfold Per.
    exists C1'.
    split.
      eapply image_preserves_midpoint.
        apply H.
        apply H1.
        apply H2.
        apply H6.
      assumption.
    eapply cong_transitivity.
      eapply l10_10_spec.
        apply H.
        apply H0.
      apply H2.
    eapply cong_transitivity.
      unfold Per in H3.
      ex_and H3 C2.
      assert (C2=C1).
        eapply symmetric_point_uniqueness.
          apply H3.
        assumption.
      subst C2.
      apply H5.
    eapply l10_10_spec.
      apply H.
      apply l10_4_spec.
      assumption.
    apply l10_4_spec.
    assumption.
Qed.

Lemma l10_12 : forall A B C A' B' C',
 Per A B C -> Per A' B' C' ->
 Cong A B A' B' -> Cong B C B' C' ->
 Cong A C A' C'.
Proof.
    intros.
    induction (eq_dec_points B C).
      subst B.
      apply cong_symmetry in H2.
      apply cong_identity in H2.
      subst B'.
      assumption.
    induction (eq_dec_points A B).
      subst B.
      apply cong_symmetry in H1.
      apply cong_identity in H1.
      subst B'.
      assumption.
    assert (exists X, Midpoint X B B').
      apply midpoint_existence.
    ex_and H5 X.
    double A' X A1.
    double C' X C1.
    assert(Cong_3 A' B' C' A1 B C1).
    {
      repeat split.
        eapply l7_13.
          apply l7_2.
          apply H5.
        assumption.
        eapply l7_13.
          apply l7_2.
          apply H5.
        apply l7_2.
        assumption.
      eapply l7_13.
        apply H6.
      apply l7_2.
      assumption.
    }
    assert (Per A1 B C1).
      eapply l8_10.
        apply H0.
      apply H8.

    unfold Cong_3 in H8.
    spliter.
    assert(Cong A B A1 B) by eCong.
    assert(Cong B C B C1) by eCong.

    assert(exists Y, Midpoint Y C C1)
      by (apply midpoint_existence).
    ex_and H14 Y.
    apply cong_symmetry.
    eapply cong_transitivity.
      apply H10.

    induction (eq_dec_points B Y).
    {
      subst Y.
      induction (eq_dec_points A A1).
        subst A1.
        unfold Per in H9.
        ex_and H9 C2.
        assert (C=C2).
          eapply l7_9.
            apply H15.
          apply l7_2.
          assumption.
        subst C2.
        assumption.
      assert(C1 <> B).
        intro.
        subst C1.
        apply l7_2 in H15.
        apply is_midpoint_id in H15.
        contradiction.
      assert (Per  C B A1).
        eapply (l8_3 C1 B A1 C).
          apply l8_2.
          apply H9.
          assumption.
        apply midpoint_col.
        apply l7_2.
        assumption.
      assert(Col A  A1 B).
        assert_cols.
        assert_diffs.

        eapply per_per_col.
          apply H.
          assumption.
        apply l8_2.
        assumption.
      assert (A= A1 \/ Midpoint B A A1).
        eapply l7_20.
          apply col_permutation_5.
          assumption.
        apply cong_commutativity.
        assumption.
      induction H19.
        contradiction.
      eapply l7_13.
        apply H19.
      assumption.
    }
    assert(ReflectL C1 C B Y).
      unfold ReflectL.
      split.
        exists Y.
        split.
          assumption.
        apply col_trivial_2.
      induction(eq_dec_points C C1).
        right.
        assumption.
      left.
      apply perp_sym.
      assert(Y<>C /\ Y <> C1).
        eapply midpoint_distinct_1.
          assumption.
        assumption.
      spliter.
      eapply col_per_perp.
        assumption.
        auto.
        intuition.
        auto.
        apply midpoint_col.
        assumption.
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    induction (is_image_spec_dec A A1 B Y).
      eapply l10_10_spec.
        2:apply H17.
        assumption.
      apply l10_4_spec.
      assumption.
    (*************** cas 2 ***************)
    assert(exists A2, ReflectL A1 A2 B Y).
      apply l10_6_existence_spec.
      assumption.
    ex_elim H18 A2.
    assert (Cong  C A2 C1 A1).
      eapply l10_10_spec.
        2:apply H16.
        assumption.
      assumption.
    assert (Per A2 B C).
      eapply (image_preserves_per A1 B C1 A2 B C).
        2:apply H19.
        assumption.
        apply image_col.
        apply col_trivial_3.
        assumption.
      assumption.
    assert (Cong A1 B A2 B).
      eapply is_image_spec_col_cong.
        apply H19.
      apply col_trivial_3.
    assert (A = A2 \/ Midpoint B A A2).
      eapply l7_20.
        apply col_permutation_1.
        eapply per_per_col.
          apply H20.
          assumption.
        assumption.
      eapply cong_transitivity.
        apply cong_commutativity.
        apply H12.
      apply cong_commutativity.
      assumption.
    induction H22.
      subst A2.
      apply cong_symmetry.
      apply cong_commutativity.
      assumption.
    assert(Cong A C A2 C).
      apply l8_2 in H.
      unfold Per in H.
      ex_and H A3.
      assert(A2=A3).
        eapply symmetric_point_uniqueness.
          apply H22.
        apply H.
      subst A3.
      apply cong_commutativity.
      assumption.
    eapply cong_transitivity.
      apply cong_symmetry.
      apply cong_commutativity.
      apply H18.
    apply cong_symmetry.
    assumption.
Qed.

Lemma l10_16 : forall A B C A' B' P,
 ~ Col A B C -> ~ Col A' B' P -> Cong A B A' B' ->
 exists C', Cong_3 A B C A' B' C' /\ OS  A' B' P C' .
Proof.
    intros.
    induction (eq_dec_points A B).
      subst B.
      apply cong_symmetry in H1.
      apply False_ind.
      apply H.
      apply col_trivial_1.
    assert(exists X, Col A B X /\ Perp A B C X).
      apply l8_18_existence.
      assumption.
    ex_and H3 X.
    assert (exists X', Cong_3 A B X A' B' X').
      eapply l4_14.
        assumption.
      assumption.
    ex_elim H5 X'.
    assert (exists Q, Perp A' B' Q X' /\ OS A' B' P Q).
      apply l10_15.
        eapply l4_13.
          apply H3.
        assumption.
      assumption.
    ex_and H5 Q.
    assert (exists C', Out X' C' Q /\ Cong  X' C' X C).
      eapply l6_11_existence.
        apply perp_distinct in H5.
        spliter.
        assumption.
      intro.
      subst C.
      apply perp_distinct in H4.
      spliter.
      absurde.
    ex_and H8 C'.
    exists C'.
    unfold Cong_3 in *.
    spliter.
    assert (Cong A C A' C').
      induction(eq_dec_points A X).
        subst X.
        apply cong_symmetry in H10.
        apply cong_identity in H10.
        subst X'.
        apply cong_symmetry.
        assumption.
      eapply l10_12.
        3: apply H10.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            assumption.
            apply perp_right_comm.
            apply H4.
          assumption.
          apply col_trivial_3.
        apply col_trivial_1.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            intro assumption.
            subst X'.
            apply cong_identity in H10.
            contradiction.
            apply perp_sym.
            eapply perp_col.
              intro.
              subst X'.
              apply cong_symmetry in H9.
              apply cong_identity in H9.
              subst X.
              apply perp_distinct in H4.
              spliter.
              absurde.
              apply perp_sym.
              apply perp_right_comm.
              apply H5.
            apply col_permutation_5.
            eapply out_col.
            assumption.
          eapply l4_13.
            apply H3.
          unfold Cong_3.
          repeat split;assumption.
          apply col_trivial_3.
        apply col_trivial_1.
      apply cong_symmetry.
      assumption.
    assert (Cong B C B' C').
      induction(eq_dec_points B X).
        subst X.
        apply cong_symmetry in H11.
        apply cong_identity in H11.
        subst X'.
        apply cong_symmetry.
        assumption.
      eapply l10_12.
        3: apply H11.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            assumption.
            apply perp_comm.
            apply H4.
          apply col_permutation_4.
          assumption.
          apply col_trivial_3.
        apply col_trivial_1.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            intro assumption.
            subst X'.
            apply cong_identity in H11.
            contradiction.
            apply perp_sym.
            eapply perp_col.
              intro.
              subst X'.
              apply cong_symmetry in H9.
              apply cong_identity in H9.
              subst X.
              apply perp_distinct in H4.
              spliter.
              absurde.
              apply perp_sym.
              apply perp_comm.
              apply H5.
            apply col_permutation_5.
            eapply out_col.
            assumption.
          apply col_permutation_4.
          eapply l4_13.
            apply H3.
          unfold Cong_3.
          repeat split; assumption.
          apply col_trivial_3.
        apply col_trivial_1.
      apply cong_symmetry.
      assumption.
    repeat split.
      assumption.
      assumption.
      assumption.
    assert (T19 := (l9_19 A' B' C' Q X')).
    assert (OS A' B' C' Q <-> Out X' C' Q /\ ~ Col A' B' C').
      apply T19.
        intro.
        subst B'.
        apply cong_identity in H1.
        contradiction.
        eapply l4_13.
          apply H3.
        unfold Cong_3.
        repeat split; assumption.
      apply col_permutation_1.
      apply out_col.
      assumption.
    apply cong_symmetry in H1.
    destruct H14.
    spliter.
    assert (OS A' B' C' Q).
      apply H15.
      split.
        assumption.
      intro.
      apply H.
      eapply l4_13.
        apply H16.
      unfold Cong_3.
      repeat split.
        assumption.
        apply cong_symmetry.
        assumption.
      apply cong_symmetry.
      assumption.
    eapply one_side_transitivity.
      apply H7.
    apply one_side_symmetry.
    assumption.
Qed.

Lemma image_cong_col : forall A B P P' X,
 P <> P' -> Reflect P P' A B -> Cong P X P' X ->
 Col A B X.
Proof.
    intros.
    unfold Reflect in *.
    induction H0.
      spliter.
      unfold ReflectL in H2.
      spliter.
      ex_and H2 M.
      induction H3.
        induction(eq_dec_points A M).
          subst M.
          assert (Perp P A A B).
            eapply perp_col.
              apply perp_distinct in H3.
              spliter.
              intro.
              subst P.
              apply l7_2 in H2.
              apply is_midpoint_id in H2.
              subst P'.
              absurde.
              apply perp_sym.
              apply perp_right_comm.
              apply H3.
            unfold Col.
            right; left.
            apply midpoint_bet.
            assumption.
          apply perp_comm in H5.
          apply perp_perp_in in H5.
          apply perp_in_comm in H5.
          apply perp_in_per in H5.
          assert (Per X A P).
            unfold Per.
            exists P'.
            split.
              apply l7_2.
              assumption.
            Cong.
          apply l8_2 in H5.
          apply col_permutation_2.
          eapply per_per_col.
            apply H5.
            intro.
            subst P.
            apply l7_2 in H2.
            apply is_midpoint_id in H2.
            subst P'.
            absurde.
          assumption.
        assert (Perp P M M A).
          eapply perp_col.
            intro.
            subst P.
            apply l7_2 in H2.
            apply is_midpoint_id in H2.
            subst P'.
            absurde.
            apply perp_sym.
            apply perp_comm.
            eapply perp_col.
              assumption.
              apply H3.
            assumption.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        apply perp_comm in H6.
        apply perp_perp_in in H6.
        apply perp_in_comm in H6.
        apply perp_in_per in H6.
        assert (Per X M P).
          unfold Per.
          exists P'.
          split.
            apply l7_2.
            assumption.
          apply cong_commutativity.
          assumption.
        apply l8_2 in H6.
        assert (Col A X M).
          eapply per_per_col.
            apply H6.
            intro.
            subst P.
            apply l7_2 in H2.
            apply is_midpoint_id in H2.
            subst P'.
            absurde.
          assumption.
        eapply col_transitivity_1.
          apply H5.
          apply col_permutation_5.
          assumption.
        apply col_permutation_5.
        assumption.
      subst P'.
      absurde.
    spliter;subst;Col.
Qed.

Lemma per_per_cong_1 :
 forall A B X Y, A <> B -> Per A B X -> Per A B Y ->
 Cong B X B Y -> X = Y \/ Midpoint B X Y.
Proof.
    intros.
    (* eauto 6 using l7_20, per_per_col, l8_2, col_permutation_5.
    *)
    eapply l7_20.
      apply col_permutation_5.
      eapply per_per_col with A.
        apply l8_2.
        apply H0.
        auto.
      apply l8_2.
      assumption.
    assumption.
Qed.


Lemma per_per_cong : forall A B X Y,
 A <> B -> Per A B X -> Per A B Y -> Cong B X B Y ->
 X = Y \/ ReflectL X Y A B.
Proof.
    intros.
    assert (Col X Y B).
      eapply per_per_col.
        apply l8_2.
        apply H0.
        auto.
      apply l8_2.
      assumption.
    induction (eq_dec_points X Y).
      left.
      assumption.
    right.
    unfold ReflectL.
    split.
      exists B.
      split.
        assert (X = Y \/ Midpoint B X Y).
          eapply l7_20.
            apply col_permutation_5.
            assumption.
          assumption.
        induction H5.
          contradiction.
        apply l7_2.
        assumption.
      apply col_trivial_2.
    left.
    assert(Perp A B B Y).
      eapply per_perp.
        assumption.
        intro.
        subst Y.
        apply cong_identity in H2.
        subst X.
        absurde.
      assumption.
    apply perp_sym.
    eapply perp_col.
      auto.
      apply perp_sym.
      apply perp_right_comm.
      apply H5.
    apply col_permutation_1.
    assumption.
Qed.

Lemma per_per_cong_gen : forall A B X Y,
 A <> B -> Per A B X -> Per A B Y -> Cong B X B Y ->
 X = Y \/ Reflect X Y A B.
Proof.
    intros.
    assert (X = Y \/ ReflectL X Y A B) by (apply per_per_cong;auto).
    induction H3.
      tauto.
    right.
    unfold Reflect.
    tauto.
Qed.

Lemma two_sides_dec : forall A B C D, TS A B C D \/ ~ TS A B C D.
Proof.
apply upper_dim_implies_two_sides_dec.
apply all_coplanar_implies_upper_dim; unfold all_coplanar_axiom;
apply all_coplanar.
Qed.

(* cleanup the proof *)

Lemma one_side_dec : forall A B C D,
 OS A B C D \/ ~ OS A B C D.
Proof.
    intros.
    elim (Col_dec C A B); intro HCol1.
      right.
      intro H.
      destruct H as [C' [Hts1 Hts2]].
      unfold TS in *.
      intuition.
    elim (Col_dec D A B); intro HCol2.
      right.
      intro H.
      destruct H as [C' [Hts1 Hts2]].
      unfold TS in *.
      intuition.
induction(eq_dec_points C D).
subst D.
left.
apply one_side_reflexivity; auto.
assert(A <> B).
intro.
subst B.
apply HCol1.
Col.

assert( exists X : Tpoint, Col A B X /\ Perp A B D X).
apply(l8_18_existence A B D); Col.
ex_and H1 D'.

induction(eq_dec_points D' B).
subst D'.


assert(exists P T : Tpoint,
       Cong B P B D /\ Perp B A P B /\ Col B A T /\ TS B A C P).
apply(l8_21_bis B A C B D); auto.
intro.
subst D.
apply HCol2.
Col.
Col.
ex_and H3 P.
ex_and H4 T.

assert(Per A B D).
apply perp_in_per.
apply perp_left_comm in H2.
apply perp_perp_in in H2.
Perp.

assert(Per A B P).
apply perp_in_per.
apply perp_perp_in in H4.
Perp.
assert(Col D P B).
apply (per_per_col _ _ A); Perp.

assert(D = P \/ Midpoint B D P).
apply(l7_20 B D P); finish.
apply invert_two_sides in H6.

induction H10.
subst P.
right.
apply l9_9 in H6.
assumption.
left.

assert(TS A B D P).
unfold Midpoint in H10.
spliter.
repeat split; Col.
apply per_not_col in H8.
intro.
apply H8.
Col.
assumption.
intro.
subst P.
apply cong_identity in H11.
subst D.
apply HCol2.
Col.
exists B.
split; Col.
unfold OS.
exists P.
split; auto.

assert(exists P T : Tpoint,
       Cong D' P D' D /\ Perp D' B P D' /\ Col D' B T /\ TS D' B C P).
apply(l8_21_bis D' B C D' D); auto.
intro.
subst D.
apply HCol2.
Col.
intro.
apply HCol1.
ColR.
ex_and H4 P.
ex_and H5 T.

assert(Perp D' B D D').
apply perp_left_comm.
apply(perp_col _ A); Perp.
Col.

assert(Per B D' D).
apply perp_in_per.
apply perp_perp_in in H8.
Perp.


assert(Per B D' P).
apply perp_in_per.
apply perp_perp_in in H5.
Perp.
assert(Col D P D').
apply (per_per_col _ _ B); Perp.
assert(D = P \/ Midpoint D' D P).
apply(l7_20 D' D P); finish.
apply invert_two_sides in H7.

assert(TS A B C P).
apply(col_preserves_two_sides B D' A B C P); Col.

induction H12.
subst P.
right.
apply l9_9 in H13.
assumption.
left.

assert(TS A B D P).
unfold Midpoint in H12.
spliter.
repeat split; Col.
apply per_not_col in H10; auto.
intro.
apply H10.
ColR.
intro.
subst P.
apply cong_identity in H14.
subst D'.
apply perp_distinct in H8.
tauto.
exists D'.
split; Col.
apply(l9_8_1 A B C D P);auto.
Qed.

End T10_2D.
