Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid.

Section T13.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma perp_vector : forall A B, A <> B -> (exists X, exists Y, Perp A B X Y).
Proof.
intros.
assert(HH:=not_col_exists A B H).
ex_and HH P.
assert(HH:=l8_18_existence A B P H0).
ex_and HH P'.
exists P.
exists P'.
assumption.
Qed.

Lemma inter_dec : decidability_of_intersection.
Proof.
apply strong_parallel_postulate_implies_inter_dec.
apply strong_parallel_postulate_SPP.
cut tarski_s_parallel_postulate.
apply result_similar_to_beeson_s_one; simpl; tauto.
unfold tarski_s_parallel_postulate; apply euclid.
Qed.

Lemma tarski_s_euclid : tarski_s_parallel_postulate.
Proof.
unfold tarski_s_parallel_postulate.
apply euclid.
Qed.

Lemma not_par_inter_exists : forall A1 B1 A2 B2,
  ~Par A1 B1 A2 B2 -> exists X, Col X A1 B1 /\ Col X A2 B2.
Proof.
    intros.
    apply inter_dec_implies_not_par_inter_exists; try assumption.
    apply inter_dec.
Qed.

Lemma parallel_unicity :
 forall A1 A2 B1 B2 C1 C2 P : Tpoint,
  Par A1 A2 B1 B2 -> Col P B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2.
Proof.
    intros.
    apply tarski_s_euclid_implies_playfair with A1 A2 P; try assumption.
    apply tarski_s_euclid.
Qed.

Lemma par_trans : forall A1 A2 B1 B2 C1 C2,
  Par A1 A2 B1 B2 -> Par B1 B2 C1 C2 -> Par A1 A2 C1 C2.
Proof.
    intros.
    apply playfair_implies_par_trans with B1 B2; try assumption.
    unfold playfair_s_postulate.
    apply parallel_unicity.
Qed.

Lemma l12_16 : forall A1 A2 B1 B2 C1 C2 X,
  Par A1 A2 B1 B2 -> Inter A1 A2 C1 C2 X -> exists Y, Inter B1 B2 C1 C2 Y.
Proof.
    intros.
    assert(HH:= H).
    unfold Par in H.
    induction H.
      unfold Inter in H0.
      spliter.
      ex_and H0 P.
      assert(HNCol : ~Col B1 B2 X) by (intro; unfold Par_strict in H; spliter; apply H7; exists X; Col).
      assert(HH1 := l8_18_existence B1 B2 X HNCol).
      ex_and HH1 X0.
      assert(HPar : ~Par B1 B2 C1 C2).
        intro.
        assert(Par A1 A2 C1 C2) by (apply par_trans with B1 B2; assumption).
        assert(~Par A1 A2 C1 C2).
          apply col_not_col_not_par.
            exists X; Col.
          exists P; Col.
        contradiction.
      apply not_par_inter_exists in HPar.
      ex_and HPar Y.
      exists Y.
      split; try Col.
      exists X.
      split.
        Col.
      intro.
      apply HNCol; Col.
    unfold Inter in H0.
    spliter.
    ex_and H0 P.
    exists X.
    split.
      exists P.
      split.
        Col.
      intro.
      apply H6.
      apply (col3 B1 B2); Col.
    split; try Col.
    apply par_symmetry in HH.
    unfold Par in HH.
    induction HH.
      unfold Par_strict in H7.
      spliter.
      apply False_ind.
      apply H10.
      exists A1.
      split; try Col.
    spliter.
    apply (col3 A1 A2); Col.
Qed.

Lemma lea_cases :
 forall A B C D E F,
  A <> B -> C <> B -> D <> E -> F <> E ->
  LeA A B C D E F \/ LeA D E F A B C.
Proof.
    intros.
    assert(HH:= or_bet_out A B C).
    induction HH.
      right.
      apply l11_31_2; assumption.
    induction H3.
      left.
      apply l11_31_1; assumption.
    assert(HH:= or_bet_out D E F).
    induction HH.
      left.
      apply l11_31_2; assumption.
    induction H4.
      right.
      apply l11_31_1; assumption.
    assert(exists C', CongA  D E F A B C' /\ OS A B C' C).
      apply angle_construction_1.
        assumption.
      assumption.
    ex_and H5 C'.
    induction(two_sides_dec B C A C').
      unfold TS in H7.
      spliter.
      ex_and H10 X.
      assert(A <> X).
        intro.
        subst X.
        contradiction.
      assert(Out A X C').
        apply bet_out.
          auto.
          intro.
          subst C'.
          apply between_equality in H11.
            subst X.
            absurde.
          apply between_trivial.
        assumption.
      assert(~Col A B X).
        intro.
        apply H3.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ X).
          intro.
          subst X.
          unfold OS in H6.
          ex_and H6 C0.
          unfold TS in *.
          spliter.
          ex_and H21 T0.
          ex_and H18 T1.
          apply bet_col in H11.
          apply H19.
          apply col_permutation_2.
          assumption.
          apply col_permutation_4.
          assumption.
        apply col_permutation_1.
        assumption.
      assert(OS A B X C').
        apply out_one_side.
          left.
          assumption.
        assumption.
      assert(OS A B C X).
        eapply one_side_transitivity.
          apply one_side_symmetry.
          apply H6.
        apply one_side_symmetry.
        assumption.
      assert(Out B X C).
        eapply col_one_side_out.
          apply col_permutation_4.
          assumption.
        apply invert_one_side.
        apply one_side_symmetry.
        apply H16.
      left.
      apply l11_29_b.
      exists C'.
      split.
        unfold InAngle.
        repeat split; try assumption.
          intro.
          subst C'.
          unfold OS in H6.
          ex_and H6 C0.
          unfold TS in *.
          spliter.
          apply H22.
          apply col_trivial_3.
        exists X.
        split.
          assumption.
        right.
        assumption.
      apply conga_sym.
      assumption.
    induction(Col_dec B C C').
      unfold Col in H8.
      induction H8.
        apply bet_out in H8.
          assert(CongA D E F A B C).
            eapply out_conga.
              apply H5.
              apply out_trivial.
              auto.
              apply out_trivial.
              auto.
              apply out_trivial.
              auto.
            apply l6_6.
            assumption.
          left.
          eapply (l11_30 A B C A B C).
            apply lea_refl.
              assumption.
            assumption.
            apply conga_refl.
              assumption.
            assumption.
          apply conga_sym.
          assumption.
          assumption.
        intro.
        subst C'.
        apply between_identity in H8.
        subst C.
        absurde.
      induction H8.
        apply between_symmetry in H8.
        apply bet_out in H8.
          assert(CongA D E F A B C).
            eapply out_conga.
              apply H5.
              apply out_trivial.
              auto.
              apply out_trivial.
              auto.
              apply out_trivial.
              auto.
            assumption.
          left.
          eapply (l11_30 A B C A B C).
            apply lea_refl.
              assumption.
            assumption.
            apply conga_refl.
              assumption.
            assumption.
          apply conga_sym.
          assumption.
          unfold OS in H6.
          ex_and H6 C0.
          unfold TS in H6.
          spliter.
          intro.
          subst C'.
          apply H10.
          apply col_trivial_3.
        assumption.
      assert (TS A B C' C).
        repeat split.
          assumption.
          intro.
          apply H4.
          eapply col_conga_col.
            apply col_permutation_1.
            apply H9.
          apply conga_sym.
          assumption.
          intro.
          apply H3.
          apply col_permutation_1.
          assumption.
        exists B.
        split.
          apply col_trivial_3.
        assumption.
      apply l9_9 in H9.
      contradiction.
    right.
    apply not_two_sides_one_side in H7.
      2:auto.
      2:assumption.
      assert(TS B C' A C).
        eapply l9_31.
          apply invert_one_side.
          assumption.
        apply one_side_symmetry.
        assumption.
      unfold TS in H9.
      spliter.
      ex_and H12 T.
      unfold LeA.
      exists C'.
      split.
        unfold InAngle.
        repeat split; try assumption.
          auto.
        exists T.
        split.
          assumption.
        right.
        unfold Col in H12.
        induction H12.
          assert(OS A B T C).
            apply out_one_side.
              right.
              assumption.
            apply bet_out.
              intro.
              subst T.
              apply H10.
              apply bet_col.
              assumption.
              intro.
              subst C.
              apply between_identity in H13.
              subst T.
              apply H10.
              apply bet_col.
              assumption.
            assumption.
          assert(TS A B C' T).
            repeat split.
              assumption.
              intro.
              apply H10.
              apply col_permutation_1.
              assumption.
              intro.
              apply H10.
              apply col_permutation_2.
              eapply (col_transitivity_1 _ T).
                intro.
                subst T.
                unfold OS in H14.
                ex_and H14 C0.
                unfold TS in H14.
                spliter.
                apply H17.
                apply col_trivial_3.
                apply bet_col in H12.
                apply col_permutation_4.
                assumption.
              apply col_permutation_2.
              assumption.
            exists B.
            split.
              apply col_trivial_3.
            apply between_symmetry.
            assumption.
          assert(TS A B C' C).
            apply l9_2.
            eapply l9_8_2.
              apply l9_2.
              apply H15.
            assumption.
          apply l9_9 in H16.
          contradiction.
        repeat split.
          intro.
          subst T.
          apply H3.
          apply bet_col.
          assumption.
          auto.
        induction H12.
          right.
          assumption.
        left.
        apply between_symmetry.
        assumption.
      assumption.
    intro.
    apply H8.
    apply col_permutation_1.
    assumption.
Qed.

Lemma or_lta_conga_gta : forall A B C D E F,
 A <> B -> C <> B -> D <> E -> F <> E ->
 LtA A B C D E F \/ GtA  A B C D E F \/ CongA A B C D E F.
Proof.
    intros.
    assert(HH:=lea_cases A B C D E F H H0 H1 H2).
    induction HH.
      induction(conga_dec A B C D E F).
        right; right.
        assumption.
      left.
      unfold LtA.
      split; assumption.
    induction(conga_dec A B C D E F).
      right; right.
      assumption.
    right; left.
    unfold GtA.
    unfold LtA.
    split.
      assumption.
    intro.
    apply H4.
    apply conga_sym.
    assumption.
Qed.

Lemma not_lta_gea : forall  A B C D E F,
 A <> B -> C <> B -> D <> E -> F <> E ->
 ~ LtA A B C D E F ->
 GeA A B C D E F.
Proof.
    intros.
    assert(HH:=or_lta_conga_gta A B C D E F H H0 H1 H2).
    induction HH.
      contradiction.
    unfold GeA.
    induction H4.
      unfold GtA in H4.
      unfold LtA in H4.
      spliter.
      assumption.
    unfold LeA.
    exists C.
    split.
      apply in_angle_trivial_2; assumption.
    apply conga_sym.
    assumption.
Qed.

Lemma par_strict_one_side : forall A B C D P,
 Par_strict A B C D -> Col C D P -> OS A B C P.
Proof.
    intros.
    assert(HH:= H).
    unfold Par_strict in HH.
    spliter.
    apply l12_6 in H.
    unfold OS in *.
    ex_and H C'.
    exists C'.
    split.
      assumption.
    apply not_one_side_two_sides.
      assumption.
      intro.
      apply H4.
      exists P.
      split; Col.
      unfold TS in H.
      spliter.
      assumption.
    intro.
    apply H4.
    unfold OS in H6.
    ex_and H6 P'.
    assert(OS A B P C').
      eapply l9_8_1.
        apply H6.
      assumption.
    assert(TS A B P C).
      eapply l9_8_2.
        apply l9_2.
        apply H.
      apply one_side_symmetry.
      assumption.
    unfold TS in H9.
    spliter.
    ex_and H12 T.
    exists T.
    split.
      assumption.
    induction(eq_dec_points C P).
      subst P.
      apply between_identity in H13.
      subst T.
      apply col_trivial_1.
    eapply col_permutation_2.
    eapply (col_transitivity_1 _ P).
      assumption.
      Col.
    apply bet_col in H13.
    Col.
Qed.

Lemma par_strict_all_one_side : forall A B C D,
 Par_strict A B C D -> (forall P, Col C D P -> OS A B C P).
Proof.
    intros.
    eapply par_strict_one_side.
      apply H.
    assumption.
Qed.

Lemma Par_dec : forall A B C D, Par A B C D \/ ~ Par A B C D.
Proof.
    intros.
    intros.
    elim (eq_dec_points A B); intro HAB.
      subst.
      right.
      unfold Par.
      intro H.
      induction H.
        unfold Par_strict in *.
        intuition.
      intuition.
    elim (eq_dec_points C D); intro HCD.
      subst.
      right.
      unfold Par.
      intro H.
      induction H.
        unfold Par_strict in *.
        intuition.
      intuition.
    elim (parallel_existence_spec A B C HAB);intros D' HD'.
    destruct HD' as [HCD' HPar].
    elim (Col_dec C D D'); intro HCol.
      left.
      apply par_col_par with D';Par;Col.
    right.
    intro H.
    apply HCol.
    assert (Par C D C D') by (apply par_trans with A B;Par;apply par_symmetry;assumption).
    apply par_id_3;apply par_symmetry;assumption.
Qed.

Lemma par_not_par : forall A B C D P Q, Par A B C D -> ~Par A B P Q -> ~Par C D P Q.
Proof.
    intros.
    apply par_trans_implies_par_not_par with A B; Par.
    unfold postulate_of_transitivity_of_parallelism.
    apply par_trans.
Qed.

Lemma par_inter : forall A B C D P Q X, Par A B C D -> ~Par A B P Q -> Col P Q X -> Col A B X -> exists Y, Col P Q Y /\ Col C D Y.
Proof.
    intros A B C D P Q X HPar HNPar HCol1 HCol2.
    elim (eq_dec_points P Q); intro HDiff; treat_equalities.

      {
      exists C; Col.
      }

      {
      elim (Col_dec A B P); intro HNC1; elim (Col_dec A B Q); intro HNC2.

        {
        apply par_distincts in HPar; spliter.
        exfalso; apply HNPar; right; repeat (split; Col; try ColR).
        }

        {
        assert (HY : exists Y : Tpoint, Col X Q Y /\ Col C D Y).
          {
          apply inter_dec_plus_par_trans_imply_proclus with A B; Col.
          apply inter_dec.
          unfold postulate_of_transitivity_of_parallelism.
          apply par_trans.
          }
        show_distinct Q X; Col.
        destruct HY as [Y [HCol3 HCol4]]; exists Y; split; ColR.
        }

        {
        assert (HY : exists Y : Tpoint, Col X P Y /\ Col C D Y).
          {
          apply inter_dec_plus_par_trans_imply_proclus with A B; Col.
          apply inter_dec.
          unfold postulate_of_transitivity_of_parallelism.
          apply par_trans.
          }
        show_distinct P X; Col.
        destruct HY as [Y [HCol3 HCol4]]; exists Y; split; ColR.
        }

        {
        assert (HY : exists Y : Tpoint, Col X Q Y /\ Col C D Y).
          {
          apply inter_dec_plus_par_trans_imply_proclus with A B; Col.
          apply inter_dec.
          unfold postulate_of_transitivity_of_parallelism.
          apply par_trans.
          }
        show_distinct Q X; Col.
        destruct HY as [Y [HCol3 HCol4]]; exists Y; split; ColR.
        }
      }
Qed.

Lemma l12_19 :
  forall A B C D ,
   ~Col A B C -> Par A B C D -> Par B C D A ->
   Cong A B C D /\ Cong B C D A /\ TS B D A C /\ TS A C B D.
Proof.
    intros.
    assert(exists P, Midpoint P A C) by (eapply midpoint_existence).
    ex_and H2 P.
    double B P D'.
    assert(Cong C D' A B).
      eapply (l7_13 P); assumption.
    assert(Cong B C D' A).
      eapply (l7_13 P).
        apply l7_2.
        assumption.
      assumption.
    assert(Par A B C D').
      eapply l12_17.
        intro.
        subst B.
        apply H.
        apply col_trivial_1.
        apply H3.
      assumption.
    assert(Par C D C D').
      eapply par_trans.
        apply par_symmetry.
        apply H0.
      apply H6.
    assert(Col C D D').
      unfold Par in H7.
      induction H7.
        unfold Par_strict in H7.
        spliter.
        apply False_ind.
        apply H10.
        exists C.
        split; apply col_trivial_1.
      spliter.
      Col.
    assert(Par B C D' A).
      eapply l12_17.
        intro.
        subst B.
        apply H.
        apply col_trivial_2.
        apply H2.
      apply l7_2.
      assumption.
    assert(Par D A D' A).
      eapply par_trans.
        apply par_symmetry.
        apply H1.
      assumption.
    assert(Col A D D').
      unfold Par in H10.
      induction H10.
        unfold Par_strict in H10.
        spliter.
        apply False_ind.
        apply H13.
        exists A.
        split; apply col_trivial_3.
      spliter.
      Col.
    assert(D = D').
      eapply l6_21.
        4: apply H11.
        5: apply H8.
        intro.
        apply H.
        assert(Col P C D).
          apply col_permutation_2.
          eapply (col_transitivity_1 _ A).
            intro.
            subst C.
            apply H.
            apply col_trivial_3.
            Col.
          unfold Midpoint in H3.
          spliter.
          apply bet_col in H3.
          Col.
        assert(Col P C D').
          apply col_permutation_2.
          eapply (col_transitivity_1 _ D).
            apply par_distincts in H0.
            spliter.
            assumption.
            Col.
          Col.
        assert(Col P A D').
          eapply (col_transitivity_1 _ C).
            intro.
            subst P.
            apply l7_2 in H3.
            apply is_midpoint_id in H3.
            subst C.
            apply H.
            apply col_trivial_3.
            unfold Midpoint in H3.
            spliter.
            apply bet_col in H3.
            Col.
          assumption.
        eapply (col3 P D').
          intro.
          subst D'.
          apply l7_2 in H2.
          apply is_midpoint_id in H2.
          subst P.
          apply H.
          unfold Midpoint in H3.
          spliter.
          apply bet_col.
          assumption.
          Col.
          unfold Midpoint in H2.
          spliter.
          apply bet_col in H2.
          Col.
        Col.
      apply par_distincts in H0.
      spliter.
      assumption.
      apply col_trivial_2.
      apply col_trivial_2.
    subst D'.
    split.
      Cong.
    split.
      Cong.
    assert(B <> D).
      intro.
      subst D.
      apply  l7_3 in H2.
      subst P.
      apply H.
      unfold Par in H0.
      induction H0.
        unfold Par_strict in H0.
        spliter.
        apply  False_ind.
        apply H13.
        exists B.
        split; apply col_trivial_3.
      spliter.
      Col.
    unfold Midpoint in *.
    spliter.
    split.
      eapply l12_18_c.
        Cong.
        Cong.
        assumption.
        assumption.
        apply bet_col.
        apply H3.
      apply bet_col.
      assumption.
    eapply l12_18_d.
      Cong.
      Cong.
      assumption.
      assumption.
      apply bet_col.
      apply H3.
    apply bet_col.
    assumption.
Qed.

Lemma l12_20_bis :
  forall A B C D,
   Par A B C D -> Cong A B C D -> TS B D A C ->
   Par B C D A /\ Cong B C D A /\ TS A C B D.
Proof.
    intros.
    induction(eq_dec_points B C).
      subst C.
      unfold TS in H1.
      spliter.
      apply False_ind.
      apply H3.
      apply col_trivial_1.
    induction(eq_dec_points A D).
      subst D.
      unfold TS in H1.
      spliter.
      apply False_ind.
      apply H3.
      apply col_trivial_3.
    assert(~ Col A B C).
      intro.
      assert(Col A B D).
        eapply not_strict_par1.
          2: apply H4.
          2: apply col_trivial_2.
        apply par_right_comm.
        assumption.
      unfold TS in H1.
      spliter.
      contradiction.
    assert(exists P, Midpoint P A C) by (apply midpoint_existence).
    ex_and H5 P.
    double B P D'.
    assert(Par B C D' A).
      eapply l12_17.
        assumption.
        apply H5.
      apply l7_2.
      assumption.
    assert(Par A B C D').
      eapply l12_17.
        intro.
        subst B.
        apply H4.
        apply col_trivial_1.
        apply H6.
      assumption.
    assert(Cong C D' A B).
      eapply (l7_13 P); assumption.
    assert(Cong B C D' A).
      eapply (l7_13 P).
        apply l7_2.
        assumption.
      assumption.
    assert(Par C D C D').
      eapply par_trans.
        apply par_symmetry.
        apply H.
      assumption.
    assert(Col C D D').
      unfold Par in H11.
      induction H11.
        unfold Par_strict in H11.
        spliter.
        apply False_ind.
        apply H14.
        exists C.
        split; apply col_trivial_1.
      spliter.
      Col.
    assert(Cong C D C D').
      eapply (cong_transitivity _ _ A B).
        Cong.
      Cong.
    assert(D = D' \/ Midpoint C D D').
      eapply l7_20.
        Col.
      assumption.
    induction H14.
      subst D'.
      assert(Par B C D A).
        eapply l12_17.
          assumption.
          apply H5.
        apply l7_2.
        assumption.
      split.
        assumption.
      assert(HH:=l12_19 A B C D H4 H H14).
      spliter.
      split; assumption.
    (************)
    assert(TS A C B D).
      apply par_two_sides_two_sides.
        assumption.
      assumption.
    assert(HH:= H15).
    assert(HH1:=H1).
    unfold TS in H15, H1.
    spliter.
    ex_and H21 T.
    ex_and H18 T'.
    assert(T = T').
      apply bet_col in H22.
      apply bet_col in H23.
      eapply (l6_21 A C B D); Col.
    subst T'.
    assert(~Col B C T).
      intro.
      apply H16.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ T).
        intro.
        treat_equalities.
        apply H20.
        apply bet_col in H23.
        Col.
        Col.
      Col.
    assert(OS B C T D).
      eapply out_one_side_1.
        assumption.
        assumption.
        apply col_trivial_3.
      apply bet_out in H23.
        assumption.
        intro.
        treat_equalities.
        apply H24.
        apply col_trivial_3.
      auto.
    assert(OS B C T A).
      eapply out_one_side_1.
        assumption.
        assumption.
        apply col_trivial_2.
      apply between_symmetry in H22.
      apply bet_out in H22.
        assumption.
        intro.
        treat_equalities.
        apply H24.
        apply col_trivial_2.
      assumption.
    assert(OS B C A D).
      apply (one_side_transitivity _ _ _ T).
        apply one_side_symmetry.
        assumption.
      assumption.
    assert(TS B C D D').
      unfold TS.
      repeat split.
        assumption.
        intro.
        apply H20.
        Col.
        intro.
        apply H20.
        eapply (col_transitivity_1 _ D').
          intro.
          treat_equalities.
          apply H17.
          apply col_trivial_3.
          Col.
        Col.
      exists C.
      split.
        apply col_trivial_3.
      unfold Midpoint in H14.
      spliter.
      assumption.
    assert(TS B C A D').
      eapply l9_8_2.
        apply H28.
      apply one_side_symmetry.
      assumption.
    unfold Par in H7.
    induction H7.
      unfold Par_strict in H7.
      spliter.
      apply False_ind.
      apply H32.
      unfold TS in H29.
      spliter.
      ex_and H35 X.
      exists X.
      split.
        assumption.
      apply bet_col in H36.
      Col.
    spliter.
    apply False_ind.
    apply H4.
    eapply (col_transitivity_1 _ P).
      intro.
      subst P.
      apply is_midpoint_id in H6.
      tauto.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ D').
        intro.
        subst.
        apply l7_3 in H5.
        subst P.
        apply H4.
        unfold Midpoint in H6.
        spliter.
        auto.
        apply bet_col.
        assumption.
        Col.
      unfold Midpoint in H5.
      spliter.
      apply bet_col in H5.
      Col.
    unfold Midpoint in H6.
    spliter.
    apply bet_col in H6.
    Col.
Qed.

Lemma l12_20 :
 forall A B C D,
  Par A B C D -> Cong A B C D -> TS A C B D ->
  Par B C D A /\ Cong B C D A /\ TS A C B D.
Proof.
    intros.
    assert(TS B D A C).
      apply par_two_sides_two_sides.
        apply par_comm.
        assumption.
      assumption.
    assert(HH:=l12_20_bis A B C D H H0 H2).
    spliter.
    split.
      assumption.
    split.
      assumption.
    assumption.
Qed.

Lemma par_one_or_two_sides :
 forall A B C D,
  Par_strict A B C D ->
 TS A C B D /\ TS B D A C \/ OS A C B D /\ OS B D A C.
Proof.
    intros.
    induction(two_sides_dec A C B D).
      left.
      split.
        assumption.
      apply par_two_sides_two_sides.
        apply par_comm.
        unfold Par.
        left.
        assumption.
      assumption.
    right.
    assert(HH:=H).
    unfold Par_strict in H.
    spliter.
    assert(A <> C).
      intro.
      subst C.
      apply H3.
      exists A.
      split; Col.
    assert(B <> D).
      intro.
      subst D.
      apply H3.
      exists B.
      split; Col.
    split.
      apply not_two_sides_one_side.
        assumption.
        intro.
        apply H3.
        exists C.
        split; Col.
        intro.
        apply H3.
        exists A.
        split; Col.
      assumption.
    apply not_two_sides_one_side.
      assumption.
      intro.
      apply H3.
      exists D.
      split; Col.
      intro.
      apply H3.
      exists B.
      split; Col.
    intro.
    apply H0.
    apply par_two_sides_two_sides.
      left.
      assumption.
    assumption.
Qed.

Lemma l12_21_a :
 forall A B C D,
  TS A C B D ->
  (Par A B C D -> CongA B A C D C A).
Proof.
    intros.
    assert(TS B D A C).
      apply par_two_sides_two_sides.
        apply par_comm.
        assumption.
      assumption.
    assert(B <> C).
      intro.
      subst B.
      unfold TS in H.
      spliter.
      apply H2.
      apply col_trivial_3.
    assert(~Col B C D).
      unfold TS in H1.
      spliter.
      intro.
      apply H4.
      Col.
    assert(Inter B C D C C).
      repeat split.
        exists D.
        split.
          apply col_trivial_1.
        intro.
        apply H3.
        Col.
        apply col_trivial_2.
      apply col_trivial_2.
    assert(HH:= parallel_existence B C A H2).
    ex_and HH X.
    ex_and H5 Y.
    assert(HH:=l12_16 B C X Y D C C H6 H4).
    ex_and HH D'.
    apply par_distincts in H0.
    spliter.
    assert(~Col A B C).
      intro.
      unfold Par in H0.
      induction H0.
        unfold Par_strict in H0.
        spliter.
        apply H14.
        exists C.
        split; Col.
      spliter.
      contradiction.
    assert(Par B C A D').
      eapply par_col2_par.
        intro.
        subst D'.
        unfold Par in H0.
        induction H0.
          unfold Par_strict in H0.
          spliter.
          apply H14.
          unfold Inter in H7.
          ex_and H8 P.
          exists A.
          split; Col.
        spliter.
        contradiction.
        apply H6.
        Col.
      unfold Inter in H8.
      spliter.
      assumption.
    assert(Par_strict A B C D).
      unfold Par in H0.
      induction H0.
        assumption.
      spliter.
      apply False_ind.
      apply H11.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ D).
        assumption.
        Col.
      Col.
    assert(Par_strict B C A D').
      unfold Par in H12.
      induction H12.
        assumption.
      spliter.
      unfold Par_strict.
      repeat split; try assumption; try apply all_coplanar.
      intro.
      ex_and H17 P.
      apply H11.
      eapply col_transitivity_1.
        apply H14.
        Col.
      Col.
    assert(Par A B C D').
      eapply par_col_par.
        intro.
        subst D'.
        unfold Par_strict in H14.
        spliter.
        apply H17.
        exists C.
        split; Col.
        apply H0.
      unfold Inter in H8.
      spliter.
      Col.
    apply par_right_comm in H12.
    assert(HH:= l12_19 A B C D' H11 H15 H12).
    spliter.
    assert(A <> C).
      unfold TS in H19.
      spliter.
      assumption.
    assert(CongA B A C D' C A).
      apply cong3_conga.
        auto.
        auto.
      repeat split; Cong.
    eapply l11_10.
      apply H21.
      apply out_trivial.
      auto.
      apply out_trivial.
      auto.
      unfold Inter in H8.
      spliter.
      induction H23.
        assert(OS A C D D').
          eapply l9_8_1.
            apply l9_2.
            apply H.
          apply l9_2.
          assumption.
        assert(TS A C D D').
          unfold TS.
          repeat split.
            assumption.
            unfold TS in H.
            spliter.
            assumption.
            unfold TS in H19.
            spliter.
            assumption.
          exists C.
          split.
            apply col_trivial_3.
          assumption.
        apply l9_9 in H25.
        contradiction.
      induction H23.
        apply bet_out in H23.
          apply l6_6.
          assumption.
          intro.
          treat_equalities.
          auto.
        auto.
      apply between_symmetry in H23.
      apply bet_out in H23.
        assumption.
        auto.
      intro.
      treat_equalities.
      auto.
    apply out_trivial.
    auto.
Qed.

Lemma l12_21 : forall A B C D,
 TS A C B D ->
 (CongA B A C D C A <-> Par A B C D).
Proof.
    intros.
    split.
      intro.
      apply l12_21_b ; assumption.
    intro.
    apply l12_21_a; assumption.
Qed.

Lemma l12_22_a : forall A B C D P,
 Out P A C -> OS P A B D -> Par A B C D ->
 CongA B A P D C P.
Proof.
    intros.
    unfold Par in H1.
    induction H1.
      assert(~Col A B C).
        intro.
        unfold Par_strict in H1.
        spliter.
        apply H5.
        exists C.
        Col.
      assert( A <> C).
        intro.
        treat_equalities.
        assert(HH := not_par_strict_id A B D).
        contradiction.
      assert(HH:= parallel_existence A C B H3).
      ex_and HH X.
      ex_and H4 Y.
      assert(Inter A C C D C).
        apply inter_right_comm.
        apply inter_trivial.
        intro.
        unfold Par_strict in H1.
        spliter.
        apply H10.
        exists A.
        split; Col.
      assert(HH:= l12_16 A C X Y C D C H5 H7).
      ex_and HH D'.
      assert(Par A C B D').
        eapply par_col2_par.
          intro.
          unfold Par_strict in H1.
          spliter.
          unfold Inter in H8.
          spliter.
          treat_equalities.
          apply H12.
          exists B.
          Col.
          apply H5.
          Col.
        unfold Inter in H8.
        spliter; assumption.
      assert(Par A B C D').
        eapply par_col_par.
          intro.
          treat_equalities.
          apply H2.
          apply par_comm in H9.
          apply par_id in H9.
          Col.
          unfold Par.
          left.
          apply H1.
        unfold Inter in H8.
        spliter.
        assumption.
      assert(Par_strict A C B D').
        unfold Par in H9.
        induction H9.
          assumption.
        spliter.
        apply False_ind.
        apply H2.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ D').
          assumption.
          Col.
        Col.
      assert(Cong A B D' C /\ Cong B D' C A /\ TS B C A D' /\ TS A D' B C).
        eapply l12_19.
          eapply par_not_col.
            apply H11.
          Col.
          apply par_right_comm.
          assumption.
        apply par_symmetry.
        apply par_left_comm.
        assumption.
      spliter.
      prolong C A C' C A.
      assert(Par B D' A C').
        eapply par_col_par.
          intro.
          treat_equalities.
          tauto.
          unfold Par.
          left.
          apply par_strict_symmetry.
          apply H11.
        apply bet_col in H16.
        Col.
      assert(Cong B D' A C').
        eCong.
      assert(Par_strict A B C D').
        unfold Par in H10.
        induction H10.
          assumption.
        spliter.
        apply False_ind.
        apply H2.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ D').
          intro.
          treat_equalities.
          tauto.
          Col.
        Col.
      assert(HH := l12_6 A B C D' H20).
      assert(TS A B C C').
        unfold TS.
        repeat split.
          intro.
          treat_equalities.
          apply H2.
          Col.
          intro.
          apply H2.
          Col.
          intro.
          apply H2.
          eapply (col_transitivity_1 _ C').
            intro.
            treat_equalities.
            tauto.
            Col.
          apply bet_col in H16.
          Col.
        exists A.
        split.
          Col.
        assumption.
      assert(TS A B D' C').
        eapply l9_8_2.
          apply H21.
        assumption.
      assert(TS C' D' A B).
        apply par_two_sides_two_sides.
          apply par_comm.
          apply par_symmetry.
          assumption.
        apply l9_2.
        assumption.
      apply l9_2 in H23.
      apply invert_two_sides in H22.
      assert(HH1:= l12_20 B D' A C' H18 H19 H22).
      spliter.
      assert(Cong_3 D' C A B A C').
        repeat split; Cong.
      apply cong3_conga in H27.
        assert(OS A C D D').
          eapply one_side_transitivity with B.
            apply col_one_side with P.
              apply out_col in H.
              Col.
              assumption.
            apply invert_one_side.
            apply one_side_symmetry.
            apply H0.
          apply l12_6.
          induction H9.
            assumption.
          spliter.
          apply False_ind.
          apply H2.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ D').
            assumption.
            Col.
          Col.
        assert(Out C D' D).
          unfold Inter in H8.
          spliter.
          induction H30.
            apply l6_6.
            apply bet_out.
              intro.
              treat_equalities.
              unfold Par_strict in H1.
              tauto.
              intro.
              treat_equalities.
              unfold TS in H14.
              spliter.
              apply H12.
              Col.
            assumption.
          induction H30.
            apply bet_out.
              intro.
              treat_equalities.
              unfold CongA in H27.
              tauto.
              intro.
              treat_equalities.
              unfold CongA in H27.
              tauto.
            apply between_symmetry.
            assumption.
          assert(TS A C D D').
            unfold TS.
            repeat split.
              auto.
              unfold OS in H28.
              ex_and H28 K.
              unfold TS in H28.
              tauto.
              unfold OS in H28.
              ex_and H28 K.
              unfold TS in H31.
              tauto.
            exists C.
            split.
              Col.
            apply between_symmetry.
            assumption.
          apply l9_9 in H31.
          contradiction.
        unfold Out in H.
        spliter.
        induction H31.
          assert(Out C A C').
            unfold Out.
            repeat split.
              assumption.
              intro.
              subst C'.
              apply between_identity in H16.
              subst C.
              assert(HX:=not_par_strict_id A B D').
              apply HX.
              contradiction.
            left.
            assumption.
          assert(CongA D' C A D C P).
            eapply l11_10.
              apply conga_refl.
                3: apply H29.
              3:apply H32.
              intro.
              treat_equalities.
              unfold Out in H29.
              tauto.
              intro.
              treat_equalities.
              unfold TS in H22.
              spliter.
              apply H12.
              Col.
              apply out_trivial.
              intro.
              treat_equalities.
              unfold Out in H29.
              tauto.
            unfold Out.
            repeat split.
              intro.
              treat_equalities.
              unfold CongA in H27.
              tauto.
              intro.
              treat_equalities.
              unfold TS in H14.
              spliter.
              apply H13.
              Col.
            unfold Out in H32.
            spliter.
            induction H34.
              eapply (l5_1 _ A).
                auto.
                apply between_symmetry.
                assumption.
              assumption.
            right.
            eapply between_exchange4.
              apply H34.
            apply between_symmetry.
            assumption.
          assert(CongA B A P B A C').
            eapply l11_10.
              apply (conga_refl B A P).
                intro.
                treat_equalities.
                apply H2.
                Col.
              intro.
              treat_equalities.
              tauto.
              apply out_trivial.
              intro.
              treat_equalities.
              unfold CongA in H33.
              tauto.
              apply out_trivial.
              intro.
              treat_equalities.
              tauto.
              apply out_trivial.
              intro.
              treat_equalities.
              unfold CongA in H33.
              tauto.
            unfold Out.
            repeat split.
              intro.
              treat_equalities.
              unfold Out in H32.
              tauto.
              auto.
            eapply (l5_2 C).
              auto.
              assumption.
            apply between_symmetry.
            assumption.
          eapply conga_trans.
            apply H34.
          eapply conga_trans.
            apply conga_sym.
            apply H27.
          assumption.
        apply conga_comm.
        assert(CongA D C A B A C').
          eapply l11_10.
            apply H27.
            apply l6_6.
            assumption.
            apply out_trivial.
            assumption.
            apply out_trivial.
            intro.
            treat_equalities.
            apply H2.
            Col.
          apply out_trivial.
          intro.
          treat_equalities.
          apply H2.
          Col.
        eapply l11_13.
          apply conga_comm.
          apply conga_sym.
          apply H32.
          eapply outer_transitivity_between.
            apply between_symmetry.
            apply H16.
            apply between_symmetry.
            assumption.
          assumption.
          auto.
          apply between_symmetry.
          assumption.
        auto.
        intro.
        treat_equalities.
        unfold TS in H14.
        spliter.
        apply H13.
        Col.
      assumption.
    spliter.
    induction(eq_dec_points A C).
      treat_equalities.
      unfold Out in H.
      spliter.
      assert(HH:= H0).
      unfold OS in HH.
      ex_and HH T.
      unfold TS in *.
      spliter.
      induction H4.
        assert(TS P A B D).
          unfold TS.
          repeat split.
            auto.
            assumption.
            assumption.
          exists A.
          split.
            Col.
          assumption.
        apply l9_9 in H14.
        contradiction.
      induction H4.
        eapply l11_10.
          apply (conga_refl B A P).
            auto.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          unfold Out.
          repeat split.
            auto.
            auto.
          left.
          assumption.
        apply out_trivial.
        auto.
      eapply l11_10.
        apply (conga_refl B A P).
          auto.
        auto.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        unfold Out.
        repeat split.
          auto.
          auto.
        right.
        apply between_symmetry.
        assumption.
      apply out_trivial.
      auto.
    unfold OS in H0.
    ex_and H0 T.
    unfold TS in *.
    spliter.
    apply False_ind.
    apply H7.
    apply col_permutation_1.
    eapply (col_transitivity_1 _ C).
      assumption.
      Col.
    unfold Out in H.
    spliter.
    induction H14; apply bet_col in H14; Col.
Qed.

Lemma l12_22 :
  forall A B C D P,
  Out P A C -> OS P A B D ->
  (CongA B A P D C P <-> Par A B C D).
Proof.
    intros.
    split; intro.
      eapply (l12_22_b _ _ _ _ P); assumption.
    apply l12_22_a; assumption.
Qed.

Lemma l12_23 :
 forall A B C,
  ~Col A B C ->
  exists B', exists C',
  TS A C B B' /\ TS A B C C' /\
      Bet B' A C' /\ CongA A B C B A C' /\ CongA A C B C A B'.
Proof.
    intros.
    assert(exists B0, Midpoint B0 A B) by (apply midpoint_existence).
    assert(exists C0, Midpoint C0 A C) by (apply midpoint_existence).
    ex_and H0 B0.
    ex_and H1 C0.
    prolong B C0 B' B C0.
    prolong C B0 C' C B0.
    exists B'.
    exists C'.
    assert(TS A C B B').
      eapply mid_two_sides.
        intro.
        treat_equalities.
        apply H.
        Col.
        apply H0.
        intro.
        apply H.
        Col.
      split.
        assumption.
      Cong.
    assert(TS A B C C').
      eapply mid_two_sides.
        intro.
        treat_equalities.
        apply H.
        Col.
        apply H2.
        assumption.
      split.
        assumption.
      Cong.
    split.
      assumption.
    split.
      assumption.
    assert(Par A B' C B).
      eapply l12_17.
        intro.
        treat_equalities.
        assert(C0 = B0).
          eapply l7_17.
            2: apply H2.
          split.
            apply between_symmetry.
            assumption.
          Cong.
        subst C0.
        assert(B=C).
          eapply symmetric_point_unicity.
            apply H2.
          assumption.
        subst C.
        apply H.
        Col.
        apply H0.
      split.
        apply between_symmetry.
        assumption.
      Cong.
    assert(Par A C' B C).
      eapply l12_17.
        intro.
        treat_equalities.
        assert(C0 = B0).
          eapply l7_17.
            apply H0.
          split.
            apply between_symmetry.
            assumption.
          Cong.
        subst C0.
        assert(B=C).
          eapply symmetric_point_unicity.
            apply H2.
          assumption.
        subst C.
        apply H.
        Col.
        apply H2.
      split.
        apply between_symmetry.
        assumption.
      Cong.
    assert(Par A B' A C').
      eapply par_trans.
        apply H8.
      apply par_symmetry.
      apply par_right_comm.
      assumption.
    apply par_id in H10.
    assert(OS A C B0 C').
      eapply out_one_side_1.
        intro.
        treat_equalities.
        apply H.
        Col.
        intro.
        apply H.
        eapply (col_transitivity_1 _ B0).
          intro.
          treat_equalities; unfold TS.
          apply H.
          apply is_midpoint_id in H2; subst; Col.
          unfold Midpoint in H2.
          spliter.
          apply bet_col in H2.
          Col.
        Col.
        apply col_trivial_2.
      unfold Out.
      repeat split.
        intro.
        treat_equalities.
        unfold TS in H7.
        spliter.
        ex_and H11 T.
        apply between_identity in H12.
        subst T.
        contradiction.
        intro.
        treat_equalities; repeat split.
        unfold TS in H7.
        spliter.
        unfold Midpoint in H2.
        spliter.
        apply bet_col in H2.
        apply H7.
        Col.
      left.
      assumption.
    assert(OS A C B0 B).
      eapply out_one_side_1.
        intro.
        treat_equalities.
        apply H.
        Col.
        intro.
        apply H.
        eapply (col_transitivity_1 _ B0).
          intro.
          treat_equalities; unfold TS.
          apply H.
          apply is_midpoint_id in H2; subst; Col.
          unfold Midpoint in H2.
          spliter.
          apply bet_col in H2.
          Col.
        Col.
        apply col_trivial_3.
      unfold Out.
      repeat split.
        intro.
        treat_equalities.
        unfold TS in H7.
        apply is_midpoint_id in H2; subst.
        tauto.
        intro.
        treat_equalities; repeat split.
        unfold TS in H7.
        tauto.
      unfold Midpoint in H2.
      spliter.
      left.
      assumption.
    assert(OS A C B C').
      eapply one_side_transitivity.
        2:apply H11; intro.
      apply one_side_symmetry.
      assumption.
    assert(TS A C B' C').
      apply l9_2.
      eapply l9_8_2.
        apply H6.
      assumption.
    split.
      unfold TS in H14.
      spliter.
      ex_and H17 T.
      assert(A = T).
        eapply (l6_21 A C B' C').
          intro.
          apply H15.
          Col.
          intro.
          treat_equalities.
          contradiction.
          Col.
          Col.
          Col.
          apply bet_col in H18.
          Col.
      subst T.
      assumption.
    split.
      apply l9_2 in H7.
      assert(HH:= l12_21_a A C' B C H7 H9).
      apply conga_comm.
      apply conga_sym.
      assumption.
    apply par_symmetry in H8.
    apply invert_two_sides in H6.
    assert(HH:= l12_21_a C B A B' H6 H8).
    apply conga_comm.
    assumption.
Qed.

(* TODO remove duplicate *)
Lemma parallel_trans : forall A B C D E F, Par A B C D -> Par C D E F -> Par A B E F.
Proof.
    intros.
    assert(H1:=par_distinct A B C D H).
    assert(H2:=par_distinct C D E F H0).
    spliter.
    assert(P0:=H).
    assert(P1:=H0).
    induction(Col_dec A E F).
      right.
      repeat split; auto.
      induction H; induction H0.
        assert(Col E A B /\ Col F A B).
          apply (parallel_unicity C D A B E F A).
            apply par_symmetry.
            assumption.
            Col.
            assumption.
          assumption.
        spliter.
        ColR.
        assert(Col E A B /\ Col F A B).
          spliter.
          apply (parallel_unicity C D A B E F A).
            apply par_symmetry.
            assumption.
            Col.
            assumption.
          assumption.
        spliter.
        ColR.
        spliter.
        assert(Col A E F /\ Col B E F).
          apply (parallel_unicity C D E F A B A).
            assumption.
            Col.
            apply par_symmetry.
            assumption.
          Col.
        spliter.
        Col.
      spliter.
      assert(Col C D E).
        ColR.
      assert(Col C D F).
        ColR.
      eapply col3.
        apply H2.
        Col.
        Col.
      Col.
    left.
    unfold Par_strict.
    repeat split; auto; try apply all_coplanar.
    intro.
    ex_and H6 P.
    apply H5.
    induction H; induction H0.
      assert(Col A E F /\ Col B E F).
        apply(parallel_unicity C D E F A B P); auto.
        apply par_symmetry.
        assumption.
      spliter.
      assumption.
      spliter.
      assert(Col A E F /\ Col B E F).
        apply(parallel_unicity C D E F A B P); auto.
        apply par_symmetry.
        assumption.
      spliter.
      assumption.
      assert(Col A E F /\ Col B E F).
        apply(parallel_unicity C D E F A B P); auto.
        apply par_symmetry.
        assumption.
      spliter.
      assumption.
    spliter.
    assert(Col C D E).
      ColR.
    assert(Col C D F).
      ColR.
    eapply col3.
      apply H2.
      Col.
      assumption.
    assumption.
Qed.

Lemma not_par_strict_inter_exists :
 forall A1 B1 A2 B2,
  ~Par_strict A1 B1 A2 B2 ->
  exists X, Col X A1 B1 /\ Col X A2 B2.
Proof.
    intros.
    induction (eq_dec_points A1 B1).
      subst.
      exists A2.
      Col.
    induction (eq_dec_points A2 B2).
      subst.
      exists A1.
      Col.
    induction (inter_dec A1 B1 A2 B2).
      assumption.
    unfold Par_strict in H.
    exfalso.
    apply H.
    repeat split; try assumption; try apply all_coplanar.
Qed.

Lemma not_par_inter : forall A B A' B' X Y, ~Par  A B A' B' -> (exists P, Col P X Y /\ (Col P A B \/ Col P A' B')).
Proof.
    intros.
    induction(Par_dec A B X Y).
      assert(~ Par A' B' X Y).
        intro.
        apply H.
        apply(par_trans _ _ X Y); Par.
      assert(HH:=not_par_inter_exists A' B' X Y H1).
      ex_and HH P.
      exists P.
      split.
        Col.
      right.
      Col.
    assert(HH:=not_par_inter_exists A B X Y H0).
    ex_and HH P.
    exists P.
    split.
      Col.
    left.
    Col.
Qed.

Lemma not_par_one_not_par : forall A B A' B' X Y, ~Par  A B A' B' -> ~Par A B X Y \/ ~Par A' B' X Y.
Proof.
    intros.
    assert(HH:=not_par_inter A B A' B' X Y H).
    ex_and HH P.
    induction(Par_dec A B X Y).
      right.
      intro.
      apply H.
      apply(par_trans _ _ X Y); Par.
    left.
    auto.
Qed.

Lemma col_par_par_col : forall A B C A' B' C', Col A B C -> Par A B A' B' -> Par B C B' C' -> Col A' B' C'.
Proof.
    intros.
    apply par_distincts in H0.
    apply par_distincts in H1.
    spliter.
    assert(Par A B B C).
      right.
      repeat split; Col.
    assert(Par A' B' B' C').
      apply (par_trans _ _ A' B').
        Par.
      apply (par_trans _ _ B C).
        apply (par_trans _ _ A B); Par.
      Par.
    induction H7.
      apply False_ind.
      apply H7.
      exists B'.
      split; Col.
    spliter.
    Col.
Qed.

Lemma parallel_existence1 : forall A B P, A <> B -> exists Q, Par A B P Q.
Proof.
    intros.
    assert(HH:=parallel_existence A B P H).
    ex_and HH X.
    ex_and H0 Y.
    apply par_distincts in H1.
    spliter.
    induction(eq_dec_points P X).
      exists Y.
      apply par_symmetry.
      apply par_comm.
      apply (par_col_par_2 _ X).
        intro.
        subst X.
        subst Y.
        tauto.
        Col.
      Par.
    exists X.
    apply par_symmetry.
    apply par_comm.
    apply (par_col_par_2 _ Y).
      intro.
      subst X.
      tauto.
      Col.
    Par.
Qed.

Lemma par_strict_not_col : forall A B C D, Par_strict A B C D -> forall X, Col A B X -> ~Col C D X.
Proof.
    intros.
    intro.
    unfold Par_strict in H.
    spliter.
    apply H4.
    exists X.
    split; Col.
Qed.

Lemma perp_inter_exists : forall A B C D, Perp A B C D -> exists P, Col A B P /\ Col C D P.
Proof.
    intros.
    apply perp_not_par in H.
    apply not_par_inter_exists in H.
    ex_and H P.
    exists P.
    split;Col.
Qed.


Lemma perp_inter_perp_in : forall A B C D, Perp A B C D -> exists P, Col A B P /\ Col C D P /\ Perp_at P A B C D.
Proof.
    intros.
    assert(HH:=perp_inter_exists A B C D H).
    ex_and HH P.
    exists P.
    split.
      Col.
    split.
      Col.
    apply l8_14_2_1b_bis; Col.
Qed.

End T13.
