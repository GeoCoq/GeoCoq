(* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch13_3_angles.


Ltac anga_instance_o a A B P C :=
	assert(tempo_anga:= anga_const_o a A B P);
        match goal with
           |H: anga a |-  _ => assert(tempo_H:= H); apply tempo_anga in tempo_H; ex_elim tempo_H C
        end;
        clear tempo_anga.

Section Cosinus.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

(************************************* cos *****************************)

Lemma perp2_sym : forall A B C D P, Perp2 A B C D P -> Perp2 C D A B P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Definition lcos := fun lb lc a => lg lb /\ lg lc /\ anga a /\
                                  (exists A, exists B, exists C, (Per C B A /\ lb A B /\ lc A C /\ a B A C)).

Lemma l13_6 : forall a lc ld l, lcos lc l a -> lcos ld l a -> eqL lc ld.
Proof.
    intros.
    unfold lcos in *.
    spliter.
    ex_and H6 X1.
    ex_and H7 Y1.
    ex_and H6 Z1.
    ex_and H3 X2.
    ex_and H10 Y2.
    ex_and H3 Z2.
    clean_duplicated_hyps.
    assert(is_len X1 Z1 l).
      split; auto.
    assert(is_len X2 Z2 l).
      split; auto.
    assert(Cong X1 Z1 X2 Z2).
      eapply (is_len_cong _ _ _ _ l); auto.
    assert(is_anga Y1 X1 Z1 a).
      split; auto.
    assert(is_anga Y2 X2 Z2 a).
      split; auto.
    assert(Conga Y1 X1 Z1 Y2 X2 Z2).
      apply (is_anga_conga _ _ _ _ _ _ a); split; auto.
    assert(is_len X1 Y1 lc).
      split; auto.
    assert(is_len X2 Y2 ld).
      split; auto.
    induction(eq_dec_points Z1 Y1).
      subst Z1.
      assert(out X2 Y2 Z2).
        apply (eq_conga_out Y1 X1); auto.
      assert(Y2 = Z2).
        assert(Z2 = Y2 \/ X2 = Y2).
          apply l8_9.
            auto.
          apply out_col in H19.
          Col.
        induction H20.
          auto.
        unfold out in H19.
        spliter.
        subst Y2.
        tauto.
      subst Z2.
      assert(eqL l lc).
        apply ex_eql.
        exists X1.
        exists Y1.
        split; auto.
      assert(eqL l ld).
        apply ex_eql.
        exists X2.
        exists Y2.
        split; auto.
     transitivity l;auto.
     symmetry; auto.
    assert(Z2 <> Y2).
      intro.
      subst Z2.
      assert(out X1 Y1 Z1).
        apply (eq_conga_out Y2 X2).
        apply conga_sym.
        auto.
      assert(Y1 = Z1).
        assert(Z1 = Y1 \/ X1 = Y1).
          apply l8_9.
            auto.
          apply out_col in H20.
          Col.
        induction H21.
          auto.
        subst Y1.
        unfold out in H20.
        spliter.
        tauto.
      subst Z1.
      tauto.
    apply conga_distinct in H16.
    spliter.
    assert(Conga X1 Y1 Z1 X2 Y2 Z2).
      apply l11_16; Perp; auto.
    assert(~Col Z1 X1 Y1).
      intro.
      assert(X1 = Y1 \/ Z1 = Y1).
        apply l8_9.
          Perp.
        Col.
      induction H27.
        subst Y1.
        tauto.
      contradiction.
    apply conga_comm in H16.
    apply cong_commutativity in H13.
    assert(HH:=l11_50_2 Z1 X1 Y1 Z2 X2 Y2 H26 H25 H16 H13).
    spliter.
    apply ex_eql.
    exists X1.
    exists Y1.
    split.
      auto.
    eapply is_len_cong_is_len.
      apply H18.
    Cong.
Qed.

Lemma null_lcos_eql : forall lp l a, lcos lp l a -> is_null_anga a -> eqL l lp.
Proof.
    intros.
    unfold lcos in H.
    spliter.
    ex_and H3 A.
    ex_and H4 B.
    ex_and H3 C.
    unfold is_null_anga in H0.
    spliter.
    assert(HH:= H7 B A C H6).
    assert(Col A B C) by (apply out_col;auto).
    assert(Col C B A) by Col.
    assert(HQ:= l8_9 C B A H3 H9).
    induction HQ.
      subst C.
      apply (all_eql A B).
        split; auto.
      split; auto.
    subst B.
    exfalso.
    unfold out in HH.
    tauto.
Qed.

Lemma eql_lcos_null : forall l lp a, lcos l lp a -> eqL l lp -> is_null_anga a.
Proof.
    intros.
    unfold lcos in H.
    spliter.
    ex_and H3 B.
    ex_and H4 A.
    ex_and H3 C.
    assert(forall A0 B0 : Tpoint, l A0 B0 <-> lp A0 B0).
      apply H0; auto.
    assert(HP:= (H7 B A)).
    assert(HQ:= (H7 B C)).
    destruct HP.
    destruct HQ.
    assert(l B C).
      apply H11.
      auto.
    assert(lp B A).
      apply H8.
      auto.
    clear H7 H8 H9 H10 H11.
    assert(Cong B A B C).
      apply (lg_cong l); auto.
    unfold Per in H3.
    ex_and H3 B'.
    assert(HH:= anga_distinct a A B C H2 H6).
    spliter.
    assert(A = C).
      eapply (l4_18 B B').
        intro.
        subst B'.
        apply l7_3 in H3.
        contradiction.
        unfold is_midpoint in H3; assert(HH:= midpoint_col).
        spliter.
        apply bet_col in H3.
        Col.
        auto.
      unfold is_midpoint in H3.
      spliter.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply cong_commutativity.
        apply H11.
      eapply cong_transitivity.
        apply cong_commutativity.
        apply H7.
      Cong.
    subst C.
    unfold is_null_anga.
    split.
      auto.
    intros A0 B0 C0 HP.
    apply (eq_conga_out A B).
    apply (anga_conga a); auto.
Qed.

Lemma lcos_lg_not_null: forall l lp a, lcos l lp a -> ~lg_null l /\ ~lg_null lp.
Proof.
    intros.
    unfold lcos in H.
    spliter.
    ex_and H2 A.
    ex_and H3 B.
    ex_and H2 C.
    assert(HH:= anga_distinct a B A C H1 H5).
    spliter.
    unfold lg_null.
    split; intro; spliter; ex_and H9 X.
      assert (Cong A B X X) by (apply (lg_cong l); auto).
      treat_equalities;intuition.
    assert(Cong A C X X) by (apply (lg_cong lp); auto).
    treat_equalities;intuition.
Qed.

Lemma anga_col_out : forall a A B C, anga a -> a A B C -> Col A B C -> out B A C.
Proof.
    intros.
    assert(acute A B C).
      apply (anga_acute a); auto.
    unfold Col in H1.
    induction H1.
      apply acute_not_bet in H2.
      contradiction.
    unfold out.
    apply (anga_distinct a A B C) in H.
      spliter.
      repeat split; auto.
      induction H1.
        right.
        auto.
      left.
      Between.
    auto.
Qed.

Lemma perp_acute_out : forall A B C C', acute A B C -> Perp A B C C' -> Col A B C' -> out B A C'.
Proof.
    intros.
    assert (HH:= H).
    unfold acute in HH.
    ex_and HH A0.
    ex_and H2 B0.
    ex_and H3 C0.
    assert(HH:=H3).
    unfold lta in HH.
    spliter.
    unfold lea in H4.
    ex_and H4 P0.
    apply conga_distinct in H6.
    spliter.
    assert(C' <> B).
      intro.
      subst C'.
      assert(Per A B C).
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in; auto.
        Perp.
      unfold InAngle in H4.
      spliter.
      apply H5.
      apply l11_16; auto.
    induction H1.
      apply False_ind.
      assert(HH:= H4).
      unfold InAngle in HH.
      spliter.
      ex_and H15 X.
      induction H16.
        subst X.
        assert(~ Col A0 B0 C0).
          apply per_not_col; auto.
        assert(Col A0 B0 C0).
          apply bet_col.
          auto.
        contradiction.
      assert(lea A B C A0 B0 C0).
        unfold lta in H3.
        spliter.
        auto.
      assert(HQ:= l11_29_a A B C A0 B0 C0 H17).
      ex_and HQ Q.
      assert(Per A B Q).
        apply (l11_17 A0 B0 C0).
          auto.
        apply conga_sym.
        auto.
      assert(Perp_in B Q B A B).
        apply perp_in_right_comm.
        apply per_perp_in.
          apply conga_distinct in H19.
          spliter.
          auto.
          auto.
        apply l8_2.
        auto.
      assert(HH:= perp_in_perp Q  B A B B H21).
      induction HH.
        apply perp_distinct in H22.
        tauto.
      assert(HH:= l12_9 Q B  C C' A B).
      assert(Par Q B C C').
        apply HH; try apply all_coplanar; Perp.
      assert(one_side B Q C C').
        apply l12_6.
        induction H23.
          apply par_strict_left_comm.
          auto.
        spliter.
        apply False_ind.
        assert(~Col B C' C).
          apply per_not_col; auto.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_comm.
          apply (perp_col _ A); Perp.
          apply bet_col in H1.
          Col.
        apply H27.
        Col.
      assert(one_side Q B C A).
        eapply in_angle_one_side.
          intro.
          assert(~ Col B Q A).
            apply( perp_not_col).
            Perp.
          apply H26.
          Col.
          intro.
          apply H11.
          eapply (l8_18_unicity A B Q).
            intro.
            assert(~Col B A Q).
              apply perp_not_col.
              Perp.
            apply H27.
            Col.
            apply bet_col in H1.
            Col.
            apply perp_sym.
            apply perp_left_comm.
            eapply (perp_col _ C).
              intro.
              subst Q.
              unfold one_side in H24.
              ex_and H24 T.
              unfold two_sides in H26.
              spliter.
              apply H27.
              Col.
              Perp.
            unfold Par in H23.
            induction H23.
              apply False_ind.
              apply H23.
              exists C.
              split; Col.
            spliter.
            Col.
            Col.
          Perp.
        apply l11_24.
        auto.
      apply invert_one_side in H25.
      assert(one_side B Q A C').
        eapply one_side_transitivity.
          apply one_side_symmetry.
          apply H25.
        assumption.
      assert(~ Col B A Q).
        apply perp_not_col.
        Perp.
      assert(two_sides B Q A C').
        unfold two_sides.
        repeat split; auto.
          apply perp_distinct in H22.
          spliter.
          auto.
          intro.
          apply H27.
          Col.
          intro.
          apply H27.
          apply bet_col in H1.
          ColR.
        exists B.
        split.
          Col.
        auto.
      apply l9_9_bis in H26.
      contradiction.
    unfold out.
    repeat split; auto.
    induction H1.
      right.
      auto.
    left.
    Between.
Qed.

End Cosinus.

Section Cosinus2.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

(*
Lemma perp_out_acute : forall A B C C', out B A C' -> Perp A B C C' -> Col A B C' -> acute A B C.
Proof.
    intros.
    assert(A <> B /\ C <> C' /\ B <> C').
      apply perp_distinct in H0.
      unfold out in H.
      spliter.
      repeat split; auto.
    spliter.
    assert(acute C' B C).
      assert(Perp C' B C C').
        apply perp_left_comm.
        apply (perp_col _ A); Col.
        Perp.
      assert(exists M, is_midpoint M B C).
        apply midpoint_existence.
      ex_and H6 M.
      prolong C' M P C' M.
      assert(is_midpoint M C' P).
        split; Cong.
      assert(Plg C' B P C).
        unfold Plg.
        split.
          right.
          intro.
          subst C.
          apply l7_3 in H7.
          subst M.
          apply perp_not_col in H5.
          apply H5.
          Col.
        exists M.
        split; auto.
      assert(Parallelogram C' B P C).
        apply plg_to_parallelogram.
        auto.
      induction H11.
        unfold acute.
        exists C'.
        exists B.
        exists P.
        split.
          assert(Rectangle C' B P C).
            apply plg_per_rect1.
              auto.
            apply perp_in_per.
            apply perp_in_comm.
            apply perp_perp_in.
            apply perp_sym.
            apply (perp_col _ A); Perp.
            apply out_col in H.
            auto.
          eapply (rect_per2 _ _ _ C).
          auto.
        unfold lta.
        split.
          unfold lea.
          exists C.
          split.
            apply plgs_in_angle.
            auto.
          apply conga_refl; auto.
          intro.
          subst C.
          apply perp_not_col in H5.
          apply H5.
          Col.
        assert(Par_strict C C' B P /\ Par_strict C P C' B).
          apply plgs_par_strict.
          apply plgs_permut.
          apply plgs_permut.
          apply plgs_permut.
          auto.
        spliter.
        intro.
        apply l11_22_aux in H14.
        induction H14.
          apply H12.
          apply out_col in H14.
          exists C.
          split; Col.
        apply par_strict_symmetry in H13.
        apply l12_6 in H13.
        apply l9_9 in H14.
        contradiction.
      unfold Parallelogram_flat in H11.
      spliter.
      apply perp_not_col in H5.
      contradiction.
    assert(C <> B).
      apply acute_distinct in H5.
      spliter.
      auto.
    assert(Conga A B C C' B C).
      apply (out_conga C' B C C' B C).
        apply conga_refl;  auto.
        apply l6_6.
        auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      apply out_trivial; auto.
    apply (acute_lea_acute A B C C' B C).
      auto.
    unfold lea.
    exists C.
    split.
      apply in_angle_trivial_2; auto.
    auto.
Qed.
*)


Lemma perp_out__acute : forall A B C C', Perp A B C C' -> Col A B C' -> (acute A B C <-> out B A C').
Proof.
    intros.
    split.
      intro.
      apply (perp_acute_out _ _ C); auto.
    intro.
    apply (perp_out_acute _ _ C C'); auto.
Qed.

Lemma obtuse_not_acute : forall A B C, obtuse A B C -> ~ acute A B C.
Proof.
    intros.
    intro.
    unfold obtuse in H.
    unfold acute in H0.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    ex_and H0 A1.
    ex_and H2 B1.
    ex_and H0 C1.
    assert(A0 <> B0 /\ C0 <> B0 /\ A1 <> B1 /\ C1 <> B1 /\ A <> B /\ C <> B).
      unfold gta in H1.
      unfold lta in *.
      unfold lea in *.
      spliter.
      ex_and H1 P0.
      ex_and H2 P.
      unfold InAngle in H2.
      unfold Conga in H5 .
      unfold Conga in H6 .
      spliter.
      repeat split; auto.
    spliter.
    assert(Conga A0 B0 C0 A1 B1 C1).
      apply l11_16; auto.
    assert(gta A B C A1 B1 C1).
      apply (conga_preserves_gta A B C A0 B0 C0).
        apply conga_refl; auto.
        auto.
      assumption.
    assert(HH:=not_lta_and_gta A B C A1 B1 C1).
    apply HH.
    split; auto.
Qed.

Lemma acute_not_obtuse : forall A B C, acute A B C -> ~ obtuse A B C.
Proof.
    intros.
    intro.
    apply obtuse_not_acute in H0.
    contradiction.
Qed.

Lemma perp_obtuse_bet : forall A B C C', Perp A B C C' -> Col A B C' -> obtuse A B C -> Bet A B C'.
Proof.
    intros.
    assert(HH:= H1).
    unfold obtuse in HH.
    ex_and HH A0.
    ex_and H2 B0.
    ex_and H3 C0.
    assert(A0 <> B0 /\ C0 <> B0 /\ A <> B /\ C <> B).
      unfold gta in H3.
      unfold lta in H3.
      spliter.
      unfold lea in H3.
      ex_and H3 P.
      unfold Conga in H5.
      spliter.
      repeat split; auto.
      intro.
      subst C.
      apply perp_comm in H.
      apply perp_not_col in H.
      apply H.
      Col.
    spliter.
    assert(B <> C').
      intro.
      subst C'.
      assert(Per A B C).
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        Perp.
      assert(Conga A0 B0 C0 A B C).
        apply l11_16; auto.
      unfold gta in H3.
      unfold lta in H3.
      spliter.
      unfold lea in H3.
      contradiction.
    induction H0.
      auto.
    assert(out B A C').
      unfold out.
      repeat split; auto.
      induction H0.
        right.
        auto.
      left.
      Between.
    eapply (perp_out_acute _ _ C) in H9.
      apply obtuse_not_acute in H1.
      contradiction.
      auto.
Qed.
(*
Lemma perp_bet_obtuse : forall A B C C', B <> C' -> Perp A B C C' -> Col A B C' -> Bet A B C' -> obtuse A B C.
Proof.
    intros.
    assert(exists M, is_midpoint M B C).
      apply midpoint_existence.
    ex_and H3 M.
    prolong C' M P C' M.
    assert(is_midpoint M C' P).
      unfold is_midpoint.
      split; auto.
      Cong.
    assert(Plg B C' C P).
      unfold Plg.
      split.
        left.
        intro.
        subst C.
        apply perp_comm in H0.
        apply perp_not_col in H0.
        apply H0.
        Col.
      exists M.
      split; auto.
    assert(Parallelogram B C' C P).
      apply plg_to_parallelogram.
      auto.
    induction H8.
      assert(Par_strict B C' C P /\ Par_strict B P C' C).
        apply plgs_par_strict.
        auto.
      spliter.
      apply plgs_comm2 in H8.
      assert(Rectangle C' B P C).
        apply plg_per_rect.
          apply parallelogram_to_plg.
          left.
          auto.
        left.
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        apply perp_sym.
        apply (perp_col _ A).
          intro.
          subst C'.
          unfold Par_strict in H9.
          tauto.
          Perp.
        Col.
      assert(Per C' B P).
        eapply rect_per1.
        apply plg_per_rect.
          apply H7.
        right; left.
        apply perp_in_per.
        apply perp_in_sym.
        apply perp_perp_in.
        apply perp_comm.
        apply (perp_col _ A).
          auto.
          Perp.
        Col.
      assert(A <> B /\ C <> B /\ P <> B).
        apply perp_distinct in H0.
        spliter.
        repeat split.
          auto.
          intro.
          subst C.
          apply H10.
          exists B.
          split; Col.
        intro.
        subst P.
        apply H10.
        exists C.
        split; Col.
      spliter.
      unfold obtuse.
      exists A.
      exists B.
      exists P.
      split.
        apply l8_2.
        eapply (per_col _ _ C').
          auto.
          Perp.
        Col.
      unfold gta.
      unfold lta.
      split.
        unfold lea.
        exists P.
        split.
          unfold InAngle.
          repeat split; auto.
          assert(one_side B P C C').
            apply l12_6.
            apply par_strict_right_comm.
            auto.
          assert(two_sides B P A C').
            unfold two_sides.
            repeat split.
              auto.
              intro.
              apply H9.
              exists P.
              split.
                ColR.
              Col.
              intro.
              apply H10.
              exists C'.
              split; Col.
            exists B.
            split; Col.
          assert(two_sides B P C A).
            eapply l9_8_2.
              apply l9_2.
              apply H17.
            apply one_side_symmetry.
            auto.
          unfold two_sides in H18.
          spliter.
          ex_and H21 T.
          exists T.
          split.
            repeat split.
            Between.
          right.
          assert(~ Col T A B).
            intro.
            assert(T = B).
              apply bet_col in H22.
              apply (inter_unicity B A P B); Col.
            subst T.
            apply bet_col in H22.
            assert(Col B C C').
              ColR.
            apply H9.
            exists C.
            split; Col.
          induction H21.
            assert(one_side A B T C).
              eapply out_one_side_1.
                auto.
                intro.
                apply H23.
                Col.
                apply col_trivial_3.
              unfold out.
              repeat split.
                intro.
                subst T.
                apply bet_col in H21.
                contradiction.
                intro.
                unfold one_side in H16.
                subst C.
                apply between_identity in H22.
                subst T.
                apply bet_col in H21.
                contradiction.
              left.
              Between.
            assert(one_side A B C P).
              apply l12_6.
              unfold Par_strict.
              repeat split; auto; try apply all_coplanar.
                intro.
                subst P.
                apply H10.
                exists C.
                split; Col.
              intro.
              ex_and H25 K.
              apply H9.
              exists K.
              split.
                ColR.
              auto.
            assert(one_side A B T P).
              eapply one_side_transitivity.
                apply H24.
              auto.
            assert(two_sides A B T P).
              unfold two_sides.
              repeat split.
                auto.
                auto.
                intro.
                unfold two_sides in H17.
                spliter.
                apply H28.
                Col.
              exists B.
              split.
                Col.
              Between.
            apply l9_9 in H27.
            contradiction.
          unfold out.
          repeat split.
            intro.
            subst T.
            apply H23.
            Col.
            intro.
            subst P.
            apply H10.
            exists C.
            split; Col.
          induction H21.
            right.
            auto.
          left.
          Between.
        apply conga_refl.
          auto.
        auto.
      assert(Per P B A).
        apply (per_col _ _ C').
          auto.
          Perp.
        Col.
      intro.
      assert(Per A B C).
        apply (l11_17 A B P).
          Perp.
        auto.
      assert(Col C P B).
        eapply (per_per_col _ _ A); Perp.
      apply H10.
      exists C.
      split; Col.
    unfold Parallelogram_flat in H8.
    spliter.
    apply False_ind.
    assert(Perp B C' C C').
      apply (perp_col _ A).
        auto.
        Perp.
      Col.
    apply perp_left_comm in H13.
    apply perp_not_col in H13.
    apply H13.
    Col.
Qed.
*)
Lemma anga_conga_anga : forall a A B C A' B' C' , anga a -> a A B C -> Conga A B C A' B' C' -> a A' B' C'.
Proof.
    intros.
    unfold anga in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH := H2 A B C).
    assert(HP := H2 A' B' C').
    destruct HH.
    destruct HP.
    apply H4 in H0.
    assert(Conga A0 B0 C0 A' B' C').
      eapply conga_trans.
        apply H0.
      apply H1.
    apply H5.
    auto.
Qed.

Lemma anga_out_anga : forall a A B C A' C', anga a -> a A B C -> out B A A' -> out B C C' -> a A' B C'.
Proof.
    intros.
    assert(HH:= H).
    unfold anga in HH.
    ex_and HH A0.
    ex_and H3 B0.
    ex_and H4 C0.
    assert(HP:= H4 A B C).
    destruct HP.
    assert(Conga A0 B0 C0 A B C).
      apply H6.
      auto.
    assert(HP:= anga_distincts a A B C H H0).
    spliter.
    assert(Conga A B C A' B C').
      apply (out_conga A B C A B C).
        apply conga_refl; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
        auto.
      auto.
    assert(HH:= H4 A' B C').
    destruct HH.
    apply H11.
    apply (conga_trans _ _ _ A B C); auto.
Qed.

Lemma out_out_anga : forall a A B C A' B' C', anga a -> out B A C -> out B' A' C' -> a A B C -> a A' B' C'.
Proof.
    intros.
    assert(Conga A B C A' B' C').
      apply l11_21_b; auto.
    apply (anga_conga_anga a A B C); auto.
Qed.

Lemma is_null_all : forall a A B, A <> B -> is_null_anga a -> a A B A.
Proof.
    intros.
    unfold is_null_anga in H0.
    spliter.
    assert(HH:= H0).
    unfold anga in HH.
    ex_and HH A0.
    ex_and H2 B0.
    ex_and H3 C0.
    apply acute_distinct in H2.
    spliter.
    assert (HH:= H3 A0 B0 C0).
    destruct HH.
    assert (a A0 B0 C0).
      apply H6.
      apply conga_refl; auto.
    assert(HH:= (H1 A0 B0 C0)).
    eapply (out_out_anga a A0 B0 C0); auto.
    apply out_trivial.
    auto.
Qed.

Lemma lcos_const0 : forall l lp a, lcos lp l a -> is_null_anga a ->
 exists A, exists B, exists C, l A B /\ lp B C /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold lcos in HH.
    spliter.
    ex_and H4 A.
    ex_and H5 B.
    ex_and H4 C.
    exists C.
    exists A.
    exists B.
    repeat split.
      apply lg_sym; auto.
      auto.
    apply anga_sym; auto.
Qed.

Lemma lcos_const1 : forall l lp a P, lcos lp l a -> ~ is_null_anga a ->
 exists A, exists B, exists C, ~Col A B P /\ one_side A B C P /\ l A B /\ lp B C /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold lcos in HH.
    spliter.
    assert(HH:= (lcos_lg_not_null lp l a H)).
    spliter.
    lg_instance_not_col l P A B.
    exists A.
    exists B.
    assert(HH:=anga_const_o a A B P H8 H0 H3).
    ex_and HH C'.
    assert(A <> B /\ B <> C').
      assert(HP:= anga_distinct a A B C' H3 H9).
      spliter.
      auto.
    spliter.
    assert(HH:=ex_point_lg_out lp B C' H12 H1 H5).
    ex_and HH C.
    exists C.
    repeat split; auto.
      assert(~ Col A B C').
        unfold one_side in H10.
        ex_and H10 D.
        unfold two_sides in H10.
        spliter.
        intro.
        apply H16.
        Col.
      assert(HP:=out_one_side_1 A B C' C B H11 H15).
      eapply (one_side_transitivity _ _ _ C').
        apply one_side_symmetry.
        apply HP.
          Col.
        apply l6_6.
        auto.
      auto.
    apply (anga_out_anga a A B C'); auto.
      apply out_trivial.
      auto.
    apply l6_6.
    auto.
Qed.

Lemma lcos_const : forall lp l a, lcos lp l a ->
 exists A, exists B, exists C, lp A B /\ l B C /\ a A B C.
Proof.
    intros.
    unfold lcos in H.
    spliter.
    ex_and H2 A.
    ex_and H3 B.
    ex_and H2 C.
    exists B.
    exists A.
    exists C.
    repeat split; auto.
    apply lg_sym; auto.
Qed.

Lemma lcos_lg_distincts : forall lp l a A B C, lcos lp l a -> l A B -> lp B C -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(HH:= lcos_lg_not_null lp l a H).
    spliter.
    unfold lg_null in *.
    split.
      intro.
      subst B.
      apply H4.
      unfold lcos in H.
      split.
        tauto.
      exists A.
      auto.
    intro.
    subst C.
    apply H3.
    unfold lcos in H.
    split.
      tauto.
    exists B.
    auto.
Qed.


Lemma lcos_const_a : forall lp l a B, lcos lp l a -> exists A, exists C, l A B /\ lp B C /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold lcos in HH.
    spliter.
    clear H3.
    assert(HH:= ex_point_lg l B H1).
    ex_and HH A.
    assert(l A B).
      apply lg_sym; auto.
    exists A.
    assert(HH:= lcos_lg_not_null lp l a H).
    spliter.
    assert(A <> B).
      intro.
      subst A.
      apply H6.
      unfold lg_null.
      split.
        auto.
      exists B.
      auto.
    assert(HH:= anga_const a A B H2 H7).
    ex_and HH C'.
    assert(HH:= anga_distincts a A B C' H2 H8).
    spliter.
    assert(B <> C'); auto.
    assert(HH:= ex_point_lg_out lp B C' H11 H0 H5).
    ex_and HH C.
    exists C.
    repeat split; auto.
    apply (anga_out_anga a A B C' A C); auto.
      apply out_trivial.
      auto.
    apply l6_6.
    auto.
Qed.


Lemma lcos_const_ab : forall lp l a B A, lcos lp l a -> l A B -> exists C, lp B C /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold lcos in HH.
    spliter.
    clear H4.
    assert(HH:= lcos_lg_not_null lp l a H).
    spliter.
    assert(A <> B).
      intro.
      subst A.
      apply H5.
      unfold lg_null.
      split.
        auto.
      exists B.
      auto.
    assert(HH:= anga_const a A B H3 H6).
    ex_and HH C'.
    assert(HH:= anga_distincts a A B C' H3 H7).
    spliter.
    assert(B <> C'); auto.
    assert(HH:= ex_point_lg_out lp B C' H10 H1 H4).
    ex_and HH C.
    exists C.
    repeat split; auto.
    apply (anga_out_anga a A B C' A C); auto.
      apply out_trivial.
      auto.
    apply l6_6.
    auto.
Qed.

Lemma lcos_const_cb : forall lp l a B C, lcos lp l a -> lp B C -> exists A, l A B /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold lcos in HH.
    spliter.
    clear H4.
    assert(HH:= lcos_lg_not_null lp l a H).
    spliter.
    assert(C <> B).
      intro.
      subst C.
      apply H4.
      unfold lg_null.
      split.
        auto.
      exists B.
      auto.
    assert(HH:= anga_const a C B H3 H6).
    ex_and HH A'.
    assert(HH:= anga_distincts a C B A' H3 H7).
    spliter.
    assert(B <> A'); auto.
    assert(HH:= ex_point_lg_out l B A' H10 H2 H5).
    ex_and HH A.
    exists A.
    split.
      apply lg_sym; auto.
    apply(anga_out_anga a A' B C); auto.
      apply anga_sym; auto.
      apply l6_6.
      auto.
    apply out_trivial.
    auto.
Qed.

Lemma lcos_lg_anga : forall l lp a, lcos lp l a -> lcos lp l a /\ lg l /\ lg lp /\ anga a.
Proof.
    intros.
    split.
      auto.
    unfold lcos in H.
    tauto.
Qed.

Lemma lg_eql_lg : forall l1 l2, lg l1 -> eqL l1 l2 -> lg l2.
Proof.
    intros.
    unfold eqL in *.
    unfold lg in *.
    decompose [ex] H.
    exists x. exists x0.
    intros.
    rewrite H2.
    apply H0.
Qed.

Lemma lcos_eql_lcos : forall lp1 l1 lp2 l2 a, eqL lp1 lp2 -> eqL l1 l2 -> lcos lp1 l1 a -> lcos lp2 l2 a.
Proof.
    intros.
    unfold lcos in *.
    spliter.
    ex_and H4 A.
    ex_and H5 B.
    ex_and H4 C.

    assert(HH:=lg_eql_lg l1 l2 H2 H0).
    assert(HP:=lg_eql_lg lp1 lp2 H1 H).
    repeat split; auto.
    exists A.
    exists B.
    exists C.
    unfold eqL in *.
    spliter.
    repeat split; auto.
      apply H.
      auto.
    apply H0; auto.
Qed.

Require Export Morphisms.

Global Instance lcos_morphism :
 Proper (eqL ==> eqL ==> eq ==> iff) lcos.
Proof.
unfold Proper.
split.
 - rewrite H1.
   intro.
   eauto using lcos_eql_lcos.
 - intro.
   rewrite H1.
   eapply lcos_eql_lcos with y y0;
   try symmetry;assumption.
Qed.

Lemma ang_not_lg_null : forall a la lc A B C, lg la -> lg lc -> ang a ->
 la A B -> lc C B -> a A B C -> ~ lg_null la /\ ~ lg_null lc.
Proof.
    intros.
    assert(HH:=ang_distincts a A B C H1 H4).
    spliter.
    split.
      intro.
      unfold lg_null in H7.
      spliter.
      ex_and H8 P.
      assert(HH:= lg_cong la A B P P H H2 H9).
      apply cong_identity in HH.
      contradiction.
    intro.
    unfold lg_null in H7.
    spliter.
    ex_and H8 P.
    assert(HH:= lg_cong lc C B P P H0 H3 H9).
    apply cong_identity in HH.
    contradiction.
Qed.

Lemma anga_not_lg_null : forall a la lc A B C, lg la -> lg lc ->
 anga a -> la A B -> lc C B -> a A B C -> ~ lg_null la /\ ~ lg_null lc.
Proof.
    intros.
    apply anga_is_ang in H1.
    apply(ang_not_lg_null a la lc A B C); auto.
Qed.


Lemma lcos_not_lg_null : forall lp l a, lcos lp l a -> ~ lg_null lp.
Proof.
    intros.
    intro.
    unfold lg_null in H0.
    spliter.
    unfold lcos in H.
    spliter.
    ex_and H4 B.
    ex_and H5 A.
    ex_and H4 C.
    ex_and H1 P.
    unfold lg in H0.
    ex_and H0 X.
    ex_and H1 Y.
    assert(HH:= (H0 B A)).
    destruct HH.
    assert(HH:= (H0 P P)).
    destruct HH.
    apply H11 in H8.
    apply H9 in H5.
    assert(Cong B A P P).
      apply (cong_transitivity _ _ X Y); Cong.
    assert(A = B).
      eapply (cong_identity _ _ P).
      Cong.
    assert(HH:=anga_distincts a A B C H3 H7).
    spliter.
    contradiction.
Qed.

Lemma lcos_const_o : forall lp l a A B P, ~ Col A B P -> ~ is_null_anga a -> lg l -> lg lp ->
  anga a -> l A B -> lcos lp l a ->
  exists C, one_side A B C P /\ a A B C /\ lp B C.
Proof.
    intros.
    assert(HH:= anga_const_o a A B P H H0 H3).
    ex_and HH C'.
    assert(A <> B /\ C' <> B).
      apply (anga_distincts a); auto.
    spliter.
    assert(HH:= lcos_not_lg_null lp l a H5).
    assert (B <> C').
      intro.
      apply H9.
      auto.
    assert(HP:=lg_exists C' B).
    ex_and HP lc'.
    assert(HQ:=anga_not_lg_null a l lc' A B C' H1 H11 H3 H4 H12 H6).
    spliter.
    assert(HR:= ex_point_lg_out lp B C' H10 H2 HH).
    ex_and HR C.
    exists C.
    split.
      apply invert_one_side.
      apply one_side_symmetry.
      apply (out_out_one_side _ _ _ C').
        apply invert_one_side.
        apply one_side_symmetry.
        auto.
      apply l6_6.
      auto.
    split.
      eapply (anga_out_anga a A B C'); auto.
        apply out_trivial.
        auto.
      apply l6_6.
      auto.
    auto.
Qed.

Lemma anga_col_null : forall a A B C, anga a -> a A B C -> Col A B C -> out B A C /\ is_null_anga a.
Proof.
    intros.
    assert(HH:= anga_distincts a A B C H H0).
    spliter.
    assert(out B A C).
      induction H1.
        assert(HP:=anga_acute a A B C H H0).
        assert(HH:=acute_not_bet A B C HP).
        contradiction.
      induction H1.
        unfold out.
        repeat split; auto.
      unfold out.
      repeat split; auto.
      left.
      Between.
    split.
      auto.
    apply (out_null_anga a A B C); auto.
Qed.


Lemma flat_not_acute : forall A B C, Bet A B C -> ~ acute A B C.
Proof.
    intros.
    intro.
    unfold acute in H0.
    ex_and H0 A'.
    ex_and H1 B'.
    ex_and H0 C'.
    unfold lta in H1.
    spliter.
    unfold lea in H1.
    ex_and H1 P'.
    unfold InAngle in H1.
    spliter.
    ex_and H6 X.
    apply conga_distinct in H3.
    spliter.
    assert(A <> C).
      intro.
      subst C.
      apply between_identity in H.
      contradiction.
    induction H7.
      subst X.
      apply H2.
      apply conga_line; auto.
    assert(Conga A B C A' B' X).
      apply (out_conga A B C A' B' P').
        auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      apply l6_6.
      auto.
    apply H2.
    assert(Bet A' B' X).
      apply (bet_conga_bet A B C); auto.
    apply conga_line; auto.
    apply (between_exchange4 _ _ X); auto.
Qed.

Lemma acute_comp_not_acute : forall A B C D, Bet A B C -> acute A B D -> ~ acute C B D.
Proof.
    intros.
    intro.
    induction(Col_dec A C D).
      induction H2.
        assert(Bet A B D).
          eBetween.
        assert(HH:= flat_not_acute A B D H3).
        contradiction.
      induction H2.
        assert(Bet A B D \/ Bet A D B).
          apply (l5_3 A B D C).
            auto.
          Between.
        induction H3.
          assert(HH:= flat_not_acute A B D H3).
          contradiction.
        assert(Bet C B D).
          eBetween.
        assert(HH:= flat_not_acute C B D H4).
        contradiction.
      assert(Bet C B D).
        eBetween.
      assert(HH:= flat_not_acute C B D H3).
      contradiction.
    unfold acute in *.
    ex_and H0 A0.
    ex_and H3 B0.
    ex_and H0 C0.
    ex_and H1 A1.
    ex_and H4 B1.
    ex_and H1 C1.
    apply lta_diff in H3.
    apply lta_diff in H4.
    spliter.
    assert(HH:=l11_16 A0 B0 C0 A1 B1 C1 H0 H11 H12 H1 H7 H8).
    assert(lta C B D A0 B0 C0).
      eapply(conga_preserves_lta C B D A1 B1 C1).
        apply conga_refl; auto.
        apply conga_sym.
        auto.
      auto.
    clear H4.
    assert(A <> C).
      intro.
      subst C.
      apply between_identity in H.
      contradiction.
    assert(Col A C B).
      apply bet_col in H.
      Col.
    assert(HP:= l10_15 A C B D H14 H2).
    ex_and HP P.
    assert(HP:= perp_col A C P B B H9 H15 H14).
    apply perp_left_comm in HP.
    apply perp_perp_in in HP.
    assert(Per A B P).
      apply perp_in_per.
      apply perp_in_comm.
      auto.
    assert(HR:= perp_not_eq_2 A C P B H15).
    assert(HQ:=l11_16 A B P A0 B0 C0 H17 H9 HR H0 H11 H12).
    assert(lta A B D A B P).
      apply (conga_preserves_lta A B D A0 B0 C0); auto.
        apply conga_refl; auto.
      apply conga_sym.
      auto.
    assert(lta C B D A B P).
      apply (conga_preserves_lta C B D A0 B0 C0); auto.
        apply conga_refl; auto.
      apply conga_sym.
      auto.
    clear HQ H13 H8 HH H3 H11 H12 H0 H1 H7.
    unfold lta in *.
    spliter.
    assert((lea A B D A B P <-> lea C B P C B D)).
      apply (l11_36 A B D A B P C C); auto.
    destruct H8.
    assert(lea C B P C B D).
      apply H8.
      auto.
    assert(Conga A B P C B P).
      apply l11_16; auto.
      apply perp_in_per.
      assert(Perp C B P B).
        apply(perp_col _ A).
          auto.
          apply perp_left_comm.
          auto.
        apply bet_col in H.
        Col.
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_left_comm.
      auto.
    assert(lea A B P C B D).
      apply (l11_30 C B P C B D); auto.
        apply conga_sym.
        auto.
      apply conga_refl; auto.
    assert(HH:=lea_asym C B D A B P H0 H18).
    contradiction.
Qed.

Lemma lcos_per : forall A B C lp l a, anga a -> lg l -> lg lp ->
  lcos lp l a -> l A C -> lp A B -> a B A C -> Per A B C.
Proof.
    intros.
    induction(eq_dec_points B C).
      subst C.
      apply l8_5.
    unfold lcos in H2.
    spliter.
    ex_and H9 A0.
    ex_and H10 B0.
    ex_and H9 C0.
    assert(Conga B0 A0 C0 B A C).
      apply (anga_conga a); auto.
    assert(Cong A0 C0 A C).
      apply (lg_cong l); auto.
    assert(Cong A0 B0 A B).
      apply (lg_cong lp); auto.
    assert(HH:=l11_49 B0 A0 C0 B A C H13 H15 H14).
    spliter.
    assert(B0 <> C0).
      intro.
      subst C0.
      apply H6.
      apply (cong_identity _ _ B0).
      Cong.
    apply H17 in H18.
    spliter.
    eapply (l11_17 A0 B0 C0).
      apply l8_2.
      auto.
    auto.
Qed.

Lemma is_null_anga_dec : forall a, anga a -> is_null_anga a \/ ~is_null_anga a.
Proof.
    intros a H.
    assert (H' := H).
    unfold anga in H.
    destruct H as [A [B [C [Hacute HConga]]]].
    elim (out_dec B A C); intro Hout.
      left.
      unfold is_null_anga.
      split; auto.
      intros.
      apply (out_conga_out A B C); auto.
      apply HConga.
      assumption.
    right.
    unfold is_null_anga.
    intro H.
    destruct H as [Hclear H]; clear Hclear.
    apply Hout.
    apply H.
    apply HConga.
    apply acute_distinct in Hacute.
    spliter.
    apply conga_refl; auto.
Qed.

Lemma lcos_lg : forall a lp l A B C, lcos lp l a -> Perp A B B C -> a B A C -> l A C -> lp A B.
Proof.
    intros.
    assert(HH:=H).
    unfold lcos in HH.
    spliter.
    ex_and H6 A'.
    ex_and H7 B'.
    ex_and H6 C'.
    assert(Cong A C A' C').
      apply (lg_cong l); auto.
    assert(Conga B A C B' A' C').
      apply (anga_conga a); auto.
    induction(is_null_anga_dec a).
      assert(HP := null_lcos_eql lp l a H H12).
      unfold is_null_anga in H12.
      spliter.
      assert(HH:= (H13 B A C H1)).
      apply perp_comm in H0.
      apply perp_not_col in H0.
      apply False_ind.
      apply H0.
      apply out_col in HH.
      Col.
      apply conga_distinct in H11.
      spliter.
      assert(Conga A B C A' B' C').
        apply l11_16; auto.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_comm.
          auto.
          apply perp_not_eq_2 in H0.
          auto.
          apply l8_2.
          auto.
        intro.
        subst C'.
        apply H12.
        unfold is_null_anga.
        split; auto.
        intros.
        assert(Conga A0 B0 C0 B' A' B').
          apply (anga_conga a); auto.
        apply (out_conga_out B' A' B') .
          apply out_trivial; auto.
        apply conga_sym.
        auto.
      assert(Cong C B C' B' /\ Cong A B A' B' /\ Conga B C A B' C' A').
        apply(l11_50_2 C A B C' A' B').
          apply perp_comm in H0.
          apply perp_not_col in H0.
          intro.
          apply H0.
          Col.
          auto.
          apply conga_comm.
          auto.
        Cong.
      spliter.
      apply (lg_cong_lg lp A' B');auto.
      Cong.
    assumption.
Qed.

Lemma l13_7 : forall a b l la lb lab lba, lcos la l a -> lcos lb l b ->
  lcos lab la b -> lcos lba lb a -> eqL lab lba.
Proof.
    intros.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    apply lcos_lg_anga in H1.
    apply lcos_lg_anga in H2.
    spliter.
    clean_duplicated_hyps.
    induction (is_null_anga_dec a).
      assert(HH:=null_lcos_eql lba lb  a H2 H3).
      assert(HP:=null_lcos_eql la l  a H H3).
      assert(lcos lab l b) by (rewrite HP;assumption).
      assert(HQ:= l13_6 b lb lab l H0 H5).
      rewrite <- HQ;assumption. 
      induction (is_null_anga_dec b).
        assert(HH:=null_lcos_eql lab la  b H1 H5).
        assert(HP:=null_lcos_eql lb l  b H0 H5).
        assert(lcos lba l a) by (rewrite HP;auto).
        assert(HQ:= l13_6 a la lba l H H6).
        rewrite HH in HQ;assumption.
        assert(HH:=lcos_const la l a H).
        ex_and HH C.
        ex_and H6 A.
        ex_and H8 B.
        assert(HH:= anga_distincts a C A B H14 H9).
        spliter.
        assert(~Col A B C).
          intro.
          apply H3.
          assert(Col C A B).
            Col.
          assert(HH:= anga_col_null a C A B H14 H9 H18).
          spliter.
          auto.
        assert(HH:=l10_2_existence B A C).
        ex_and HH P.
        assert( ~ Col B A P).
          eapply (osym_not_col _ _ C).
            apply l10_4.
            auto.
          intro.
          apply H17.
          Col.
        assert(l B A).
          apply lg_sym; auto.
        assert(HH:= lcos_const_o lb l b B A P H19 H5 H12 H10 H11 H20 H0).
        ex_and HH D.
        assert(two_sides B A P C).
          apply l10_14.
            intro.
            subst P.
            assert(Col C B A).
              apply(l10_8 B A C); auto.
            apply H19.
            Col.
            auto.
          auto.
        assert(two_sides B A D C).
          eapply (l9_8_2 _ _ P).
            auto.
          apply one_side_symmetry.
          auto.
        assert(Per A C B).
          apply (lcos_per _ _ _ la l a); auto.
          apply lg_sym; auto.
        assert(Per A D B).
          apply (lcos_per _ _ _ lb l b); auto.
          apply anga_sym; auto.
        assert(~ Col C D A).
          intro.
          assert(Per B C D).
            apply(per_col B C A D); auto.
              apply l8_2.
              auto.
            Col.
          assert(Per B D C).
            apply(per_col B D A C); auto.
              unfold one_side in H21.
              ex_and H21 T.
              unfold two_sides in H21.
              spliter.
              intro.
              subst D.
              apply H31.
              Col.
              apply l8_2.
              auto.
            Col.
          assert(C = D).
            apply (l8_7 B); auto.
          subst D.
          unfold two_sides in H25.
          spliter.
          ex_and H33 T.
          assert(C=T).
            apply between_identity.
            auto.
          subst T.
          contradiction.
        assert(HH:= l8_18_existence C D A H28).
        ex_and HH E.
        assert(Conga B A C D A E /\ Conga B A D C A E /\ Bet C E D).
          apply(l13_2 A B C D E).
            apply invert_two_sides.
            apply l9_2.
            auto.
            apply l8_2.
            auto.
            apply l8_2.
            auto.
            auto.
          apply perp_sym.
          auto.
        spliter.
        assert(a D A E).
          eapply (anga_conga_anga a B A C); auto.
          apply anga_sym; auto.
        assert(b C A E).
          eapply (anga_conga_anga b B A D); auto.
        assert(Perp C E A E).
          eapply (perp_col _ D) .
            intro.
            subst E.
            apply H5.
            unfold is_null_anga.
            split; auto.
            intros.
            assert(Conga A0 B0 C0 C A C).
              apply (anga_conga b); auto.
            apply (out_conga_out C A C A0 B0 C0 ).
              apply out_trivial; auto.
            apply conga_sym.
            auto.
            auto.
          auto.
        assert(lab A E).
          apply (lcos_lg b lab la A E C H1).
            apply perp_sym in H36.
            apply perp_right_comm in H36.
            auto.
            apply anga_sym; auto.
          apply lg_sym; auto.
        assert(Perp D E A E).
          eapply (perp_col _ C) .
            intro.
            subst E.
            apply H3.
            unfold is_null_anga.
            split; auto.
            intros.
            assert(Conga A0 B0 C0 D A D).
              apply (anga_conga a); auto.
            apply (out_conga_out D A D A0 B0 C0 ).
              apply out_trivial; auto.
              apply perp_not_eq_2 in H36.
              auto.
            apply conga_sym.
            auto.
            Perp.
          Col.
        assert(lba A E).
          apply (lcos_lg a lba lb A E D).
            auto.
            Perp.
            auto.
            apply anga_sym; auto.
          auto.
        apply ex_eql.
        exists A.
        exists E.
        split.
          unfold is_len.
          split; auto.
        unfold is_len.
        split; auto.
      assumption.
    assumption.
Qed.

Lemma out_acute : forall A B C, out B A C -> acute A B C.
Proof.
    intros.
    assert( A <> B /\ C <> B).
      unfold out in H.
      tauto.
    spliter.
    assert(HH:= not_col_exists A B H0).
    ex_and HH Q.
    assert(exists P : Tpoint, Perp A B P B /\ one_side A B Q P).
      apply(l10_15 A B B Q).
        Col.
      auto.
    ex_and H3 P.
    assert(Per P B A).
      apply perp_in_per.
      apply perp_left_comm in H3.
      apply perp_in_comm.
      apply perp_perp_in.
      Perp.
    unfold acute.
    exists A.
    exists B.
    exists P.
    split.
      apply l8_2.
      auto.
    unfold lta.
    split.
      unfold lea.
      exists C.
      split.
        apply col_in_angle; auto.
        apply perp_not_eq_2 in H3.
        auto.
      apply conga_refl; auto.
    intro.
    apply out_conga_out in H6.
      apply perp_left_comm in H3.
      apply perp_not_col in H3.
      apply out_col in H6.
      contradiction.
    assumption.
Qed.



Lemma perp_acute : forall A B C P,  Col A C P -> Perp_in P B P A C -> acute A B P.
Proof.
    intros.
    assert(HH0:=H0).
    assert(HH:= l11_43 P A B).
    induction(Col_dec P A B).
      assert(Perp B A A C).
        eapply (perp_col _ P).
          intro.
          subst A.
          assert(Perp_in B B P C B).
            apply perp_perp_in.
            apply perp_in_perp in H0.
            induction H0.
              apply perp_not_eq_1 in H0.
              tauto.
            Perp.
          assert(P=B).
            eapply(l8_14_3 B P B C); Perp.
          subst P.
          apply perp_in_perp in H0.
          induction H0.
            apply perp_not_eq_1 in H0.
            tauto.
          apply perp_not_eq_1 in H0.
          tauto.
          apply perp_in_perp in H0.
          induction H0.
            apply perp_not_eq_1 in H0.
            tauto.
          auto.
        Col.
      apply perp_comm in H2.
      apply perp_perp_in in H2.
      apply perp_in_comm in H2.
      apply perp_in_sym in H2.
      eapply (perp_in_col_perp_in _ _ _ _ P) in H2.
        assert( A = P).
          eapply(l8_14_3 A C B P); Perp.
        subst P.
        apply out_acute.
        apply perp_in_perp in H2.
        induction H2.
          apply out_trivial.
          apply perp_not_eq_2 in H2.
          auto.
        apply perp_not_eq_1 in H2.
        tauto.
        apply perp_in_perp in H0.
        induction H0; apply perp_not_eq_1 in H0; tauto.
      Col.
    apply acute_sym.
    apply l11_43.
      auto.
    left.
    assert(A <> P).
      intro.
      subst P.
      apply H1.
      Col.
    eapply (perp_in_col_perp_in _ _ _ _ P) in H0; auto.
    apply perp_in_per.
    Perp.
Qed.



Lemma null_lcos : forall l a,lg l -> ~lg_null l -> is_null_anga a -> lcos l l a.
Proof.
    intros.
    unfold is_null_anga in H1.
    spliter.
    assert(HH:=ex_points_anga a H1).
    ex_and HH A.
    ex_and H3 B.
    ex_and H4 C.
    assert(HH:=H2 A B C H3).
    unfold lcos.
    repeat split; auto.
    assert(B <> A).
      unfold out in HH.
      spliter.
      auto.
    lg_instance l A' B'.
    assert(HP:=ex_point_lg_out l B A H4 H H0).
    ex_and HP P.
    exists B.
    exists P.
    exists P.
    repeat split; auto.
      apply l8_2.
      apply l8_5.
    apply (anga_out_anga _ A _ C); auto.
      apply l6_6.
      auto.
    apply (out2_out_2 _ _ _ A).
      apply l6_6.
      auto.
    auto.
Qed.

Lemma eqA_preserves_ang: forall a b, ang a -> eqA a b -> ang b.
Proof.
intros.
unfold ang in *.
decompose [ex and] H.
exists x. exists x0. exists x1.
split.
assumption.
split.
assumption.
intros.
rewrite H4.
unfold eqA in H0.
apply H0.
Qed.

Lemma eqA_preserves_anga : forall a b, anga a -> ang b -> eqA a b -> anga b.
Proof.
    intros.
    assert (ang a).
        apply eqA_preserves_ang with b;auto.
        symmetry;auto.         
    unfold eqA in H1.
    anga_instance a A B C.

    assert(HH:= H1 A B C).
    destruct HH.
    unfold anga.
    exists A.
    exists B.
    exists C.
    split.
      unfold anga in H.
      ex_and H A'.
      ex_and H6 B'.
      ex_and H C'.
      assert(a A' B' C').
        assert(HP:= H6 A B C).
        destruct HP.
        assert(Conga A B C A' B' C') by (apply conga_sym;auto).
        assert(HP:=is_ang_conga_is_ang A B C A' B' C' a).
        assert(is_ang A' B' C' a).
          apply HP.
            split; auto.
          auto.
        unfold is_ang in H10.
        spliter.
        auto.
      apply (acute_lea_acute _ _ _ A' B' C').
        auto.
      unfold lea.
      exists C'.
      split.
        assert (HH:= is_ang_distinct A' B' C' a).
        assert( A' <> B' /\ C' <> B').
          apply HH.
          split; auto.
        spliter.
        apply in_angle_trivial_2; auto.
      eapply (is_ang_conga _ _ _ _ _ _ a).
        split; auto.
      split; auto.
    intros.
    split.
      intro.
      assert(HH:= H1 x y z).
      destruct HH.
      assert(is_ang x y z a).
        eapply (is_ang_conga_is_ang A B C).
          split; auto.
        auto.
      unfold is_ang in H9.
      spliter.
      auto.
    intro.
    assert(HH:= H1 x y z).
    destruct HH.
    assert(a x y z).
      auto.
    eapply (is_ang_conga _ _ _ _ _ _ a).
      split; auto.
    split; auto.
Qed.


Lemma lcos_existence : forall l a, lg l -> ~lg_null l -> anga a -> exists lp, lcos lp l a.
Proof.
intros.
assert (HL:= H).
unfold lg in HL.
ex_and HL A.
ex_and H2 C.

assert(C <> A).
intro.
subst C.
apply H0.
unfold lg_null.
split; auto.
exists A.
assert(HH:= H3 A A).
destruct HH.
apply H2.
Cong.

anga_instance1 a C A P; auto.

induction(Col_dec C A P).
assert(HH:= anga_col_out a C A P H1 H4 H5).
exists l.
assert(HP:= null_lcos l a H H0).
apply HP.
unfold is_null_anga.
split; auto.
intros.
assert(HA:= anga_conga a C A P A0 B C0).
apply (out_conga_out C A P); auto.

assert(exists X : Tpoint, Col A P X /\ Perp A P C X).

apply(l8_18_existence A P C).
intro.
apply H5.
Col.
ex_and H6 B.

assert(HH:= lg_exists A B).
ex_and HH lp.
exists lp.
unfold lcos.
repeat split; auto.
exists A.
exists B.
exists C.

assert(HH:=anga_acute a C A P H1 H4).
assert(out A P B).
apply(perp_acute_out P A C B); Perp; Col.
apply acute_sym.
auto.

assert(A <> B).
apply out_distinct in H10.
spliter.
auto.

split.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
assert(HP:=perp_col A P C B B H11 H7 H6).
Perp.
split; auto.
split.
assert(HL:= H3 A C).
destruct HL.
apply H12.
Cong.

apply(anga_out_anga a P A C B C); auto.
apply anga_sym; auto.
apply out_trivial; auto.
Qed.


Lemma ex_eqL : forall l1 l2, lg l1 -> lg l2 -> (exists A, exists B, l1 A B /\ l2 A B) -> eqL l1 l2.
Proof.
intros.
ex_and H1 A.
ex_and H2 B.
unfold eqL.
assert(HH1:= H).
assert(HH2:= H0).

unfold lg in HH1.
unfold lg in HH2.
ex_and HH1 A1.
ex_and H3 B1.
ex_and HH2 A2.
ex_and H3 B2.

repeat split; auto.
intro.
assert(HH:= H4 A0 B0).
assert(HP:= H5 A0 B0).
destruct HP.
apply H6.
assert(HP:= H4 A B).
assert(HQ:= H5 A B).
destruct HP.
destruct HQ.
apply H9 in H1.
apply H11 in H2.
destruct HH.
apply H13 in H3.
eCong.

intro.
assert(HH:= H4 A0 B0).
assert(HP:= H5 A0 B0).
destruct HH.
apply H6.
assert(HH:= H4 A B).
assert(HQ:= H5 A B).
destruct HH.
destruct HQ.
apply H9 in H1.
apply H11 in H2.
destruct HP.
apply H13 in H3.
eCong.
Qed.

Lemma lcos_unicity : forall l a l1 l2, lcos l1 l a-> lcos l2 l a -> eqL l1 l2.
Proof.
intros.
unfold lcos in *.
spliter.
ex_and H6 A1.
ex_and H7 B1.
ex_and H6 C1.
ex_and H3 A2.
ex_and H10 B2.
ex_and H3 C2.

assert(Cong A1 C1 A2 C2).
apply (lg_cong l); auto.

assert(Conga B1 A1 C1 B2 A2 C2).
apply (anga_conga a); auto.

induction(eq_dec_points C1 B1).
subst C1.

assert(eqL l l1).
apply ex_eqL; auto.
exists A1.
exists B1.
split; auto.

assert(out A2 B2 C2).
apply (out_conga_out B1 A1 B1).
apply out_trivial.
intro.
subst B1.
apply conga_distinct in H14.
tauto.
auto.

assert(C2 = B2 \/ A2 = B2).
apply(l8_9 C2 B2 A2).
auto.
apply out_col in H16.
Col.
induction H17.
subst C2.

assert(eqL l l2).
apply ex_eqL; auto.
exists A2.
exists B2.
split; auto.
transitivity l; auto.
symmetry; auto.

subst B2.
apply conga_distinct in H14.
tauto.

apply conga_distinct in H14.
spliter.
assert(Conga C1 B1 A1 C2 B2 A2).
apply l11_16; auto.
intro.
subst C2.

assert(out A1 B1 C1).
apply (out_conga_out B2 A2 B2).
apply out_trivial; auto.
apply conga_sym.
auto.
assert(C1 = B1 \/ A1 = B1).
apply(l8_9 C1 B1 A1 ); auto.
apply out_col in H20.
Col.
induction H21.
subst C1.
tauto.
subst B1.
tauto.

assert( Cong C1 B1 C2 B2 /\ Cong A1 B1 A2 B2 /\ Conga B1 C1 A1 B2 C2 A2).
apply(l11_50_2 C1 A1 B1 C2 A2 B2).
intro.
assert(C1 = B1 \/ A1 = B1).
apply(l8_9 C1 B1 A1 ); auto.
Col.
induction H22.
contradiction.
subst B1.
tauto.
apply conga_comm.
auto.
apply conga_comm.
auto.
Cong.
spliter.

apply ex_eqL; auto.
exists A1.
exists B1.
split; auto.
apply (lg_cong_lg l2 A2 B2); auto.
Cong.
Qed.

End Cosinus2.