Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.

Ltac clean_reap_hyps :=
  repeat
  match goal with
   | H:(is_midpoint ?A ?B ?C), H2 : is_midpoint ?A ?C ?B |- _ => clear H2
   | H:(is_midpoint ?A ?B ?C), H2 : is_midpoint ?A ?B ?C |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : ~Col ?A ?B ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?A ?C ?B |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?A ?B ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?A ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?C ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?B ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?A ?B |- _ => clear H2
   | H:(Bet ?A ?B ?C), H2 : Bet ?C ?B ?A |- _ => clear H2
   | H:(Bet ?A ?B ?C), H2 : Bet ?A ?B ?C |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?A ?B ?D ?C |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?A ?B ?C ?D |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?C ?D |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?D ?C |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?A ?B ?D ?C |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?A ?B ?C ?D |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?C ?D |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?D ?C |- _ => clear H2
   | H:(?A<>?B), H2 : (?B<>?A) |- _ => clear H2
   | H:(?A<>?B), H2 : (?A<>?B) |- _ => clear H2
   | H:(Per ?A ?D ?C), H2 : (Per ?C ?D ?A) |- _ => clear H2
   | H:(Per ?A ?D ?C), H2 : (Per ?A ?D ?C) |- _ => clear H2
   | H:(Perp_in ?X ?A ?B ?C ?D), H2 : Perp_in ?X ?A ?B ?D ?C |- _ => clear H2
   | H:(Perp_in ?X ?A ?B ?C ?D), H2 : Perp_in ?X ?A ?B ?C ?D |- _ => clear H2
   | H:(Perp_in ?X ?A ?B ?C ?D), H2 : Perp_in ?X ?C ?D ?A ?B |- _ => clear H2
   | H:(Perp_in ?X ?A ?B ?C ?D), H2 : Perp_in ?X ?C ?D ?B ?A |- _ => clear H2
   | H:(Perp_in ?X ?A ?B ?C ?D), H2 : Perp_in ?X ?D ?C ?B ?A |- _ => clear H2
   | H:(Perp_in ?X ?A ?B ?C ?D), H2 : Perp_in ?X ?D ?C ?A ?B |- _ => clear H2
   | H:(Perp_in ?X ?A ?B ?C ?D), H2 : Perp_in ?X ?B ?A ?C ?D |- _ => clear H2
   | H:(Perp_in ?X ?A ?B ?C ?D), H2 : Perp_in ?X ?B ?A ?D ?C |- _ => clear H2
end.

Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := not_col_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_4 A B C D H2 H);clean_reap_hyps

      | H:is_midpoint ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:is_midpoint ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B (swap_diff B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:is_midpoint ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:is_midpoint ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B (swap_diff A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:is_midpoint ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:is_midpoint ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B (swap_diff B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Perp_in ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_in_distinct X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps
 end.

Ltac clean_trivial_hyps :=
  repeat
  match goal with
   | H:(Cong ?X1 ?X1 ?X2 ?X2) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Col ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X2 ?X1) |- _ => clear H
   | H:(Per ?X1 ?X2 ?X2)     |- _ => clear H
   | H:(Per ?X1 ?X1 ?X2)     |- _ => clear H
   | H:(is_midpoint ?X1 ?X1 ?X1) |- _ => clear H
end.

Ltac finish := match goal with
 | |- Col ?A ?B ?C => Col
 | |- ~ Col ?A ?B ?C => Col
 | |- Perp ?A ?B ?C ?D => Perp
 | |- Cong ?A ?B ?C ?D => Cong
 | |- is_midpoint ?A ?B ?C => Midpoint
 | |- ?A<>?B => apply swap_diff;assumption
 | |- _ => try assumption
end.

Section T9.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Definition two_sides A B P Q :=
  A<>B /\ ~ Col P A B /\ ~ Col Q A B /\ exists T, Col T A B /\ Bet P T Q.

Lemma l9_2 : forall A B P Q, two_sides A B P Q -> two_sides A B Q P.
Proof.
    unfold two_sides.
    intros.
    spliter.
    repeat split; try Col.
    destruct H2 as [T [HCol1 HCol2]].
    exists T; Col; Between.
Qed.

Lemma invert_two_sides : forall A B P Q,
 two_sides A B P Q -> two_sides B A P Q.
Proof with finish.
    unfold two_sides.
    intros.
    spliter.
    repeat split...
    ex_and H2 T.
    exists T;split...
Qed.

(* TODO should we need this lemma about col ? at least move it in the right chapter 
Lemma colx : forall A B M N X, A <> B -> N <> M -> X <> M -> Col A B M -> Col A B N -> Col M N X -> Col A B X.
Proof.
    intros.
    ColR.
Qed. *)

Lemma l9_3 : forall P Q A C M R B,
 two_sides P Q A C -> Col M P Q ->
 is_midpoint M A C -> Col R P Q ->
 out R A B -> two_sides P Q B C.
Proof with finish.
    intros.
    unfold two_sides in *.
    spliter.
    ex_and H6 T.
    show_distinct A C.
      intuition.
    assert (T = M).
      assert_bet.
      assert_cols.
      eapply l6_21 with P Q A C...
    subst T.
    repeat split...
      induction(eq_dec_points C M).
        subst M.
        intuition.
      intro.
      clear H0.
      assert (B <> R).
        intro.
        subst B.
        unfold out in H3.
        spliter.
        absurde.
      assert (Col P R B) by ColR.
      assert (Col P R A).
        induction (eq_dec_points P B).
          subst B.
          assert_cols...
        apply col_permutation_2.
        eapply col_transitivity_2.
          apply H0.
          assert_cols...
        Col.
      induction (eq_dec_points P R).
        subst R.
        apply H4.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ B).
          assert_diffs;intuition.
          apply col_permutation_4.
          assumption.
        assert_cols...
      assert (Col P B A ).
        eapply col_transitivity_1.
          apply H13.
          assumption.
        assumption.
      induction (eq_dec_points P B).
        subst B.
        apply H4.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ R).
          apply H0.
          apply col_permutation_4.
          assumption.
        unfold out in H3.
        spliter.
        unfold Col.
        induction H16.
          right; left.
          assumption.
        right;right.
        Between.
      apply H4.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H15.
        Col.
      assumption.
    induction H3.
    spliter.
    induction H10.
      double B M B'.
      double R M R'.
      assert (Bet B' C R').
        eapply l7_15.
          apply H11.
          apply H1.
          apply H12.
        Between.
      assert (exists X, Bet M X R' /\ Bet C X B).
        eapply inner_pasch.
          (* assert_bet.
          Between.
          *)
          apply midpoint_bet.
          apply H11.
        apply between_symmetry.
        assumption.
      ex_and H14 X.
      exists X.
      split.
        assert (Col P M R ).
          eapply col_transitivity_1.
            apply H.
            Col.
          Col.
        assert (Col Q M R).
          eapply (col_transitivity_1 _ P).
            auto.
            Col.
          Col.
        induction (eq_dec_points M X).
          subst X.
          assumption.
        show_distinct M R'.
          intuition.
        assert (M <> R).
          intro.
          subst R.
          eapply (symmetric_point_unicity) in H12.
            apply H19.
            apply H12.
          apply l7_3_2.
        apply col_permutation_2.
        ColR.
      Between.
    assert (exists X, Bet B X C /\ Bet M X R).
      eapply inner_pasch.
        apply H10.
      Between.
    ex_and H11 X.
    exists X.
    induction (eq_dec_points M R).
      subst R.
      apply between_identity in H12.
      subst X.
      split; assumption.
    induction (eq_dec_points R X).
      subst X.
      split; assumption.
    split.
      induction (eq_dec_points X M).
        subst X.
        assumption.
      assert (Col P M R ).
        eapply col_transitivity_1.
          apply H.
          Col.
        Col.
      assert (Col X P Q).
        apply col_permutation_2.
        ColR.
      assumption.
    assumption.
Qed.

Definition is_symmetric (A A' C : Tpoint) := is_midpoint C A A'.

Lemma sym_sym : forall A C A', is_symmetric A A' C  -> is_symmetric A' A C.
Proof.
    unfold is_symmetric.
    intros.
    apply l7_2.
    assumption.
Qed.


Lemma distinct : forall P Q R : Tpoint, P <> Q -> (R <> P \/ R <> Q).
Proof.
    intros.
    assert (~ (R = P /\ R = Q) -> (R <> P \/ R <> Q)).
      intro.
      induction (eq_dec_points P R).
        subst R.
        right.
        intro.
        apply H0.
        split.
          reflexivity.
        assumption.
      left.
      intro.
      apply H1.
      subst R.
      reflexivity.
    apply H0.
    intro.
    spliter.
    subst P.
    subst Q.
    apply H.
    reflexivity.
Qed.

Lemma diff_col_ex : forall A B, exists C, A <> C /\ B <> C /\ Col A B C.
Proof.
    intros.
    assert (exists C, Bet A B C /\ B <> C).
      apply point_construction_different.
    ex_and H C.
    exists C.
    split.
      intro.
      induction (eq_dec_points A B).
        subst B.
        subst C.
        intuition.
      subst C.
      Between.
    assert_cols.
    auto.
Qed.

Lemma diff_bet_ex3 : forall A B C,
 Bet A B C ->
 exists D, A <> D /\ B <> D /\ C <> D /\ Col A B D.
Proof.
    intros.
    induction (eq_dec_points A B).
      induction (eq_dec_points B C).
        assert (exists D, Bet B C D /\ C <> D).
          apply point_construction_different.
        ex_and H2 D.
        exists D.
        repeat split.
          subst C.
          subst A.
          assumption.
          subst A.
          subst C.
          assumption.
          assumption.
        unfold Col.
        left.
        subst A.
        subst C.
        assumption.
      assert (exists D, Bet B C D /\ C <> D).
        apply point_construction_different.
      ex_and H2 D.
      exists D.
      repeat split.
        intro.
        subst D.
        apply between_symmetry in H.
        apply H1.
        eapply between_equality.
          apply H2.
        apply H.
        intro.
        subst D.
        subst A.
        apply between_identity in H2.
        apply H3.
        subst B.
        reflexivity.
        assumption.
      unfold Col.
      left.
      eapply outer_transitivity_between.
        apply H.
        apply H2.
      assumption.
    induction (eq_dec_points B C).
      subst C.
      cut(exists D : Tpoint, A <> D /\ B <> D /\ Col A B D).
        intro.
        ex_and H1 D.
        exists D.
        repeat split.
          assumption.
          assumption.
          assumption.
        assumption.
      apply diff_col_ex.
    assert (exists D, Bet B C D /\ C <> D).
      apply point_construction_different.
    ex_and H2 D.
    exists D.
    repeat split.
      intro.
      subst D.
      assert (B = C).
        eapply between_equality.
          apply H2.
        apply between_symmetry.
        assumption.
      apply H1.
      assumption.
      intro.
      subst D.
      apply between_identity in H2.
      subst C.
      apply H1.
      reflexivity.
      assumption.
    unfold Col.
    left.
    eapply outer_transitivity_between.
      apply H.
      assumption.
    assumption.
Qed.

Lemma diff_col_ex3 : forall A B C,
 Col A B C -> exists D, A <> D /\ B <> D /\ C <> D /\ Col A B D.
Proof.
    intros.
    assert(cas1 := diff_bet_ex3 A B C).
    assert(cas2 := diff_bet_ex3 B C A).
    assert(cas3 := diff_bet_ex3 C A B).
    unfold Col in H.
    induction H.
      apply (diff_bet_ex3 A B C).
      assumption.
    induction H.
      assert (HH:=H).
      induction (eq_dec_points B C).
        subst C.
        assert (exists C, A <> C /\ B <> C /\ Col A B C).
          apply (diff_col_ex).
        ex_and H0 D.
        exists D.
        repeat split; assumption.
      apply cas2 in HH.
      ex_and HH D.
      exists D.
      repeat split; try assumption.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H0.
        assumption.
      unfold Col.
      left.
      assumption.
    induction (eq_dec_points A C).
      subst C.
      assert (exists C, A <> C /\ B <> C /\ Col A B C).
        apply (diff_col_ex).
      ex_and H0 D.
      exists D.
      repeat split; assumption.
    assert (HH:=H).
    apply cas3 in HH.
    ex_and HH D.
    exists D.
    repeat split; try assumption.
    apply col_permutation_5.
    eapply col_transitivity_1.
      apply H0.
      apply col_permutation_4.
      assumption.
    unfold Col.
    right;right.
    apply between_symmetry.
    assumption.
Qed.

Lemma mid_preserves_col : forall A B C M A' B' C',
  Col A B C ->
  is_midpoint M A A' ->
  is_midpoint M B B' ->
  is_midpoint M C C' ->
  Col A' B' C'.
Proof.
    intros.
    induction H.
      assert (Bet A' B' C').
        eapply l7_15 with A B C M;auto.
      assert_cols;Col.
    induction H.
      assert (Bet B' C' A').
        eapply l7_15 with B C A M;auto.
      assert_cols;Col.
    assert (Bet C' A' B').
      eapply l7_15 with C A B M;auto.
    assert_cols;Col.
Qed.

Lemma per_mid_per : forall A B X Y M,
   A <> B -> Per X A B ->
   is_midpoint M A B -> is_midpoint M X Y ->
   Cong A X B Y /\ Per Y B A.
Proof.
    intros.
    assert (Cong A X B Y).
      eapply l7_13.
        apply l7_2.
        apply H1.
      apply l7_2.
      assumption.
    split.
      assumption.
    unfold Per in H0.
    ex_and H0 B'.
    double A B A'.
    assert (Cong B X A Y).
      eapply l7_13.
        apply H1.
      apply l7_2.
      assumption.
    assert (OFSC B A B' X A B A' Y).
      unfold OFSC.
      repeat split.
        apply midpoint_bet.
        assumption.
        apply midpoint_bet.
        assumption.
        apply cong_pseudo_reflexivity.
        unfold is_midpoint in *.
        spliter.
        eapply cong_transitivity.
          apply cong_symmetry.
          apply H8.
        apply cong_left_commutativity.
        assumption.
        assumption.
      assumption.
    unfold Per.
    exists A'.
    split.
      assumption.
    assert (Cong B' X A' Y).
      eapply five_segment_with_def.
        apply H7.
      intro.
      apply H.
      subst B.
      reflexivity.
    eapply cong_transitivity.
      apply cong_commutativity.
      apply cong_symmetry.
      apply H6.
    eapply cong_transitivity.
      apply H4.
    apply cong_commutativity.
    assumption.
Qed.

Lemma perp_in_perp : forall A B C D X,
 Perp_in X A B C D -> Perp X B C D \/ Perp A X C D.
Proof.
    intros.
    induction (eq_dec_points X A).
      subst X.
      left.
      unfold Perp.
      exists A.
      assumption.
    right.
    unfold Perp.
    exists X.
    unfold Perp_in in *.
    spliter.
    repeat split.
      intro.
      apply H0.
      subst X.
      reflexivity.
      assumption.
      apply col_trivial_3.
      assumption.
    intros.
    apply H4.
      apply col_permutation_2.
      eapply col_transitivity_1.
        intro.
        apply H0.
        apply sym_equal.
        apply H7.
        Col.
      Col.
    assumption.
Qed.


Lemma sym_preserve_diff : forall A B M A' B',
 A <> B -> is_midpoint M A A' -> is_midpoint M B B' -> A'<> B'.
Proof.
    intros.
    intro.
    subst B'.
    assert (A = B).
      eapply l7_9.
        apply H0.
      assumption.
    contradiction.
Qed.


Lemma l9_4_1_aux : forall P Q A C R S M,
 le S C R A ->
 two_sides P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
 Perp P Q C S -> is_midpoint M R S ->
 (forall U C',is_midpoint M U C' -> (out R U A <-> out S C C')).
Proof.
    intros.
    induction (eq_dec_points R S).
      subst S.
      apply l7_3 in H5.
      subst R.
      unfold two_sides in H0.
      spliter.
      ex_and H8 T.
      induction (eq_dec_points M T).
        subst T.
        split.
          intro.
          unfold out in *.
          spliter.
          repeat split.
            intro.
            subst C.
            apply perp_distinct in H4.
            spliter.
            absurde.
            intro.
            subst C'.
            apply l7_2 in H6.
            eapply (symmetric_point_unicity _ _ M) in H6.
              apply H10.
              apply sym_equal.
              apply H6.
            apply l7_3_2.
          induction H12.
            assert (Bet U M C).
              eapply between_exchange3.
                apply between_symmetry.
                apply H12.
              assumption.
            unfold is_midpoint in H13.
            spliter.
            eapply l5_2.
              apply H10.
              assumption.
            apply midpoint_bet.
            assumption.
          assert (Bet U M C).
            eapply outer_transitivity_between2.
              apply between_symmetry.
              apply H12.
              assumption.
            assumption.
          eapply l5_2.
            apply H10.
            assumption.
          unfold is_midpoint in H6.
          spliter.
          assumption.
        intro.
        unfold out in *.
        spliter.
        repeat split.
          intro.
          subst U.
          eapply is_midpoint_id in H6.
          subst C'.
          apply H11.
          reflexivity.
          intro.
          subst A.
          apply perp_distinct in H2.
          spliter.
          apply H13.
          reflexivity.
        unfold is_midpoint in H6.
        spliter.
        assert (Bet A M C').
          induction H12.
            eapply outer_transitivity_between.
              apply H9.
              assumption.
            intro.
            apply H10.
            subst C.
            reflexivity.
          eapply between_inner_transitivity.
            apply H9.
          assumption.
        eapply l5_2.
          apply H11.
          apply between_symmetry.
          assumption.
        apply between_symmetry.
        assumption.
      assert (Perp M T A M) by (eapply perp_col2  with P Q;Col).
      apply perp_perp_in in H11.
      apply perp_in_comm in H11.
      eapply perp_in_per in H11.
      assert (Perp M T C M) by (eapply perp_col2  with P Q;Col).
      apply perp_perp_in in H12.
      apply perp_in_comm in H12.
      eapply perp_in_per in H12.
      assert (M = T).
        apply (l8_6 C M T A).
          3:Between.
          apply l8_2;auto.
        apply l8_2;auto.
      subst T.
      split.
        intro.
        unfold out in *.
        spliter.
        repeat split.
          intro.
          subst C.
          apply perp_distinct in H4.
          spliter.
          absurde.
          intro.
          subst C'.
          intuition.
        intuition.
      intuition.
    (*   R <> S  *)
    unfold le in H.
    ex_and H D.
    assert (C <> S).
      intro.
      subst S.
      apply perp_distinct in H4.
      spliter.
      absurde.
    assert (R <> D).
      intro.
      subst D.
      apply cong_identity in H8.
      apply H9.
      subst S.
      reflexivity.
    assert (Perp R S A R).
      eapply perp_col2.
        apply H2.
        assumption.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
    assert(exists M, is_midpoint M S R /\ is_midpoint M C D).
      unfold two_sides in H0.
      spliter.
      ex_and H14 T.
      eapply (l8_24 S R C A D T).
        apply perp_sym.
        apply perp_left_comm.
        eapply perp_col2.
          apply H4.
          assumption.
          apply col_permutation_1.
          assumption.
          apply col_permutation_1.
          assumption.
        apply perp_right_comm.
        apply perp_sym.
        assumption.
        eapply col3.
          apply H0.
          apply col_permutation_1.
          assumption.
          apply col_permutation_1.
          assumption.
        apply col_permutation_1.
        assumption.
        apply between_symmetry.
        assumption.
        assumption.
      assumption.
    ex_and H12 M'.
    apply l7_2 in H12.
    assert (M = M').
      eapply l7_17.
        apply H5.
      apply H12.
    subst M'.
    split.
      intro.
      unfold out in H14.
      spliter.
      unfold out.
      repeat split.
        assumption.
        eapply sym_preserve_diff.
          2:apply H6.
          apply H14.
        assumption.
      induction H16.
        assert(Bet R U D \/ Bet R D U).
          eapply l5_3.
            apply H16.
          assumption.
        induction H17.
          right.
          eapply l7_15.
            apply H5.
            apply H6.
            apply l7_2.
            apply H13.
          assumption.
        left.
        eapply l7_15.
          apply H5.
          apply l7_2.
          apply H13.
          apply H6.
        assumption.
      left.
      eapply l7_15.
        apply H5.
        apply l7_2.
        apply H13.
        apply H6.
      eapply between_exchange4.
        apply H.
      apply H16.
    unfold out.
    intros.
    spliter.
    repeat split.
      eapply sym_preserve_diff.
        apply H15.
        apply l7_2.
        apply H6.
      apply l7_2.
      assumption.
      intro.
      subst R.
      apply perp_distinct in H11.
      spliter.
      absurde.
    induction H16.
      eapply l5_1.
        apply H10.
        eapply l7_15.
          apply l7_2.
          apply H12.
          apply H13.
          apply l7_2.
          apply H6.
        assumption.
      assumption.
    left.
    eapply between_exchange4.
      eapply l7_15.
        apply l7_2.
        apply H12.
        apply l7_2.
        apply H6.
        apply H13.
      assumption.
    assumption.
Qed.

Lemma per_col_eq : forall A B C, Per A B C -> Col A B C -> B <> C -> A = B.
Proof.
    intros.
    unfold Per in H.
    ex_and H C'.
    assert_bet.
    assert_cols.
    assert (Col A C C') by ColR.
    assert (C = C' \/ is_midpoint A C C') by (eapply l7_20;Col).
    induction H7.
      treat_equalities.
      intuition.
    eapply l7_17;eauto.
Qed.


Lemma l9_4_1 : forall P Q A C R S M,
 two_sides P Q A C -> Col R P Q ->
 Perp P Q A R -> Col S P Q ->
 Perp P Q C S -> is_midpoint M R S ->
 (forall U C',is_midpoint M U C' -> (out R U A <-> out S C C')).
Proof.
    intros.
    assert (le S C R A \/ le R A S C).
      apply le_cases.
    induction H6.
      apply (l9_4_1_aux P Q A C R S M); assumption.
    assert((out R A U <-> out S C' C) -> (out R U A <-> out S C C')).
      intro.
      induction H7.
      split.
        intro.
        eapply l6_6.
        apply H7.
        apply l6_6.
        assumption.
      intro.
      apply l6_6.
      apply H8.
      apply l6_6.
      assumption.
    apply H7.
    assert((out S C' C <-> out R A U) -> (out R A U <-> out S C' C)).
      intro.
      induction H8.
      split.
        intro.
        apply H9.
        assumption.
      intro.
      apply H8.
      assumption.
    apply H8.
    eapply (l9_4_1_aux).
      assumption.
      apply l9_2.
      apply H.
      assumption.
      assumption.
      assumption.
      assumption.
      apply l7_2.
      apply H4.
    apply l7_2.
    assumption.
Qed.

Lemma mid_two_sides : forall A B M X Y,
 A <> B -> is_midpoint M A B -> ~ Col A B X -> is_midpoint M X Y ->
 two_sides A B X Y.
Proof.
    intros.
    unfold two_sides.
    repeat split.
      assumption.
      intro.
      apply col_permutation_1 in H3.
      contradiction.
      intro.
      apply H1.
      unfold is_midpoint in *.
      spliter.
      assert (Col A M Y).
        eapply col_transitivity_1.
          apply H.
          unfold Col.
          right; left.
          apply between_symmetry.
          assumption.
        apply col_permutation_1.
        assumption.
      assert (Col B M Y).
        eapply col_transitivity_1.
          intro.
          apply H.
          apply sym_equal.
          apply H7.
          unfold Col.
          right; left.
          assumption.
        apply col_permutation_3.
        assumption.
      assert (Y <> M).
        intro.
        subst M.
        apply cong_identity in H4.
        subst Y.
        apply H1.
        apply col_permutation_1.
        assumption.
      assert (Col Y A X).
        eapply col_transitivity_1.
          apply H8.
          apply col_permutation_3.
          assumption.
        unfold Col.
        left.
        apply between_symmetry.
        assumption.
      assert (Col Y B X).
        eapply col_transitivity_1.
          apply H8.
          apply col_permutation_3.
          assumption.
        unfold Col.
        left.
        apply between_symmetry.
        assumption.
      assert (X <> Y).
        intro.
        subst Y.
        apply between_identity in H2.
        contradiction.
      apply col_permutation_1.
      eapply col_transitivity_1.
        apply H11.
        apply col_permutation_2.
        assumption.
      apply col_permutation_2.
      assumption.
    exists M.
    unfold is_midpoint in *.
    spliter.
    split.
      unfold Col.
      right; right.
      apply between_symmetry.
      assumption.
    assumption.
Qed.

Lemma col_preserves_two_sides : forall A B C D X Y,
 A <> B -> C <> D -> Col A B C -> Col A B D ->
 two_sides A B X Y ->
 two_sides C D X Y.
Proof.
    intros.
    unfold two_sides in *.
    spliter.
    repeat split.
      assumption.
      intro.
      apply H4.
      apply col_permutation_1.
      eapply col3.
        apply H0.
        apply col_permutation_1.
        eapply col_transitivity_1.
          intro.
          apply H3.
          apply sym_equal.
          apply H8.
          apply col_permutation_4.
          assumption.
        apply col_permutation_4.
        assumption.
        apply col_permutation_1.
        assumption.
      apply col_permutation_1.
      eapply col_transitivity_1.
        apply H.
        assumption.
      assumption.
      intro.
      apply H5.
      apply col_permutation_1.
      eapply col3.
        apply H0.
        apply col_permutation_1.
        eapply col_transitivity_1.
          intro.
          apply H3.
          apply sym_equal.
          apply H8.
          apply col_permutation_4.
          assumption.
        apply col_permutation_4.
        assumption.
        apply col_permutation_1.
        assumption.
      apply col_permutation_1.
      eapply col_transitivity_1.
        apply H.
        assumption.
      assumption.
    ex_and H6 T.
    exists T.
    split.
      eapply col3.
        apply H3.
        apply col_permutation_1.
        assumption.
        assumption.
      assumption.
    assumption.
Qed.


Lemma out_out_two_sides : forall A B X Y U V I,
  A <> B ->
  two_sides A B X Y ->
  Col I A B -> Col I X Y ->
  out I X U -> out I Y V ->
  two_sides A B U V.
Proof.
    intros.
    unfold two_sides in *.
    spliter.
    repeat split.
      assumption.
      intro.
      apply H5.
      unfold out in H3.
      spliter.
      induction H10.
      ColR.
      ColR.
      intro.
      apply H6.
      unfold out in H4.
      spliter.
      induction H10.
      ColR.
      ColR.
    ex_and H7 T.
    assert (I = T).
      apply l6_21 with A B X Y; Col.
      intro; treat_equalities; Col.
    subst I.
    exists T.
    split.
      assumption.
    unfold out in *.
    spliter.
    induction H12; induction H10.
      assert (Bet U T Y).
        eapply outer_transitivity_between2.
          apply between_symmetry.
          apply H12.
          assumption.
        assumption.
      eapply outer_transitivity_between.
        apply H13.
        assumption.
      auto.
      assert (Bet U T Y).
        eapply outer_transitivity_between2.
          apply between_symmetry.
          apply H12.
          assumption.
        assumption.
      eapply between_inner_transitivity.
        apply H13.
      assumption.
      assert (Bet U T Y).
        eapply between_exchange3.
          apply between_symmetry.
          apply H12.
        assumption.
      eapply outer_transitivity_between.
        apply H13.
        assumption.
      intro.
      subst Y.
      apply H6.
      assumption.
    assert (Bet V T X).
      eapply between_exchange3.
        apply between_symmetry.
        apply H10.
      apply between_symmetry.
      assumption.
    eapply between_exchange3.
      apply between_symmetry.
      apply H12.
    apply between_symmetry.
    assumption.
Qed.

Lemma l9_4_2_aux : forall P Q A C R S U V, le S C R A ->
two_sides P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
Perp P Q C S -> out R U A -> out S V C -> two_sides P Q U V.
Proof.
    intros.
    induction (eq_dec_points R S).
      subst S.
      assert (TT:= H0).
      unfold two_sides in H0.
      spliter.
      ex_and H9 T.
      induction (eq_dec_points R T).
        subst T.
        clear H9 H3.
        apply (out_out_two_sides P Q A C U V R); auto using l6_6, bet_col with col.
      assert (Perp R T A R) by (eapply perp_col2  with P Q;Col).
      apply perp_perp_in in H12.
      apply perp_in_comm in H12.
      eapply perp_in_per in H12.
      assert (Perp R T C R) by (eapply perp_col2  with P Q;Col).
      apply perp_perp_in in H13.
      apply perp_in_comm in H13.
      eapply perp_in_per in H13.
      assert (R = T).
        apply (l8_6 C R T A).
          3:Between.
          apply l8_2;auto.
        apply l8_2;auto.
      subst.
      intuition.
    (********* R <> S ***************)
    assert(P <> Q).
      apply perp_distinct in H4.
      spliter.
      assumption.
    assert (two_sides R S A C).
      eapply (col_preserves_two_sides P Q).
        assumption.
        apply H7.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
      assumption.
    eapply (col_preserves_two_sides R S).
      assumption.
      assumption.
      eapply col_permutation_1.
      eapply col_transitivity_1.
        apply H8.
        apply col_permutation_1.
        assumption.
      apply col_permutation_1.
      assumption.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ P).
        auto.
        apply col_permutation_3.
        assumption.
      apply col_permutation_3.
      assumption.
    assert (Perp R S A R).
      eapply perp_col2.
        apply H2.
        assumption.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
    assert (Perp R S C S).
      eapply perp_col2.
        apply H4.
        assumption.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
    assert (HH9:=H9).
    unfold two_sides in HH9.
    spliter.
    ex_and H15 T.
    unfold le in H.
    ex_and H C'.
    assert (exists M, is_midpoint M S R /\ is_midpoint M C C').
      eapply (l8_24 S R C A C' T).
        apply perp_sym.
        apply perp_left_comm.
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        assumption.
        apply col_permutation_3.
        assumption.
        apply between_symmetry.
        assumption.
        assumption.
      assumption.
    ex_and H18 M.
    double U M U'.
    assert (R <> U).
      intro.
      subst U.
      unfold out in H5.
      spliter.
      absurde.
    assert (two_sides R S U U').
      eapply mid_two_sides.
        assumption.
        apply l7_2.
        apply H18.
        intro.
        apply H13.
        eapply col_permutation_2.
        eapply col_transitivity_1.
          apply H21.
          apply col_permutation_5.
          assumption.
        induction H5.
        spliter.
        induction H24.
          unfold Col.
          left.
          assumption.
        unfold Col.
        right; left.
        apply between_symmetry.
        assumption.
      assumption.
    apply l9_2.
    eapply l9_3.
      apply l9_2.
      apply H22.
      unfold Col.
      right; right.
      apply midpoint_bet.
      apply H18.
      apply l7_2.
      assumption.
      apply col_trivial_3.
    assert (forall X Y, is_midpoint M X Y -> (out R X A <-> out S C Y)).
      eapply l9_4_1.
        apply H9.
        apply col_trivial_1.
        assumption.
        apply col_trivial_3.
        assumption.
      apply l7_2.
      assumption.
    assert (out R U A <-> out S C U').
      eapply H23.
      assumption.
    destruct H24.
    eapply l6_7.
      apply l6_6.
      apply H24.
      assumption.
    apply l6_6.
    assumption.
Qed.


Lemma l9_4_2 : forall P Q A C R S U V,
two_sides P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
Perp P Q C S -> out R U A -> out S V C -> two_sides P Q U V.
Proof.
    intros.
    assert(le S C R A \/ le R A S C) by (apply le_cases).
    induction H6.
      eapply l9_4_2_aux with A C R S;assumption.
    apply l9_2.
    apply l9_2 in H.
    eapply l9_4_2_aux with C A S R;auto.
Qed.

Lemma l9_5 : forall P Q A C R B,
 two_sides P Q A C -> Col R P Q -> out R A B -> two_sides P Q B C.
Proof.
    intros.
    assert (P <> Q).
      unfold two_sides in H.
      spliter.
      assumption.
    assert(exists A0, Col P Q A0 /\ Perp P Q A A0).
      eapply l8_18_existence.
      intro.
      unfold two_sides in H.
      spliter.
      apply H4.
      apply col_permutation_2.
      assumption.
    assert(exists C0, Col P Q C0 /\ Perp P Q C C0).
      eapply l8_18_existence.
      unfold two_sides in H.
      spliter.
      intro.
      apply H5.
      apply col_permutation_2.
      assumption.
    assert(exists B0, Col P Q B0 /\ Perp P Q B B0).
      eapply l8_18_existence.
      assert (HH1:=H1).
      unfold out in HH1.
      unfold two_sides in H.
      spliter.
      intro.
      assert (Col P B R).
        eapply col_transitivity_1.
          apply H.
          assumption.
        apply col_permutation_1.
        assumption.
      assert (R <> B).
        intro.
        subst B.
        absurde.
      assert(Col R P A ).
        eapply col_transitivity_1.
          apply H13.
          eapply col_permutation_3.
          assumption.
        apply col_permutation_5.
        apply out_col.
        assumption.
      apply H8.
      ColR.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H5 B'.
    assert (exists M, is_midpoint M A' C').
      apply midpoint_existence.
    ex_and H9 M.
    double A M D.
    assert (out C' D C <-> out A' A A).
      eapply l9_4_1.
        apply l9_2.
        apply H.
        apply col_permutation_2.
        assumption.
        assumption.
        apply col_permutation_2.
        assumption.
        assumption.
        apply l7_2.
        apply H10.
      apply l7_2.
      assumption.
    destruct H11.
    assert (out C' D C).
      apply H12.
      unfold out.
      repeat split.
        intro.
        subst A'.
        apply perp_distinct in H6.
        spliter.
        absurde.
        intro.
        subst A'.
        apply perp_distinct in H6.
        spliter.
        absurde.
      left.
      apply between_trivial.
    assert (two_sides P Q A D).
      eapply l9_4_2.
        apply H.
        apply col_permutation_2.
        apply H3.
        assumption.
        apply col_permutation_2.
        apply H4.
        apply H7.
        unfold out.
        repeat split.
          intro.
          subst A'.
          apply perp_distinct in H6.
          spliter.
          absurde.
          intro.
          subst A'.
          apply perp_distinct in H6.
          spliter.
          absurde.
        left.
        apply between_trivial.
      assumption.
    assert (two_sides P Q B D).
      eapply l9_3.
        apply H14.
        2:apply H9.
        2: apply H0.
        2:assumption.
      induction (eq_dec_points A' C').
        subst C'.
        apply l7_3 in H10.
        subst A'.
        apply col_permutation_2.
        assumption.
      ColR.
    try assumption.
    eapply l9_4_2.
      apply H15.
      2: apply H8.
      apply col_permutation_2.
      assumption.
      apply col_permutation_2.
      apply H4.
      apply perp_sym.
      apply perp_left_comm.
      eapply perp_col.
        intro.
        subst D.
        unfold out in H13.
        spliter.
        absurde.
        apply perp_sym.
        apply perp_right_comm.
        apply H7.
      apply col_permutation_5.
      apply out_col.
      assumption.
      eapply out_trivial.
      intro.
      subst B.
      apply perp_distinct in H8.
      spliter.
      absurde.
    apply l6_6.
    assumption.
Qed.

(** This lemma used to be an axiom in previous versions of Tarski's axiom system. It is a been shown to a theorem by Gupta in his Phd 1965. *)
(** This corresponds to l9_6 in Tarski's book. *)

Lemma outer_pasch : forall A B C P Q,
 Bet A C P -> Bet B Q C -> exists X, Bet A X B /\ Bet P Q X.
Proof.
    intros.
    induction(Col_dec P Q C).
      induction(Bet_dec P Q C).
        exists A.
        split.
          Between.
        eapply between_exchange4 with C;Between.
      assert (out Q P C) by (apply l6_4_2;auto).
      exists B.
      split.
        Between.
      unfold out in H3.
      spliter.
      induction H5.
        apply between_exchange3 with C;Between.
      apply outer_transitivity_between2 with C;Between.
    induction (eq_dec_points B Q).
      subst Q;exists B;Between.
    show_distinct A P.
      intuition.
    show_distinct P Q.
      intuition.
    show_distinct P B.
      intuition.
    assert(two_sides P Q C B).
      unfold two_sides.
      repeat split.
        assumption.
        Col.
        assert_cols.
        intro;apply H1; ColR.
      exists Q; split;Col;Between.
    assert_diffs.
    assert (two_sides P Q A B) by (apply l9_5 with C P;unfold out;intuition).
    unfold two_sides in H7.
    spliter.
    ex_and H11 X.
    exists X.
    split.
      assumption.
    assert (exists T, Bet X T P /\ Bet C T B) by (apply inner_pasch with A;Between).
    ex_and H14 T.
    show_distinct B C.
      intuition.
    assert (T = Q).
      apply l6_21 with X P B C; assert_cols;Col.
      intro.
      apply H10.
      eapply col_permutation_2.
      eapply col_transitivity_1 with X.
        2:Col.
        intro.
        treat_equalities.
        apply H8.
        ColR.
      Col.
    subst T;Between.
Qed.

Definition one_side P Q A B :=
 exists C, two_sides P Q A C /\ two_sides P Q B C.

Lemma invert_one_side : forall A B P Q,
 one_side A B P Q -> one_side B A P Q.
Proof.
    unfold one_side.
    intros.
    ex_and H T.
    exists T.
    split; apply invert_two_sides; assumption.
Qed.

Lemma l9_8_1 : forall P Q A B C, two_sides P Q A C -> two_sides P Q B C -> one_side P Q A B.
Proof.
    intros.
    unfold one_side.
    exists C.
    split; assumption.
Qed.

Lemma not_two_sides_id : forall A P Q, ~ two_sides P Q A A.
Proof.
    intros.
    intro.
    unfold two_sides in H.
    spliter.
    ex_and H2 T.
    apply between_identity in H3.
    subst T.
    apply H0.
    apply H2.
Qed.

Lemma l9_8_2 : forall P Q A B C,
 two_sides P Q A C ->
 one_side P Q A B ->
 two_sides P Q B C.
Proof.
    intros.
    unfold one_side in H0.
    ex_and H0 D.
    assert (HH:= H).
    assert (HH0:=H0).
    assert (HH1:=H1).
    unfold two_sides in HH.
    unfold two_sides in HH0.
    unfold two_sides in HH1.
    spliter.
    ex_and H13 T.
    ex_and H9 X.
    ex_and H5 Y.
    assert (exists M , Bet Y M A /\ Bet X M B).
      eapply inner_pasch.
        apply H16.
      apply H15.
    ex_and H17 M.
    assert (A <> D).
      intro.
      subst D.
      apply not_two_sides_id in H0.
      assumption.
    assert (B <> D).
      intro.
      subst D.
      apply not_two_sides_id in H1.
      assumption.
    induction (Col_dec A B D).
      induction (eq_dec_points M Y).
        subst M.
        assert (X = Y).
          apply l6_21 with P Q A D; assert_cols; Col; ColR.
        subst Y.
        eapply l9_5.
          apply H.
          apply H9.
        unfold out.
        repeat split.
          intro.
          subst X.
          apply H11.
          assumption.
          intro.
          subst X.
          apply H3.
          assumption.
        unfold Col in H21.
        induction H21.
          right.
          eapply between_exchange3.
            apply between_symmetry.
            apply H16.
          apply between_symmetry.
          assumption.
        induction H21.
          assert (Bet D B A \/ Bet D A B).
            eapply (l5_1 _ X).
              intro.
              subst X.
              apply H4.
              assumption.
              apply between_symmetry.
              assumption.
            apply between_symmetry.
            assumption.
          induction H22.
            assert (D = B).
              eapply between_equality.
                apply H22.
              apply H21.
            subst D.
            absurde.
          assert (D = A).
            eapply between_equality.
              apply H22.
            apply between_symmetry.
            assumption.
          subst D.
          absurde.
        eapply (l5_2 D).
          intro.
          subst X.
          apply H8.
          assumption.
          apply between_symmetry.
          assumption.
        apply between_symmetry.
        assumption.
      induction (eq_dec_points M X).
        subst M.
        assert (X = Y).
          apply l6_21 with P Q A D; assert_cols; Col; ColR.
        subst Y.
        absurde.
      eapply (l9_5 _ _ M _ X).
        eapply l9_5.
          apply H.
          apply H5.
        unfold out.
        repeat split.
          intro.
          subst Y.
          apply between_identity in H17.
          subst M.
          absurde.
          assumption.
        right.
        assumption.
        assumption.
      unfold out.
      assert (out Y M  A).
        unfold out.
        repeat split.
          assumption.
          intro.
          subst Y.
          apply H11.
          assumption.
        left.
        assumption.
      repeat split.
        assumption.
        intro.
        subst X.
        apply between_identity in H18.
        subst M.
        absurde.
      left.
      apply H18.
    eapply (l9_5 _ _ M).
      eapply l9_5.
        apply H.
        apply H5.
      unfold out.
      repeat split.
        intro.
        subst Y.
        apply H7.
        assumption.
        intro.
        subst Y.
        assert(Col B D X).
          eapply (col_transitivity_1 _ M).
            intro.
            subst M.
            apply H3.
            assumption.
            unfold Col.
            left.
            assumption.
          unfold Col.
          left.
          apply between_symmetry.
          assumption.
        apply H21.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ X).
          intro.
          subst X.
          apply H4.
          assumption.
          unfold Col.
          left.
          apply between_symmetry.
          assumption.
        apply col_permutation_1.
        assumption.
      right.
      assumption.
      apply H9.
    unfold out.
    repeat split.
      intro.
      subst X.
      assert (Col A D Y).
        eapply (col_transitivity_1 _ M).
          intro.
          subst M.
          apply H7.
          assumption.
          unfold Col.
          left.
          assumption.
        unfold Col.
        left.
        apply between_symmetry.
        assumption.
      apply H21.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ Y).
        intro.
        subst Y.
        apply H4.
        assumption.
        apply col_permutation_1.
        assumption.
      unfold Col.
      left.
      apply between_symmetry.
      assumption.
      intro.
      subst X.
      apply H3.
      assumption.
    left.
    assumption.
Qed.

Lemma l9_9 : forall P Q A B, two_sides P Q A B -> ~ one_side P Q A B.
Proof.
    intros.
    intro.
    apply (l9_8_2 P Q A B B ) in H.
      apply not_two_sides_id in H.
      assumption.
    assumption.
Qed.

Lemma l9_9_bis : forall P Q A B, one_side P Q A B -> ~ two_sides P Q A B.
Proof.
    intros.
    intro.
    unfold one_side in H.
    ex_and H C.
    assert (one_side P Q A B).
      eapply l9_8_1.
        apply H.
      assumption.
    assert (~ one_side P Q A B).
      apply l9_9.
      assumption.
    contradiction.
Qed.

Lemma one_side_chara : forall P Q A B,
 P<>Q -> ~ Col A P Q-> ~ Col B P Q ->
 one_side P Q A B -> (forall X, Col X P Q -> ~ Bet A X B).
Proof.
    intros.
    intros.
    apply l9_9_bis in H2.
    intro.
    apply H2.
    unfold two_sides.
    repeat split.
      assumption.
      assumption.
      assumption.
    exists X.
    intuition.
Qed.

Lemma l9_10 : forall P Q A,
 P<>Q -> ~ Col A P Q -> exists C, two_sides P Q A C.
Proof.
    intros.
    double A P A'.
    exists A'.
    unfold two_sides.
    repeat split.
      assumption.
      assumption.
      intro.
      apply H0.
      eapply col_permutation_2.
      eapply (col_transitivity_1 _ A').
        intro.
        subst A'.
        apply l7_2 in H1.
        eapply is_midpoint_id in H1.
        subst A.
        apply H0.
        assumption.
        apply col_permutation_4.
        assumption.
      unfold Col.
      right; right.
      apply midpoint_bet.
      assumption.
    exists P.
    split.
      apply col_trivial_1.
    apply midpoint_bet.
    assumption.
Qed.



Lemma one_side_reflexivity : forall P Q A,
 ~ Col A P Q -> one_side P Q A A.
Proof.
    intros.
    unfold one_side.
    double A P C.
    exists C.
    assert (two_sides P Q A C).
      repeat split.
        intro.
        subst Q.
        apply H.
        apply col_trivial_2.
        assumption.
        intro.
        apply H.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ C).
          intro.
          subst C.
          apply l7_2 in H0.
          apply is_midpoint_id in H0.
          subst A.
          apply H.
          assumption.
          apply col_permutation_4.
          assumption.
        unfold Col.
        right; right.
        apply midpoint_bet.
        assumption.
      exists P.
      split.
        apply col_trivial_1.
      apply midpoint_bet.
      assumption.
    split; assumption.
Qed.


Lemma one_side_symmetry : forall P Q A B,
 one_side P Q A B -> one_side P Q B A.
Proof.
    unfold one_side.
    intros.
    ex_and H C.
    exists C.
    split; assumption.
Qed.

Lemma one_side_transitivity : forall P Q A B C,
one_side P Q A B -> one_side P Q B C -> one_side P Q A C.
Proof.
    intros.
    unfold one_side in *.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    split.
      assumption.
    apply l9_2.
    eapply l9_8_2.
      apply l9_2.
      apply H2.
    eapply l9_8_1.
      apply l9_2.
      apply H0.
    apply l9_2.
    assumption.
Qed.

Lemma col_eq : forall A B X Y,
  A <> X -> Col A X Y -> Col B X Y ->
 ~ Col A X B ->
 X = Y.
Proof.
    intros.
    apply eq_sym.
    apply l6_21 with A X B X; assert_diffs; Col.
Qed.

Lemma l9_17 : forall A B C P Q, one_side P Q A C -> Bet A B C -> one_side P Q A B.
Proof.
    intros.
    induction (eq_dec_points A C).
      subst C.
      apply between_identity in H0.
      subst B.
      assumption.
    assert( HH:= H).
    unfold one_side in H.
    ex_and H D.
    assert(HH1:=H).
    unfold two_sides in H.
    unfold two_sides in H2.
    spliter.
    ex_and H8 X.
    ex_and H5 Y.
    assert (exists T,  Bet B T D /\ Bet X T Y).
      eapply l3_17.
        apply H9.
        apply H10.
      assumption.
    ex_and H11 T.
    unfold one_side.
    exists D.
    split.
      assumption.
    unfold two_sides.
    repeat split.
      assumption.
      apply l9_9_bis in HH.
      intro.
      apply HH.
      unfold two_sides.
      repeat split.
        assumption.
        assumption.
        assumption.
      exists B.
      split.
        assumption.
      assumption.
      unfold two_sides in HH1.
      spliter.
      assumption.
    exists T.
    induction (Col_dec A C D).
      assert (X = Y).
        apply l6_21 with P Q A D; Col.
          intro.
          subst D.
          assert (one_side P Q A A).
            apply one_side_reflexivity.
            assumption.
          apply l9_9_bis in H14.
          contradiction.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ C).
            intro.
            subst D.
            apply between_identity in H10.
            subst Y.
            apply H3.
            assumption.
            assert_cols; Col.
            Col.
      subst Y.
      apply between_identity in H12.
      subst X.
      split.
        assumption.
      assumption.
    split.
      assert (X <> Y).
        intro.
        subst Y.
        apply between_identity in H12.
        subst X.
        apply H13.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ T).
          intro.
          subst D.
          contradiction.
          unfold Col.
          left.
          apply between_symmetry.
          assumption.
        unfold Col.
        left.
        apply between_symmetry.
        assumption.
      eapply col3.
        apply H14.
        unfold Col.
        right; left.
        apply between_symmetry.
        assumption.
        eapply col3.
          apply H.
          apply col_permutation_1.
          assumption.
          apply col_permutation_1.
          assumption.
        apply col_trivial_3.
      eapply col3.
        apply H.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
      apply col_trivial_2.
    assumption.
Qed.

Lemma l9_18 : forall X Y  A B P,
 X <> Y -> Col X Y P -> Col A B P -> (two_sides X Y A B <-> (Bet A P B /\ ~Col X Y A /\ ~Col X Y B)).
Proof.
    intros.
    split.
      intros.
      unfold two_sides in H2.
      spliter.
      ex_and H5 T.
      assert (P=T).
        apply l6_21 with X Y A B; Col.
        intro.
        subst B.
        apply between_identity in H6.
        subst A.
        contradiction.
      subst T.
      repeat split.
        assumption.
        intro.
        apply H3.
        apply col_permutation_2.
        assumption.
      intro.
      apply H4.
      apply col_permutation_2.
      assumption.
    intro.
    unfold two_sides.
    spliter.
    repeat split.
      assumption.
      intro.
      apply H3.
      apply col_permutation_1.
      assumption.
      intro.
      apply H4.
      apply col_permutation_1.
      assumption.
    exists P.
    split.
      apply col_permutation_2.
      assumption.
    assumption.
Qed.

Lemma l9_19 : forall X Y A B P ,
 X <> Y -> Col X Y P -> Col A B P -> (one_side X Y A B <-> (out P A B /\ ~Col X Y A)).
Proof.
    intros.
    split.
      intro.
      assert (HH2:=H2).
      unfold one_side in H2.
      ex_and H2 D.
      unfold two_sides in *.
      spliter.
      ex_and H6 M.
      ex_and H9 N.
      split.
        unfold out.
        repeat split.
          intro.
          subst P.
          apply H7.
          apply col_permutation_2.
          assumption.
          intro.
          subst P.
          apply H4.
          apply col_permutation_2.
          assumption.
        unfold Col in H1.
        induction H1.
          right.
          apply between_symmetry.
          assumption.
        induction H1.
          apply False_ind.
          assert (two_sides X Y A B).
            unfold two_sides.
            repeat split.
              assumption.
              assumption.
              assumption.
            exists P.
            split.
              apply col_permutation_2.
              assumption.
            apply between_symmetry.
            assumption.
          apply l9_9_bis in HH2.
          contradiction.
        left.
        assumption.
      intro.
      apply H7.
      Col.
    intros.
    spliter.
    assert (exists D, two_sides X Y A D).
      apply l9_10.
        assumption.
      intro.
      apply H3.
      apply col_permutation_1.
      assumption.
    ex_elim H4 D.
    unfold one_side.
    exists D.
    split.
      assumption.
    eapply l9_5.
      apply H5.
      apply col_permutation_2.
      apply H0.
    assumption.
Qed.

Lemma one_side_not_col :
 forall A B X Y,
  one_side A B X Y ->
  ~ Col A B X.
Proof.
    intros.
    unfold one_side in H.
    ex_and H C.
    unfold two_sides in *.
    spliter.
    intro.
    apply H4.
    apply col_permutation_2.
    assumption.
Qed.

Lemma col_two_sides : forall A B C P Q,
 Col A B C -> A <> C -> two_sides A B P Q ->
 two_sides A C P Q.
Proof.
    intros.
    unfold two_sides in *.
    spliter.
    ex_and H4 T.
    repeat split.
      assumption.
      intro.
      apply H2.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H0.
        apply col_permutation_5.
        assumption.
      apply col_permutation_1.
      assumption.
      intro.
      apply H3.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H0.
        apply col_permutation_5.
        assumption.
      apply col_permutation_1.
      assumption.
    exists T.
    split.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H1.
        assumption.
      apply col_permutation_1.
      assumption.
    assumption.
Qed.

Lemma col_one_side : forall A B C P Q,
  Col A B C -> A <> C -> one_side A B P Q -> one_side A C P Q.
Proof.
    unfold one_side.
    intros.
    ex_and H1 T.
    exists T.
    split; eapply (col_two_sides _ B); assumption.
Qed.

Lemma out_out_one_side :
 forall A B X Y Z,
  one_side A B X Y ->
  out A Y Z ->
  one_side A B X Z.
Proof.
    intros.
    assert (A <> B).
      unfold one_side in H.
      ex_and H C.
      unfold two_sides in H.
      spliter.
      assumption.
    prolong Y A Y' A Y.
    assert(one_side A B Y Z).
      unfold one_side.
      exists Y'.
      split.
        unfold two_sides.
        repeat split.
          assumption.
          apply one_side_symmetry in H.
          eapply one_side_not_col in H.
          intro.
          apply H.
          apply col_permutation_1.
          assumption.
          intro.
          apply one_side_symmetry in H.
          eapply one_side_not_col in H.
          apply H.
          assert(Col A B Y).
            eapply (col_transitivity_1 _ Y').
              intro.
              subst Y'.
              apply cong_symmetry in H3.
              apply cong_identity in H3.
              subst Y.
              unfold out in H0.
              spliter.
              absurde.
              apply col_permutation_4.
              assumption.
            unfold Col.
            right; right.
            assumption.
          assumption.
        exists A.
        split.
          apply col_trivial_1.
        assumption.
      unfold two_sides.
      repeat split.
        assumption.
        intro.
        apply one_side_symmetry in H.
        eapply one_side_not_col in H.
        apply H.
        eapply (col_transitivity_1 _ Z).
          intro.
          subst Z.
          unfold out in H0.
          spliter.
          absurde.
          apply col_permutation_4.
          assumption.
        apply out_col in H0.
        apply col_permutation_5.
        assumption.
        apply one_side_symmetry in H.
        eapply one_side_not_col in H.
        intro.
        apply H.
        eapply (col_transitivity_1 _ Y').
          intro.
          subst Y'.
          apply cong_symmetry in H3.
          apply cong_identity in H3.
          subst Y.
          apply H.
          apply col_trivial_3.
          apply col_permutation_4.
          assumption.
        unfold Col.
        right; right.
        assumption.
      exists A.
      split.
        apply col_trivial_1.
      unfold out in H0.
      spliter.
      induction H5.
        apply between_symmetry.
        eapply outer_transitivity_between.
          apply between_symmetry.
          apply H2.
          assumption.
        auto.
      apply between_symmetry.
      eapply between_inner_transitivity.
        apply between_symmetry.
        apply H2; spliter.
      assumption.
    eapply one_side_transitivity.
      apply H.
    apply H4.
Qed.

Lemma out_one_side : forall A B X Y, (~Col A B X \/ ~ Col A B Y) -> out A X Y -> one_side A B X Y.
Proof.
    intros.
    induction H.
      assert(~ Col X A B).
        intro.
        apply H.
        apply col_permutation_1.
        assumption.
      assert(HH:=one_side_reflexivity A B X H1).
      eapply (out_out_one_side _ _ _ _ _ HH H0).
    assert(~ Col Y A B).
      intro.
      apply H.
      apply col_permutation_1.
      assumption.
    assert(HH:=one_side_reflexivity A B Y H1).
    apply one_side_symmetry.
    eapply (out_out_one_side _ _ _ _ _ HH).
    apply l6_6.
    assumption.
Qed.

Lemma l9_31 :
 forall A X Y Z,
  one_side A X Y Z ->
  one_side A Z Y X ->
  two_sides A Y X Z.
Proof.
    intros.
    assert(A <> X /\ A <> Z /\ ~ Col Y A X  /\ ~ Col Z A X /\ ~Col Y A Z).
      unfold one_side in *.
      ex_and H C.
      ex_and H0 D.
      unfold two_sides in *.
      spliter.
      repeat split; assumption.
    spliter.
    prolong Z A Z' Z A.
    assert(Z' <> A).
      intro.
      subst Z'.
      apply cong_symmetry in H7.
      apply cong_identity in H7.
      subst Z.
      absurde.
    assert(two_sides A X Y Z').
      eapply (l9_8_2 _ _ Z).
        unfold two_sides.
        repeat split.
          assumption.
          assumption.
          intro.
          apply H4.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ Z').
            auto.
            apply col_permutation_4.
            assumption.
          apply col_permutation_1.
          apply bet_col.
          assumption.
        exists A.
        split.
          apply col_trivial_1.
        assumption.
      apply one_side_symmetry.
      assumption.
    unfold two_sides in H9.
    spliter.
    ex_and H12 T.
    assert(T <> A).
      intro.
      subst T.
      apply H5.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ Z').
        auto.
        apply col_permutation_1.
        apply bet_col.
        assumption.
      apply col_permutation_1.
      apply bet_col.
      assumption.
    assert(one_side Y A Z' T).
      eapply out_one_side.
        left.
        intro.
        apply H5.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ Z').
          auto.
          apply bet_col in H6.
          apply col_permutation_1.
          assumption.
        apply col_permutation_1.
        assumption.
      apply l6_6.
      apply bet_out.
        intro.
        subst T.
        contradiction.
        intro.
        subst Z'.
        apply between_identity in H13.
        subst T.
        contradiction.
      assumption.
    unfold Col in H12.
    induction H12.
      assert(one_side Z' Z Y T).
        apply out_one_side.
          left.
          intro.
          apply H5.
          eapply col_permutation_1.
          eapply (col_transitivity_1 _ Z').
            intro.
            subst Z'.
            apply between_identity in H6.
            subst Z.
            apply H4.
            apply col_trivial_1.
            apply col_permutation_4.
            assumption.
          apply bet_col in H6.
          apply col_permutation_5.
          assumption.
        apply l6_6.
        apply bet_out.
          intro.
          subst T.
          apply H11.
          apply bet_col.
          assumption.
          intro.
          subst Z'.
          assert(Y = T).
            apply between_identity.
            assumption.
          subst T.
          apply H3.
          apply bet_col.
          assumption.
        apply between_symmetry.
        assumption.
      assert(one_side A Z Y T).
        apply invert_one_side.
        eapply (col_one_side _ Z').
          apply bet_col in H6.
          apply col_permutation_5.
          assumption.
          auto.
        apply invert_one_side.
        assumption.
      assert(two_sides A Z X T).
        repeat split.
          intro.
          subst Z.
          absurde.
          intro.
          apply H11.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ Z).
            assumption.
            apply col_permutation_1.
            assumption.
          apply bet_col in H6.
          apply col_permutation_4.
          assumption.
          unfold one_side in H17.
          ex_and H17 C.
          unfold two_sides in H18.
          spliter.
          assumption.
        exists A.
        split.
          apply col_trivial_1.
        apply between_symmetry.
        assumption.
      assert(two_sides A Z Y X).
        eapply l9_8_2.
          eapply l9_2.
          apply H18.
        apply one_side_symmetry.
        assumption.
      apply l9_9 in H19.
      contradiction.
    assert(one_side A Z T X).
      apply out_one_side.
        right.
        intro.
        apply H4.
        apply col_permutation_4.
        assumption.
      repeat split.
        assumption.
        auto.
      induction H12.
        right.
        assumption.
      left.
      apply between_symmetry.
      assumption.
    assert(two_sides A Y Z' Z).
      repeat split.
        intro.
        subst Y.
        apply H3.
        apply col_trivial_1.
        unfold one_side in H5.
        ex_and H15 C.
        unfold two_sides in H15.
        spliter.
        intro.
        apply H18.
        apply col_permutation_5.
        assumption.
        intro.
        apply H5.
        apply col_permutation_3.
        assumption.
      exists A.
      split.
        apply col_trivial_1.
      apply between_symmetry.
      assumption.
    assert(one_side A Y T X).
      apply out_one_side.
        left.
        unfold one_side in H15.
        ex_and H15 C.
        unfold two_sides in H18.
        spliter.
        intro.
        apply H19.
        apply col_permutation_3.
        assumption.
      repeat split.
        assumption.
        auto.
      induction H12.
        right.
        assumption.
      left.
      apply between_symmetry.
      assumption.
    apply invert_one_side in H15.
    assert (one_side A Y Z' X).
      eapply one_side_transitivity.
        apply H15.
      assumption.
    eapply l9_8_2.
      apply H17.
    assumption.
Qed.

Lemma col123__nos : forall A B P Q, Col P Q A -> ~ one_side P Q A B.
Proof.
  intros A B P Q HCol.
  intro HOne.
  assert (~ Col P Q A) by (apply (one_side_not_col P Q A B); auto).
  auto.
Qed.

Lemma col124__nos : forall A B P Q, Col P Q B -> ~ one_side P Q A B.
Proof.
  intros A B P Q HCol.
  intro HOne.
  assert (HN : ~ one_side P Q B A) by (apply col123__nos; auto).
  apply HN; apply one_side_symmetry; auto.
Qed.

Lemma col2_os__os : forall A B C D X Y, C <> D -> Col A B C ->
   Col A B D -> one_side A B X Y -> one_side C D X Y.
Proof.
  intros A B C D X Y HCD HColC HColD Hos.
  destruct Hos as [Z [Hts1 Hts2]].
  assert(A<>B) by (destruct Hts1; auto).
  exists Z.
  split; apply (col_preserves_two_sides A B); auto.
Qed.

Lemma os_out_os : forall A B C D C' P , Col A B P -> one_side A B C D -> out P C C' -> one_side A B C' D.
Proof.
    intros.
    assert(A <> B /\ ~ Col C A B).
      unfold one_side in H0.
      ex_and H0 T.
      unfold two_sides in H0.
      tauto.
    spliter.
    prolong C P T C P.
    assert(P <> T).
      intro.
      subst T.
      treat_equalities.
      Col.
    assert(two_sides A B C T).
      unfold two_sides.
      repeat split; Col.
        intro.
        apply H3.
        assert_cols. ColR.
      exists P.
      split; Col.
    assert(two_sides A B T C').
      apply bet_col in H4.
      eapply (out_out_two_sides _ _ T C _ _ P); Col.
        apply l9_2.
        assumption.
      apply out_trivial.
      auto.
    assert(one_side A B C C').
      eapply l9_8_1.
        apply H7.
      apply l9_2.
      assumption.
    eauto using one_side_transitivity, one_side_symmetry.
Qed.

Lemma ts_ts_os : forall A B C D, two_sides A B C D -> two_sides C D A B -> one_side A C B D.
Proof.
    intros.
    unfold two_sides in *.
    spliter.
    ex_and H6 T1.
    ex_and H3 T.
    assert(T1 = T).
      assert_cols.
      apply (l6_21 C D A B); Col.
    subst T1.

assert(one_side A C T B).
apply(out_one_side A C T B).
right.
intro.
apply H4.
Col.
unfold out.
repeat split.
intro.
subst T.
contradiction.
intro.
subst B.
apply H4.
Col.
left.
assumption.

assert(one_side C A T D).
apply(out_one_side C A T D).
right.
intro.
apply H1.
Col.
unfold out.
repeat split.
intro.
subst T.
contradiction.
intro.
subst D.
apply H1.
Col.
left.
assumption.
apply invert_one_side in H10.
apply (one_side_transitivity A C B T).
apply one_side_symmetry.
assumption.
assumption.
Qed.

Lemma two_sides_not_col :
 forall A B X Y,
  two_sides A B X Y ->
  ~ Col A B X.
Proof.
    intros.
    unfold two_sides in H.
    spliter.
    intro.
    apply H0.
    apply col_permutation_2.
    assumption.
Qed.

Lemma col_one_side_out : forall A B X Y,
 Col A X Y ->
 one_side A B X Y ->
 out A X Y.
Proof.
    intros.
    assert(X <> A /\ Y <> A).
      unfold one_side in H0.
      ex_and H0 Z.
      unfold two_sides in *.
      spliter.
      ex_and H7 T0.
      ex_and H4 T1.
      split.
        intro.
        subst X.
        apply H5.
        apply col_trivial_1.
      intro.
      subst Y.
      apply H2.
      apply col_trivial_1.
    spliter.
    unfold Col in H.
    induction H.
      unfold out.
      repeat split; try assumption.
      left.
      assumption.
    induction H.
      unfold out.
      repeat split; try assumption.
      right.
      apply between_symmetry.
      assumption.
    assert(two_sides A B X Y).
      unfold two_sides.
      assert(HH0 := H0).
      unfold one_side in H0.
      ex_and H0 Z.
      unfold two_sides in *.
      spliter.
      repeat split.
        assumption.
        assumption.
        assumption.
      exists A.
      split.
        apply col_trivial_1.
      apply between_symmetry.
      assumption.
    eapply l9_9 in H3.
    contradiction.
Qed.

Lemma col_two_sides_bet :
 forall A B X Y,
 Col A X Y ->
 two_sides A B X Y ->
 Bet X A Y.
Proof.
    intros.
    unfold Col in H.
    induction H.
      unfold two_sides in H0.
      spliter.
      ex_and H3 T.
      apply False_ind.
      apply H2.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ T).
        intro.
        subst T.
        assert(A = X).
          eapply between_equality.
            apply H.
          assumption.
        subst X.
        apply H1.
        apply col_trivial_1.
        apply col_permutation_4.
        assumption.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ X).
        intro.
        subst Y.
        apply between_identity in H4.
        subst X.
        contradiction.
        apply bet_col in H.
        apply col_permutation_3.
        assumption.
      apply col_permutation_2.
      apply bet_col.
      assumption.
    induction H.
      unfold two_sides in H0.
      spliter.
      ex_and H3 T.
      assert(Col Y A T).
        eapply (col_transitivity_1 _ X).
          intro.
          subst Y.
          apply between_identity in H4.
          subst X.
          contradiction.
          apply col_permutation_4.
          apply bet_col.
          assumption.
        apply col_permutation_2.
        apply bet_col.
        assumption.
      apply False_ind.
      apply H2.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ T).
        intro.
        subst T.
        assert(A = Y).
          eapply between_equality.
            apply between_symmetry.
            apply H.
          apply between_symmetry.
          assumption.
        subst Y.
        apply H2.
        apply col_trivial_1.
        apply col_permutation_4.
        assumption.
      apply col_permutation_1.
      assumption.
    apply between_symmetry.
    assumption.
Qed.

Lemma os_ts1324__os : forall A X Y Z,
  one_side A X Y Z ->
  two_sides A Y X Z ->
  one_side A Z X Y.
Proof.
  intros A X Y Z Hos Hts.
  destruct Hts as [HAY [HNColXY [HNColYZ [P [HColP HPBet]]]]].
  apply (one_side_transitivity _ _ _ P).
  - apply invert_one_side.
    apply one_side_symmetry.
    apply one_side_symmetry in Hos.
    apply one_side_not_col in Hos.
    apply out_one_side; Col.
    apply bet_out; Between; intro; subst Z; Col.

  - apply out_one_side.
    right; Col.
    apply (col_one_side_out _ X); Col.
    apply one_side_symmetry in Hos.
    apply (one_side_transitivity _ _ _ Z); auto.
    apply invert_one_side.
    apply one_side_not_col in Hos.
    apply out_one_side; Col.
    apply bet_out; auto; intro; subst X; Col.
Qed.

End T9.

Hint Resolve l9_2 invert_two_sides invert_one_side one_side_symmetry l9_9 l9_9_bis : side.

Ltac Side := auto with side.
