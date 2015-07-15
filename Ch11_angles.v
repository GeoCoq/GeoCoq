Require Export Ch10_line_reflexivity_2D.

Ltac permut :=
match goal with
   |H : (Col ?X ?Y ?Z) |- Col ?X ?Y ?Z => assumption
   |H : (Col ?X ?Y ?Z) |- Col ?Y ?Z ?X => apply col_permutation_1; assumption
   |H : (Col ?X ?Y ?Z) |- Col ?Z ?X ?Y => apply col_permutation_2; assumption
   |H : (Col ?X ?Y ?Z) |- Col ?X ?Z ?Y => apply col_permutation_5; assumption
   |H : (Col ?X ?Y ?Z) |- Col ?Y ?X ?Z => apply col_permutation_4; assumption
   |H : (Col ?X ?Y ?Z) |- Col ?Z ?Y ?X => apply col_permutation_3; assumption
   |_ : _ |- _ => idtac
end.

Ltac bet :=
match goal with
   |H0 : Bet ?A ?B ?C |- Bet ?A ?B ?C => assumption
   |H0 : Bet ?A ?B ?C, H1 : Bet ?B ?C ?D , H : ?B <> ?C |- Bet ?A ?B ?D => apply (outer_transitivity_between _ _ _ _ H0 H1 H)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?B ?C ?D , H : ?B <> ?C |- Bet ?A ?C ?D => apply (outer_transitivity_between2 _ _ _ _ H0 H1 H)
   |H0 : Bet ?A ?B ?D, H1 : Bet ?B ?C ?D  |- Bet ?A ?B ?C => apply (between_inner_transitivity _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?A ?C ?D  |- Bet ?B ?C ?D => apply (between_exchange3 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?D, H1 : Bet ?B ?C ?D  |- Bet ?A ?C ?D => apply (between_exchange2 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?A ?C ?D  |- Bet ?A ?B ?D => apply (between_exchange4 _ _ _ _ H0 H1)

   |H0 : Bet ?A ?B ?C |- Bet ?A ?B ?C => assumption
   |H0 : Bet ?A ?B ?C, H1 : Bet ?B ?C ?D , H : ?B <> ?C |- Bet ?D ?B ?A => apply between_symmetry; apply (outer_transitivity_between _ _ _ _ H0 H1 H)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?B ?C ?D , H : ?B <> ?C |- Bet ?D ?C ?A => apply (outer_transitivity_between2 _ _ _ _ H0 H1 H)
   |H0 : Bet ?A ?B ?D, H1 : Bet ?B ?C ?D  |- Bet ?C ?B ?A => apply between_symmetry; apply (between_inner_transitivity _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?A ?C ?D  |- Bet ?D ?C ?B => apply between_symmetry; apply (between_exchange3 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?D, H1 : Bet ?B ?C ?D  |- Bet ?D ?C ?A => apply between_symmetry; apply (between_exchange2 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?A ?C ?D  |- Bet ?D ?B ?A => apply between_symmetry; apply (between_exchange4 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C |- Bet ?C ?B ?A => apply (between_symmetry _ _ _  H0)

   |H0 : Bet ?A ?B ?C |- Bet ?C ?B ?A => apply (between_symmetry _ _ _  H0)
   |_ : _ |- Bet ?A ?B ?B => apply between_trivial
   |_ : _ |- Bet ?A ?A ?B => apply between_trivial2
   |_ : _ |- _ => idtac
end.

Ltac cong :=
match goal with
   |_ :  Cong ?A ?B ?C ?BD |- Cong ?A ?B ?C ?D => assumption
   |_ : _ |- Cong ?A ?B ?A ?B => apply cong_reflexivity
   |_ : _ |- Cong ?A ?A ?B ?B => apply cong_trivial_identity

   |H0 : Cong ?A ?B ?C ?D |- Cong ?A ?B ?C ?C => assumption
   |H0 : Cong ?A ?B ?C ?D |- Cong ?A ?B ?D ?C => apply (cong_right_commutativity _ _ _ _ H0)
   |H0 : Cong ?A ?B ?C ?D |- Cong ?B ?A ?D ?C => apply (cong_commutativity _ _ _ _ H0)
   |H0 : Cong ?A ?B ?C ?D |- Cong ?B ?A ?C ?D => apply (cong_left_commutativity _ _ _ _ H0)

   |H0 : Cong ?A ?B ?C ?D |- Cong ?C ?D ?A ?B => apply (cong_symmetry _ _ _ _ H0)
   |H0 : Cong ?A ?B ?C ?D |- Cong ?C ?D ?B ?A => apply (cong_symmetry _ _ _ _ (cong_left_commutativity _ _ _ _ H0))
   |H0 : Cong ?A ?B ?C ?D |- Cong ?D ?C ?B ?B => apply (cong_symmetry _ _ _ _ (cong_commutativity _ _ _ _ H0))
   |H0 : Cong ?A ?B ?C ?D |- Cong ?D ?C ?A ?B => apply (cong_symmetry _ _ _ _ (cong_right_commutativity _ _ _ _ H0))
   |_ : _ |- _ => idtac
end.

Section T11.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Definition Conga := fun A B C D E F =>
 A <> B /\ C <> B /\ D <> E /\ F <> E /\
 exists A', exists C', exists D', exists F',
 Bet B A A' /\ Cong A A' E D /\
 Bet B C C' /\ Cong C C' E F /\
 Bet E D D' /\ Cong D D' B A /\
 Bet E F F' /\ Cong F F' B C /\
 Cong A' C' D' F'.

Lemma l11_3 : forall A B C D E F,
Conga A B C D E F ->
 exists A', exists C', exists D', exists F',
 out B A' A /\ out B C C' /\ out E D' D /\ out E F F' /\
 Cong_3 A' B C' D' E F'.
Proof.
    intros.
    unfold Conga in H.
    spliter.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H3 D'.
    ex_and H4 F'.
    exists A'.
    exists C'.
    exists D'.
    exists F'.
    repeat split.
      intro.
      subst A'.
      apply between_identity in H3.
      subst B.
      absurde.
      assumption.
      right.
      assumption.
      assumption.
      intro.
      subst C'.
      apply between_identity in H5.
      subst C.
      absurde.
      left.
      assumption.
      intro.
      subst D'.
      apply between_identity in H7.
      subst E.
      absurde.
      assumption.
      right.
      assumption.
      assumption.
      intro.
      subst F'.
      apply between_identity in H9.
      subst F.
      absurde.
      left.
      assumption.
      2:assumption.
      apply cong_left_commutativity.
      eapply l2_11.
        apply H3.
        apply between_symmetry.
        apply H7.
        Cong.
      Cong.
    apply cong_left_commutativity.
    eapply l2_11; eBetween;eCong.
Qed.

Lemma cong_preserves_bet : forall B A' A0 E D' D0,
  Bet B A' A0 -> Cong B A' E D' -> Cong B A0 E D0 -> out E D' D0 ->
  Bet E D' D0.
Proof.
    intros.
    unfold out in H2.
    spliter.
    induction H4.
      assumption.
    assert (le E D0 E D').
      eapply l5_5_2.
      exists D'.
      split.
        assumption.
      cong.
    assert(le E D' E D0).
      eapply l5_6.
      repeat split.
        2:apply H0.
        2:apply H1.
      eapply l5_5_2.
      exists A0.
      split.
        assumption.
      cong.
    assert(Cong E D' E D0).
      apply le_anti_symmetry.
        assumption.
      assumption.
    assert(D0 = D').
      eapply between_cong.
        apply H4.
      cong.
    subst D'.
    bet.
Qed.

Lemma l11_aux : forall B A A' A0 E D D' D0,
      out B A A' -> out E D D' -> Cong B A' E D' ->
      Bet B A A0 -> Bet E D D0 -> Cong A A0 E D
      -> Cong D D0 B A -> Cong B A0 E D0 /\ Cong A' A0 D' D0.
Proof.
    intros.
    assert (A <> B).
      unfold out in H.
      spliter.
      assumption.
    assert(Cong B A0 E D0).
      apply cong_right_commutativity.
      eapply (l2_11).
        apply H2.
        apply between_symmetry.
        apply H3.
        apply cong_right_commutativity.
        apply cong_symmetry.
        apply H5.
      apply cong_right_commutativity.
      apply H4.
    split.
      apply H7.
    unfold out in *.
    spliter.
    induction H9; induction H11.
      assert(Bet B A' A0 \/ Bet B A0 A').
        eapply l5_1.
          2:apply H11.
          auto.
        apply H2.
      induction H12.
        assert(Bet E D' D0).
          eapply cong_preserves_bet.
            2: apply H1.
            apply H12.
            assumption.
          unfold out.
          repeat split.
            assumption.
            intro.
            subst D0.
            apply cong_identity in H7.
            subst A0.
            apply between_identity in H2.
            subst B.
            absurde.
          eapply l5_1.
            2:apply H9.
            auto.
          assumption.
        apply cong_commutativity.
        eapply l4_3.
          apply between_symmetry.
          apply H12.
          apply between_symmetry.
          apply H13.
          apply cong_commutativity.
          assumption.
        apply cong_commutativity.
        assumption.
      assert(Bet E D0 D').
        eapply cong_preserves_bet.
          2: apply H7.
          apply H12.
          assumption.
        unfold out.
        repeat split.
          intro.
          subst D0.
          apply cong_identity in H7.
          subst A0.
          apply between_identity in H2.
          subst B.
          absurde.
          assumption.
        eapply l5_1.
          2:apply H3.
          auto.
        assumption.
      eapply l4_3.
        apply between_symmetry.
        apply H12.
        apply between_symmetry.
        apply H13.
        apply cong_commutativity.
        assumption.
      apply cong_commutativity.
      assumption.
      apply cong_commutativity.
      eapply l4_3.
        3:apply cong_commutativity.
        3:apply H7.
        apply between_symmetry.
        eapply between_exchange4.
          apply H11.
        assumption.
        apply between_symmetry.
        eapply cong_preserves_bet.
          2: apply H1.
          2: apply H7.
          eapply between_exchange4.
            apply H11.
          assumption.
        unfold out.
        repeat split.
          assumption.
          intro.
          subst D0.
          apply cong_identity in H7.
          subst A0.
          apply between_identity in H2.
          subst B.
          absurde.
        eapply l5_1.
          2:apply H9.
          auto.
        assumption.
      apply cong_commutativity.
      assumption.
      apply cong_commutativity.
      eapply l4_3.
        3:apply cong_commutativity.
        3:apply H7.
        apply between_symmetry.
        eapply cong_preserves_bet.
          2:apply cong_symmetry.
          2:apply H1.
          2:apply cong_symmetry.
          2:apply H7.
          eapply between_exchange4.
            apply H9.
          assumption.
        unfold out.
        repeat split.
          assumption.
          intro.
          subst A0.
          apply cong_symmetry in H7.
          apply cong_identity in H7.
          subst D0.
          apply between_identity in H2.
          subst B.
          absurde.
        eapply l5_1.
          2:apply H11.
          auto.
        assumption.
        apply between_symmetry.
        eapply between_exchange4.
          apply H9.
        assumption.
      apply cong_commutativity.
      assumption.
    apply cong_commutativity.
    eapply l4_3.
      3:apply cong_commutativity.
      3:apply H7.
      apply between_symmetry.
      eapply between_exchange4.
        apply H11.
      assumption.
      apply between_symmetry.
      eapply between_exchange4.
        apply H9.
      assumption.
    apply cong_commutativity.
    assumption.
Qed.

Lemma l11_3_bis : forall A B C D E F,
 (exists A', exists C', exists D', exists F',
 out B A' A /\ out B C' C /\ out E D' D /\ out E F' F /\
 Cong_3 A' B C' D' E F') -> Conga A B C D E F.
Proof.
    intros.
    unfold Conga.
    ex_and H A'.
    ex_and H0 C'.
    ex_and H D'.
    ex_and H0 F'.
    prolong B A A0 E D.
    prolong B C C0 E F.
    prolong E D D0 B A.
    prolong E F F0 B C.
    assert(HH0:=H0).
    assert(HH1:=H1).
    assert(HH2:=H2).
    assert(HH:=H).
    unfold out in HH.
    unfold out in HH0.
    unfold out in HH1.
    unfold out in HH2.
    spliter.
    repeat split;try assumption.
    repeat split;try assumption.
    exists A0.
    exists C0.
    exists D0.
    exists F0.
    repeat split; try (assumption).
    unfold Cong_3 in H3.
    spliter.
    assert(Cong B A0 E D0 /\ Cong A' A0 D' D0).
      eapply l11_aux.
        apply l6_6.
        apply H.
        apply l6_6.
        apply H1.
        apply cong_commutativity.
        assumption.
        assumption.
        assumption.
        assumption.
      assumption.
    assert(Cong B C0 E F0 /\ Cong C' C0 F' F0).
      eapply l11_aux.
        apply l6_6.
        apply H0.
        apply l6_6.
        apply H2.
        assumption.
        assumption.
        assumption.
        assumption.
      assumption.
    spliter.
    assert (Cong_3 B A' A0 E D' D0).
      repeat split.
        apply cong_commutativity.
        assumption.
        assumption.
      assumption.
    assert (Cong_3 B C' C0 E F' F0).
      repeat split.
        assumption.
        assumption.
      assumption.
    assert (Cong C0 A' F0 D').
      eapply l4_16.
        unfold FSC.
        split.
          2:split.
            2:apply H31.
          apply out_col in H0.
          apply bet_col in H6.
          ColR.
        split.
          Cong.
        Cong.
      auto.
    eapply l4_16.
      unfold FSC.
      split.
        2:split.
          2:apply H30.
        assert_cols.
        ColR.
      split.
        assumption.
      Cong.
    auto.
Qed.

Lemma out_cong_cong : forall B A A0 E D D0,
 out B A A0 -> out E D D0 ->
 Cong B A E D -> Cong B A0 E D0 ->
 Cong A A0 D D0.
Proof.
    intros.
    unfold out in H.
    spliter.
    induction H4.
      assert (Bet E D D0).
        eapply cong_preserves_bet.
          2:apply H1.
          2:apply H2.
          assumption.
        assumption.
      apply cong_commutativity.
      eapply l4_3.
        apply between_symmetry.
        apply H4.
        apply between_symmetry.
        apply H5.
        Cong.
      Cong.
    assert (Bet E D0 D).
      eapply cong_preserves_bet.
        2:apply H2.
        2:apply H1.
        assumption.
      apply l6_6.
      assumption.
    eapply l4_3;eBetween;Cong.
Qed.

Lemma l11_4_1 : forall A B C D E F,
  Conga A B C D E F -> A<>B /\ C<>B /\ D<>E /\ F<>E /\
  (forall A' C' D' F', out B A' A /\ out B C' C /\ out E D' D /\ out E F' F /\
  Cong B A' E D' /\ Cong B C' E F' -> Cong A' C' D' F').
Proof.
    intros.
    assert (HH:=H).
    apply l11_3 in HH.
    unfold Conga in H.
    spliter.
    repeat split; try assumption.
    clear H3.
    intros.
    ex_and HH A0.
    ex_and H4 C0.
    ex_and H10 D0.
    ex_and H4 F0.
    unfold Cong_3 in H13.
    spliter.
    assert (out B A' A0).
      eapply l6_7.
        apply H3.
      apply l6_6.
      assumption.
    assert (out E D' D0).
      eapply l6_7.
        apply H6.
      apply l6_6.
      assumption.
    assert(Cong A' A0 D' D0).
      eapply out_cong_cong.
        apply H16.
        apply H17.
        assumption.
      Cong.
    assert (Cong A' C0 D' F0).
      eapply (l4_16 B A0 A' C0 E D0 D' F0).
        unfold FSC.
        repeat split.
          assert_cols;Col.
          Cong.
          assumption.
          Cong.
          assumption.
        assumption.
      intro.
      subst A0.
      unfold out in H4.
      spliter.
      absurde.
    assert (out B C' C0).
      eapply l6_7.
        apply H5.
      assumption.
    assert (out E F' F0).
      eapply l6_7.
        apply H7.
      assumption.
    assert(Cong C' C0 F' F0).
      eapply out_cong_cong.
        3:apply H9.
        assumption.
        assumption.
      assumption.
    apply cong_commutativity.
    eapply (l4_16 B C0 C' A' E F0 F' D').
      unfold FSC.
      repeat split.
        apply out_col.
        apply l6_6.
        assumption.
        assumption.
        assumption.
        Cong.
        assumption.
      Cong.
    intro.
    subst C0.
    unfold out in H10.
    spliter.
    absurde.
Qed.



Lemma l11_4_2 : forall A B C D E F,
  (A<>B /\ C<>B /\ D<>E /\ F<>E /\
  (forall A' C' D' F', out B A' A /\ out B C' C /\ out E D' D /\ out E F' F /\
  Cong B A' E D' /\ Cong B C' E F' -> Cong A' C' D' F')) ->  Conga A B C D E F.
Proof.
    intros.
    spliter.
    eapply l11_3_bis.
    prolong B A A' E D.
    prolong B C C' E F.
    prolong E D D' B A.
    prolong E F F' B C.
    exists A'.
    exists C'.
    exists D'.
    exists F'.
    assert(Cong A' B D' E).
      apply cong_right_commutativity.
      eapply l2_11.
        apply between_symmetry.
        apply H4.
        apply H8.
        Cong.
      Cong.
    assert (Cong B C' E F').
      apply cong_right_commutativity.
      eapply l2_11.
        apply H6.
        apply between_symmetry.
        apply H10.
        Cong.
      Cong.
    assert(out B A' A /\out B C' C /\ out E D' D /\ out E F' F).
      repeat split.
        intro.
        subst A'.
        treat_equalities;intuition.
        (*apply between_identity in H4.
        subst B.
        absurde.
        *)
        assumption.
        right.
        assumption.
        intro.
        subst C'.
        apply between_identity in H6.
        subst C.
        absurde.
        assumption.
        right.
        assumption.
        intro.
        subst D'.
        apply between_identity in H8.
        subst E.
        absurde.
        assumption.
        right.
        assumption.
        intro.
        subst F'.
        apply between_identity in H10.
        subst F.
        absurde.
        assumption.
      right.
      assumption.
    spliter.
    split.
      assumption.
    split.
      assumption.
    split.
      assumption.
    split.
      assumption.
    repeat split.
      assumption.
      2:assumption.
    apply H3.
    split.
      assumption.
    split.
      assumption.
    split.
      assumption.
    split.
      assumption.
    split.
      Cong.
    assumption.
Qed.

Lemma conga_refl : forall A B C, A <> B -> C <> B -> Conga A B C A B C.
Proof.
    intros.
    apply l11_3_bis.
    exists A.
    exists C.
    exists A.
    exists C.
    repeat split; try assumption; Between;Cong.
Qed.

Lemma conga_sym : forall A B C A' B' C', Conga A B C A' B' C' -> Conga A' B' C' A B C.
Proof.
    unfold Conga.
    intros.
    spliter.
    ex_and H3 A0.
    ex_and H4 C0.
    ex_and H3 D0.
    ex_and H4 F0.
    repeat split; try assumption.
    exists D0.
    exists F0.
    exists A0.
    exists C0.
    repeat split; try assumption;Cong.
Qed.

Lemma out_conga :
 forall A B C A' B' C' A0 C0 A1 C1,
 Conga A B C A' B' C' ->
 out B A A0 ->
 out B C C0 ->
 out B' A' A1 ->
 out B' C' C1 ->
 Conga A0 B C0 A1 B' C1.
Proof.
    intros.
    apply l11_4_1 in H.
    spliter.
    apply l11_4_2.
    repeat split.
      intro.
      subst A0.
      unfold out in H0.
      spliter.
      absurde.
      intro.
      subst C0.
      unfold out in H1.
      spliter.
      absurde.
      intro.
      subst A1.
      unfold out in H2.
      spliter.
      absurde.
      intro.
      subst C1.
      unfold out in H3.
      spliter.
      absurde.
    intros.
    spliter.
    apply H7.
    repeat split.
      intro.
      subst A'0.
      unfold out in H8.
      spliter.
      absurde.
      assumption.
      eapply l6_7.
        apply H8.
      apply l6_6.
      assumption.
      intro.
      subst C'0.
      unfold out in H9.
      spliter.
      absurde.
      assumption.
      eapply l6_7.
        apply H9.
      apply l6_6.
      assumption.
      intro.
      subst D'.
      unfold out in H10.
      spliter.
      absurde.
      assumption.
      eapply l6_7.
        apply H10.
      apply l6_6.
      assumption.
      intro.
      subst F'.
      unfold out in H11.
      spliter.
      absurde.
      assumption.
      eapply l6_7.
        apply H11.
      apply l6_6.
      assumption.
      assumption.
    assumption.
Qed.

Lemma cong3_diff : forall A B C A' B' C',
 A<>B -> Cong_3 A B C A' B' C' -> A' <> B'.
Proof.
unfold Cong_3 in *.
intros.
spliter.
assert_diffs.
auto.
Qed.

Lemma cong3_diff2: forall A B C A' B' C',
 B<>C -> Cong_3 A B C A' B' C' -> B' <> C'.
Proof.
unfold Cong_3 in *.
intros.
spliter.
assert_diffs.
auto.
Qed.
 

Lemma cong3_conga : forall A B C A' B' C',
 A <> B -> C <> B ->
 Cong_3 A B C A' B' C' ->
 Conga  A B C A' B' C'.
Proof.
    intros.
    assert (A' <> B') by (eauto using cong3_diff).
    assert (B' <> C') by (eauto using cong3_diff2).
    apply (l11_3_bis A B C A' B' C').
    exists A. exists C. exists A'. exists C'.
    intuition (auto using out_trivial).
Qed.
  
Lemma cong3_conga2 : forall A B C A' B' C' A'' B'' C'',
  Cong_3 A B C A' B' C' ->
  Conga A B C A'' B'' C'' ->
  Conga A' B' C' A'' B'' C''.
Proof.
    intros.
    unfold Conga in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A2.
    ex_and H5 C2.
    unfold Cong_3 in H.
    spliter.
    unfold Conga.
    repeat split.
      intro.
      subst B'.
      apply cong_identity in H.
      subst B.
      absurde.
      intro.
      subst C'.
      apply cong_identity in H14.
      subst C.
      absurde.
      assumption.
      assumption.
    prolong B' A' A1 B'' A''.
    prolong B' C' C1 B'' C''.
    exists A1.
    exists C1.
    exists A2.
    exists C2.
    repeat split; try assumption.
      eapply cong_transitivity.
        apply H9.
      Cong.
      eapply cong_transitivity.
        apply H11.
      assumption.
    assert (Cong A A0 A' A1).
      eapply cong_transitivity.
        apply H5.
      Cong.
    assert(Cong B A0 B' A1).
      eapply l2_11.
        apply H4.
        apply H15.
        Cong.
      assumption.
    assert (Cong C C0 C' C1).
      eapply cong_transitivity.
        apply H7.
      Cong.
    assert(Cong B C0 B' C1).
      eapply l2_11.
        apply H6.
        apply H17.
        assumption.
      assumption.
    assert(FSC B A A0 C B' A' A1 C').
      unfold FSC.
      repeat split; try assumption.
        unfold Col.
        left.
        assumption.
      Cong.
    assert(Cong A0 C A1 C').
      eapply l4_16.
        apply H23.
      auto.
    apply cong_commutativity.
    assert(Cong C0 A0 C1 A1).
      eapply (l4_16 B C C0 A0 B' C' C1 A1).
        unfold FSC.
        assert_cols.
        repeat split;Cong.
      auto.
    eCong.
Qed.

Lemma conga_diff1 : forall A B C A' B' C', Conga A B C A' B' C' -> A <> B.
Proof.
    intros.
    unfold Conga in H.
    spliter.
    assumption.
Qed.

Lemma conga_diff2 : forall A B C A' B' C', Conga A B C A' B' C' -> C <> B.
Proof.
    intros.
    unfold Conga in H.
    spliter.
    assumption.
Qed.

Lemma conga_trans : forall A B C A' B' C' A'' B'' C'',
  Conga A B C A' B' C' -> Conga A' B' C' A'' B'' C'' ->
  Conga A B C A'' B'' C''.
Proof.
    intros.
    assert (HH:=H).
    unfold Conga in H.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert(A'' <> B'' /\ C'' <> B'').
      unfold Conga in H0.
      spliter.
      split; assumption.
    spliter.
    assert(A0 <> B).
      intro.
      subst A0.
      apply between_identity in H4.
      subst A.
      absurde.
    assert(C0 <> B).
      intro.
      subst C0.
      apply between_identity in H6.
      subst C.
      absurde.
    assert(A1 <> B').
      intro.
      subst A1.
      apply between_identity in H8.
      subst A'.
      absurde.
    assert(C1 <> B').
      intro.
      subst C1.
      apply between_identity in H10.
      subst C'.
      absurde.
    assert(Conga A1 B' C1 A'' B'' C'').
      eapply out_conga.
        apply H0.
        repeat split.
          assumption.
          assumption.
        left.
        assumption.
        repeat split.
          assumption.
          assumption.
        left.
        assumption.
        apply out_trivial.
        assumption.
      apply out_trivial.
      assumption.
    assert (Conga A0 B C0 A' B' C').
      eapply out_conga.
        apply HH.
        apply bet_out.
          assumption.
          assumption.
        assumption.
        apply bet_out.
          assumption.
          assumption.
        assumption.
        apply out_trivial.
        assumption.
      apply out_trivial.
      assumption.
    assert (Cong B A0 B' A1).
      apply cong_right_commutativity.
      eapply l2_11.
        apply H4.
        apply between_symmetry.
        apply H8.
        apply cong_right_commutativity.
        apply cong_symmetry.
        assumption.
      apply cong_right_commutativity.
      assumption.
    assert (Cong B C0 B' C1).
      apply cong_right_commutativity.
      eapply l2_11.
        apply H6.
        apply between_symmetry.
        apply H10.
        apply cong_right_commutativity.
        apply cong_symmetry.
        assumption.
      apply cong_right_commutativity.
      assumption.
    assert (Cong A0 C0 A1 C1).
      apply (l11_4_1) in H20.
      spliter.
      apply H26.
      repeat split.
        assumption.
        assumption.
        left.
        apply between_trivial.
        assumption.
        assumption.
        left.
        apply between_trivial.
        assumption.
        assumption.
        right.
        assumption.
        assumption.
        assumption.
        right.
        assumption.
        assumption.
      assumption.
    assert (Cong_3 A0 B C0 A1 B' C1).
      repeat split.
        apply cong_commutativity.
        assumption.
        assumption.
      assumption.
    apply cong3_symmetry in H24.
    assert( Conga A0 B C0 A'' B'' C'').
      eapply cong3_conga2.
        apply H24.
      assumption.
    eapply out_conga.
      apply H25.
      repeat split.
        assumption.
        assumption.
      right.
      assumption.
      repeat split.
        assumption.
        assumption.
      right.
      assumption.
      apply out_trivial.
      assumption.
    apply out_trivial.
    assumption.
Qed.

Lemma conga_pseudo_refl : forall A B C,
 A <> B -> C <> B -> Conga A B C C B A.
Proof.
    intros.
    unfold Conga.
    repeat split; try assumption.
    prolong B A A' B C.
    prolong B C C' B A.
    prolong B A A'' B C.
    prolong B C C'' B A.
    exists A'.
    exists C'.
    exists C''.
    exists A''.
    repeat split; try assumption.
    assert (A' = A'') by (eauto using (construction_unicity B A)).
    subst A''.
    assert (C' = C'') by (eauto using (construction_unicity B C)).
    subst C''.
    Cong.
Qed.

Lemma conga_trivial_1 : forall A B C D,
  A<>B -> C<>D -> Conga A B A C D C.
Proof.
    intros.
    unfold Conga.
    repeat split; try assumption.
    prolong B A A' D C.
    prolong D C C' B A.
    exists A'.
    exists A'.
    exists C'.
    exists C'.
    repeat split; try assumption.
    apply cong_trivial_identity.
Qed.

Lemma l11_10 : forall A B C D E F A' C' D' F',
  Conga A B C D E F -> out B A' A -> out B C' C -> out E D' D -> out E F' F ->
  Conga A' B C' D' E F'.
Proof.
    intros.
    eapply (out_conga A B C D E F); auto using l6_6.
Qed.

Lemma l11_13 : forall A B C D E F A' D',
 Conga A B C D E F -> Bet A B A' -> A'<> B -> Bet D E D' -> D'<> E -> Conga A' B C D' E F.
Proof.
    intros.
    unfold Conga in H.
    spliter.
    ex_and H7 A''.
    ex_and H8 C''.
    ex_and H7 D''.
    ex_and H8 F''.
    prolong B A' A0 E D'.
    prolong E D' D0 B A'.
    unfold Conga.
    repeat split; try assumption.
    exists A0.
    exists C''.
    exists D0.
    exists F''.
    repeat split; try assumption.
    eapply (five_segments_with_def A'' B A0 C'' D'' E D0 F'').
      unfold OFSC.
      repeat split.
        eapply outer_transitivity_between2.
          apply between_symmetry.
          apply H7.
          eapply outer_transitivity_between.
            apply H0.
            assumption.
          auto.
        assumption.
        eapply outer_transitivity_between2.
          apply between_symmetry.
          apply H11.
          eapply outer_transitivity_between.
            apply H2.
            assumption.
          auto.
        assumption.
        apply cong_left_commutativity.
        eapply l2_11.
          apply H7.
          apply between_symmetry.
          apply H11.
          Cong.
        Cong.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H16.
          apply between_symmetry.
          apply H18.
          apply cong_symmetry.
          Cong.
        Cong.
        assumption.
      apply cong_right_commutativity.
      eapply l2_11 with C F;Between;Cong.
    intro.
    subst A''.
    apply between_identity in H7.
    subst A.
    absurde.
Qed.

Lemma conga_right_comm : forall A B C D E F, Conga A B C D E F -> Conga A B C F E D.
Proof.
    intros.
    eapply conga_trans.
      apply H.
    unfold Conga in H.
    spliter.
    apply conga_pseudo_refl.
      assumption.
    assumption.
Qed.

Lemma conga_left_comm : forall A B C D E F, Conga A B C D E F -> Conga C B A D E F.
Proof.
    intros.
    apply conga_sym.
    eapply conga_trans.
      apply conga_sym.
      apply H.
    unfold Conga in H.
    spliter.
    apply conga_pseudo_refl.
      assumption.
    assumption.
Qed.

Lemma conga_comm : forall A B C D E F, Conga A B C D E F -> Conga C B A F E D.
Proof.
    intros.
    apply conga_left_comm.
    apply conga_right_comm.
    assumption.
Qed.

Definition Distincts := fun A B C : Tpoint => A<>B /\ A<>C /\ B<>C.

Lemma conga_line : forall A B C A' B' C',
 Distincts A B C -> Distincts A' B' C' -> Bet A B C -> Bet A' B' C' ->
 Conga A B C A' B' C'.
Proof.
    intros.
    unfold Distincts in *.
    spliter.
    prolong B C C0 B' C'.
    prolong B' C' C1 B C.
    prolong B A A0 B' A'.
    prolong B' A' A1 B A.
    unfold Conga.
    repeat split; try assumption.
      auto.
      auto.
    exists A0.
    exists C0.
    exists A1.
    exists C1.
    repeat split; try assumption.
    apply (l2_11 A0 B C0 A1 B' C1).
      eapply outer_transitivity_between2.
        apply between_symmetry.
        apply H11.
        eapply outer_transitivity_between.
          apply H1.
          assumption.
        assumption.
      assumption.
      eapply outer_transitivity_between2.
        apply between_symmetry.
        apply H13.
        eapply outer_transitivity_between.
          apply H2.
          assumption.
        assumption.
      assumption.
      apply cong_right_commutativity.
      eapply l2_11.
        apply between_symmetry.
        apply H11.
        apply H13.
        apply cong_left_commutativity.
        assumption.
      apply cong_symmetry.
      apply cong_right_commutativity.
      assumption.
    apply cong_right_commutativity.
    eapply l2_11.
      apply H7.
      apply between_symmetry.
      apply H9.
      apply cong_symmetry.
      apply cong_left_commutativity.
      assumption.
    apply cong_right_commutativity.
    assumption.
Qed.


Lemma l11_14 : forall A B C A' C',
 Bet A B A' -> Distincts A B A' -> Bet C B C' -> Distincts C B C' ->
 Conga A B C A' B C'.
Proof.
    unfold Distincts.
    intros.
    spliter.
    assert (Conga A' B C  C' B A).
      eapply l11_13.
        eapply conga_pseudo_refl.
          assumption.
        assumption.
        assumption.
        auto.
        assumption.
      auto.
    eapply l11_13.
      apply conga_right_comm.
      apply H7.
      apply between_symmetry.
      assumption.
      assumption.
      assumption.
    auto.
Qed.


Lemma l11_16 : forall A B C A' B' C',
 Per A B C    -> A <>B  -> C <>B ->
 Per A' B' C' -> A'<>B' -> C'<>B'->
 Conga A B C A' B' C'.
Proof.
    intros.
    prolong B C C0 B' C'.
    prolong B' C' C1 B C.
    prolong B A A0 B' A'.
    prolong B' A' A1 B A.
    unfold Conga.
    repeat split; try assumption.
    exists A0.
    exists C0.
    exists A1.
    exists C1.
    repeat split; try assumption.
    eapply (l10_12 A0 B C0 A1 B' C1).
      eapply (per_col _ _ C).
        intro; subst.
        auto.
        apply l8_2.
        eapply (per_col _ _ A).
          auto.
          apply l8_2.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
      eapply (per_col _ _ C').
        auto.
        apply l8_2.
        eapply (per_col _ _ A').
          auto.
          apply l8_2.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
      apply cong_right_commutativity.
      eapply l2_11.
        apply between_symmetry.
        apply H9.
        apply H11.
        apply cong_left_commutativity.
        assumption.
      apply cong_symmetry.
      apply cong_right_commutativity.
      assumption.
    apply cong_right_commutativity.
    eapply l2_11.
      apply H5.
      apply between_symmetry.
      apply H7.
      apply cong_symmetry.
      apply cong_left_commutativity.
      assumption.
    apply cong_right_commutativity.
    assumption.
Qed.


Lemma l11_17 : forall A B C A' B' C',
  Per A B C -> Conga A B C A' B' C' -> Per A' B' C'.
Proof.
    intros.
    unfold Conga in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert (Per A0 B C0).
      eapply (per_col _ _ C).
        auto.
        apply l8_2.
        eapply (per_col _ _ A).
          auto.
          apply l8_2.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
    assert(Per A1 B' C1).
      eapply l8_10.
        apply H13.
      repeat split.
        apply cong_right_commutativity.
        eapply l2_11.
          apply between_symmetry.
          apply H4.
          apply H8.
          apply cong_left_commutativity.
          assumption.
        apply cong_symmetry.
        apply cong_right_commutativity.
        assumption.
        assumption.
      apply cong_right_commutativity.
      eapply l2_11.
        apply H6.
        apply between_symmetry.
        apply H10.
        apply cong_left_commutativity.
        apply cong_symmetry.
        apply cong_commutativity.
        assumption.
      apply cong_right_commutativity.
      assumption.
    eapply (per_col _ _ C1).
      intro.
      subst C1.
      apply between_identity in H10.
      subst C'.
      absurde.
      apply l8_2.
      eapply (per_col _ _ A1).
        intro.
        subst A1.
        apply between_identity in H8.
        subst A'.
        absurde.
        apply l8_2.
        assumption.
      unfold Col.
      right; left.
      apply between_symmetry.
      assumption.
    unfold Col.
    right; left.
    apply between_symmetry.
    assumption.
Qed.

Lemma l11_18_1 : forall A B C D,
  Bet C B D -> Distincts B C D -> A<>B -> Per A B C -> Conga A B C A B D.
Proof.
    intros.
    unfold Distincts in H0.
    spliter.
    assert (Per A B D).
      eapply per_col.
        apply H0.
        assumption.
      unfold Col.
      right; right.
      apply between_symmetry.
      assumption.
    eapply l11_16; try assumption.
      auto.
    auto.
Qed.

Lemma l11_18_2 : forall A B C D,
  Bet C B D -> Distincts B C D -> A<>B -> Conga A B C A B D -> Per A B C.
Proof.
    intros.
    unfold Conga in H2.
    spliter.
    ex_and H6 A0.
    ex_and H7 C0.
    ex_and H6 A1.
    ex_and H7 D0.
    assert( A0 = A1).
      eapply construction_unicity.
        2: apply H6.
        auto.
        apply H7.
        assumption.
      assumption.
    subst A1.
    assert(Per A0 B C0).
      unfold Per.
      exists D0.
      repeat split.
        eapply outer_transitivity_between2.
          apply between_symmetry.
          apply H8.
          eapply outer_transitivity_between.
            apply H.
            assumption.
          auto.
        assumption.
        eapply l2_11.
          apply between_symmetry.
          apply H8.
          apply H12.
          apply cong_left_commutativity.
          assumption.
        apply cong_symmetry.
        apply cong_right_commutativity.
        assumption.
      assumption.
    eapply (per_col _ _ C0).
      intro.
      subst C0.
      apply between_identity in H8.
      subst C.
      absurde.
      apply l8_2.
      eapply (per_col _ _ A0).
        intro.
        subst A0.
        apply between_identity in H10.
        subst A.
        absurde.
        apply l8_2.
        assumption.
      unfold Col.
      right; left.
      apply between_symmetry.
      assumption.
    unfold Col.
    right; left.
    apply between_symmetry.
    assumption.
Qed.

Lemma not_bet_out : forall A B C,
 A <> B -> C <> B -> Col A B C -> ~Bet A B C ->
 out B A C.
Proof.
    intros.
    unfold out.
    repeat split.
      assumption.
      assumption.
    unfold Col in H1.
    induction H1.
      contradiction.
    induction H1.
      right.
      assumption.
    left.
    apply between_symmetry.
    assumption.
Qed.



Lemma cong3_preserves_out : forall A B C A' B' C',
  out A B C -> Cong_3 A B C A' B' C' -> out A' B' C'.
Proof.
    intros.
    unfold out in *.
    spliter.
    assert(HH:=H0).
    unfold Cong_3 in H0.
    spliter.
    repeat split.
      intro.
      subst A'.
      apply cong_identity in H0.
      subst A.
      absurde.
      intro.
      subst A'.
      apply cong_identity in H3.
      subst A.
      absurde.
    induction H2.
      left.
      eapply l4_6.
        2:apply HH.
      assumption.
    right.
    eapply l4_6.
      apply H2.
    unfold Cong_3.
    repeat split.
      assumption.
      assumption.
    apply cong_commutativity.
    assumption.
Qed.

Lemma l11_21_a : forall A B C A' B' C', out B A C -> Conga A B C A' B' C' -> out B' A' C'.
Proof.
    intros.
    unfold Conga in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert (out B A0 C0).
      unfold out.
      repeat split.
        intro.
        subst A0.
        apply between_identity in H4.
        subst A.
        absurde.
        intro.
        subst C0.
        apply between_identity in H6.
        subst C.
        absurde.
      unfold out in H.
      spliter.
      induction H14.
        eapply l5_1.
          2: apply H4.
          auto.
        eapply between_exchange4.
          apply H14.
        assumption.
      eapply l5_1.
        3: apply H6.
        auto.
      eapply between_exchange4.
        apply H14.
      assumption.
    assert (out B' A1 C1).
      eapply cong3_preserves_out.
        apply H13.
      unfold Cong_3.
      repeat split.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H4.
          apply between_symmetry.
          apply H8.
          apply cong_symmetry.
          apply cong_left_commutativity.
          assumption.
        apply cong_right_commutativity.
        assumption; apply H8.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H6.
          apply between_symmetry.
          apply H10.
          apply cong_symmetry.
          apply cong_left_commutativity.
          assumption.
        apply cong_right_commutativity.
        assumption.
      assumption.
    eapply l6_7.
      apply l6_6.
      eapply l6_7.
        apply H14.
      eapply l6_7.
        apply l6_6.
        apply H14.
      unfold out.
      repeat split.
        intro.
        subst A1.
        unfold out in H14.
        spliter.
        absurde.
        assumption.
      right.
      assumption.
    eapply l6_7.
      apply H14.
    unfold out.
    repeat split.
      intro.
      subst C1.
      unfold out in H14.
      spliter.
      absurde.
      assumption.
    right.
    assumption.
Qed.

Lemma l11_21_b : forall A B C A' B' C',
 out B A C -> out B' A' C' -> Conga A B C A' B' C'.
Proof.
    intros.
    prolong A B A0 A B.
    prolong C B C0 B C.
    prolong A' B' A1 A' B'.
    prolong C' B' C1 B' C'.
    eapply l11_13.
      eapply conga_line.
        3: apply between_symmetry.
        3: apply H3.
        3: apply between_symmetry.
        3: apply H7.
        repeat split.
          intro.
          subst C0.
          apply cong_symmetry in H4.
          apply cong_identity in H4.
          subst C.
          unfold out in H.
          spliter.
          absurde.
          intro.
          subst C0.
          apply between_identity in H3.
          subst C.
          unfold out in H.
          spliter.
          absurde.
        unfold out in H.
        spliter.
        auto.
      repeat split.
        intro.
        subst C1.
        apply cong_symmetry in H8.
        apply cong_identity in H8.
        subst C'.
        unfold out in H0.
        spliter.
        absurde.
        intro.
        subst C1.
        apply between_identity in H7.
        subst C'.
        unfold out in H0.
        spliter.
        absurde.
      unfold out in H0.
      spliter.
      auto.
      unfold out in H.
      spliter.
      induction H10.
        eapply between_inner_transitivity.
          apply between_symmetry.
          apply H3.
        assumption.
      eapply outer_transitivity_between.
        apply between_symmetry.
        apply H3.
        assumption.
      auto.
      unfold out in H.
      spliter.
      assumption.
      unfold out in H0.
      spliter.
      induction H10.
        eapply between_inner_transitivity.
          apply between_symmetry.
          apply H7.
        assumption.
      eapply outer_transitivity_between.
        apply between_symmetry.
        apply H7.
        assumption.
      auto.
    unfold out in H0.
    spliter.
    assumption.
Qed.

Lemma l11_22_aux : forall A B C C',
 Conga A B C A B C' -> out B C C' \/ two_sides A B C C'.
Proof.
    intros.
    unfold Conga in H.
    spliter.
    ex_and H3 A0.
    ex_and H4 C0.
    ex_and H3 A1.
    ex_and H4 C1.
    assert (A0=A1).
      eapply construction_unicity.
        3:apply H4.
        2:apply H3.
        auto.
        assumption.
      assumption.
    subst A1.
    induction (eq_dec_points C0 C1).
      subst C1.
      left.
      unfold out.
      repeat split; try assumption.
      eapply l5_3.
        apply H5.
      assumption.
    right.
    assert(exists M, is_midpoint M C0 C1).
      apply midpoint_existence.
    ex_and H13 M.
    assert(Cong B C0 B C1).
      apply cong_right_commutativity.
      eapply l2_11.
        apply H5.
        apply between_symmetry.
        apply H9.
        apply cong_symmetry.
        apply cong_left_commutativity.
        assumption.
      apply cong_right_commutativity.
      assumption.
    assert(Per A0 M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert(Per B M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert(Per A0 M C1).
      unfold Per.
      exists C0.
      split.
        apply l7_2.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Per B M C1).
      unfold Per.
      exists C0.
      split.
        apply l7_2.
        assumption.
      apply cong_symmetry.
      assumption.
    assert (B <> A0).
      intro.
      subst A0.
      apply between_identity in H7.
      subst A.
      absurde.
    assert (Cong A C0 A C1).
      eapply (l4_2 B A A0 C0 B A A0 C1).
      unfold IFSC.
      repeat split; try assumption.
        apply cong_reflexivity.
      apply cong_reflexivity.
    assert (Per A M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert (Per A M C1).
      unfold Per.
      exists C0.
      split.
        apply l7_2.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Col B A M).
      eapply per_per_col.
        apply H16.
        intro.
        subst M.
        apply is_midpoint_id in H14.
        contradiction.
      assumption.
    (************)
    induction(eq_dec_points B M).
      subst M.
      assert(~Col A B C).
        eapply per_not_col.
          assumption.
          auto.
        eapply per_col.
          2:apply H22.
          intro.
          subst C1.
          apply l7_2 in H14.
          apply is_midpoint_id in H14.
          subst C0.
          absurde.
        assert(Bet C B C1).
          eapply between_exchange3.
            apply between_symmetry.
            apply H5.
          apply midpoint_bet.
          assumption.
        unfold Col.
        right; right.
        assumption.
      assert(~Col A B C').
        eapply per_not_col.
          assumption.
          auto.
        eapply per_col.
          2:apply H22.
          intro.
          subst C1.
          apply l7_2 in H14.
          apply is_midpoint_id in H14.
          subst C0.
          absurde.
        assert(Bet C' B C0).
          eapply between_exchange3.
            apply between_symmetry.
            apply H9.
          apply midpoint_bet.
          apply l7_2.
          assumption.
        unfold Col.
        right; left.
        apply between_symmetry.
        assumption.
      unfold two_sides.
      repeat split.
        assumption.
        Col.
        Col.
      exists B.
      split.
        Col.
      apply between_symmetry.
      eapply between_exchange3.
        apply between_symmetry.
        apply H9.
      apply between_symmetry.
      eapply between_exchange3.
        apply between_symmetry.
        apply H5.
      apply midpoint_bet.
      assumption.
    (***********)
    assert(two_sides B M C0 C1).
      unfold two_sides.
      repeat split.
        assumption.
        intro.
        apply per_not_col in H16.
          apply H16.
          apply col_permutation_1.
          assumption.
          assumption.
        intro.
        subst C0.
        apply is_midpoint_id in H14.
        subst C1.
        absurde.
        intro.
        apply per_not_col in H18.
          apply H18.
          Col.
          assumption.
        intro.
        subst C1.
        apply l7_2 in H14.
        apply is_midpoint_id in H14.
        subst C0.
        absurde.
      exists M.
      split.
        apply col_trivial_3.
      apply midpoint_bet.
      assumption.
    apply (col_two_sides _ _ A) in H25.
      apply invert_two_sides in H25.
      (*************************)
      assert(two_sides A B C C1).
        eapply l9_5.
          apply H25.
          apply col_trivial_3.
        unfold out.
        repeat split.
          intro.
          subst C0.
          apply cong_symmetry in H13.
          apply cong_identity in H13.
          subst C1.
          absurde.
          assumption.
        right.
        assumption.
      apply l9_2.
      eapply l9_5.
        apply l9_2.
        apply H26.
        apply col_trivial_3.
      unfold out.
      repeat split.
        intro.
        subst C1.
        apply cong_identity in H13.
        subst C0.
        absurde.
        intro.
        subst C'.
        apply cong_identity in H6.
        subst C0.
        absurde.
      right.
      assumption.
      Col.
    auto.
Qed.

Lemma per_cong_mid : forall A B C H,
 B <> C -> Bet A B C -> Cong A H C H -> Per H B C ->
 is_midpoint B A C.
Proof.
    intros.
    induction (eq_dec_points H B).
      subst H.
      unfold is_midpoint.
      split.
        assumption.
      apply cong_right_commutativity.
      assumption.
    assert(Per C B H).
      apply l8_2.
      assumption.
    assert (Per H B A).
      eapply per_col.
        apply H0.
        assumption.
      unfold Col.
      right; right.
      assumption.
    assert (Per A B H).
      apply l8_2.
      assumption.
    unfold Per in *.
    ex_and H3 C'.
    ex_and H5 H'.
    ex_and H6 A'.
    ex_and H7 H''.
    assert (H' = H'').
      eapply construction_unicity.
        2: apply  midpoint_bet.
        2:apply H5.
        assumption.
        apply cong_commutativity.
        apply midpoint_cong.
        apply l7_2.
        apply H5.
        apply midpoint_bet.
        assumption.
      apply cong_commutativity.
      apply midpoint_cong.
      apply l7_2.
      assumption.
    subst H''.
    assert(IFSC H B H' A H B H' C).
      repeat split.
        apply midpoint_bet.
        assumption.
        apply midpoint_bet.
        assumption.
        apply cong_reflexivity.
        apply cong_reflexivity.
        apply cong_commutativity.
        assumption.
      apply cong_commutativity.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H11.
      eapply cong_transitivity.
        apply H2.
      assumption.
    eapply l4_2 in H12.
    unfold is_midpoint.
    split.
      assumption.
    apply cong_left_commutativity.
    assumption.
Qed.

Lemma cong2_conga_cong : forall A B C A' B' C',
 Conga A B C A' B' C' -> Cong A B A' B' -> Cong B C B' C' ->
 Cong A C A' C'.
Proof.
    intros.
    unfold Conga in H.
    spliter.
    ex_and H5 A0.
    ex_and H6 C0.
    ex_and H5 A1.
    ex_and H6 C1.
    assert(Cong A C0 A' C1).
      eapply (l4_2 B A A0 C0 B' A' A1 C1).
      repeat split; try assumption.
        eapply l2_11.
          apply H5.
          apply H9.
          apply cong_commutativity.
          assumption.
        eapply cong_transitivity.
          apply H6.
        apply cong_commutativity.
        apply cong_symmetry.
        eapply cong_transitivity.
          2: apply H0.
        apply cong_commutativity.
        assumption.
        eapply cong_transitivity.
          apply H6.
        apply cong_commutativity.
        apply cong_symmetry.
        eapply cong_transitivity.
          2: apply H0.
        apply cong_commutativity.
        assumption.
      eapply cong_transitivity.
        eapply l2_11.
          apply H7.
          apply H11.
          assumption.
        eapply cong_transitivity.
          apply H8.
        apply cong_symmetry.
        eapply cong_transitivity.
          apply H12.
        assumption.
      apply cong_reflexivity.
    apply cong_commutativity.
    eapply (l4_2 B C C0 A B' C' C1 A').
    repeat split; try assumption.
      eapply l2_11.
        apply H7.
        apply H11.
        assumption.
      eapply cong_transitivity.
        apply H8.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H1.
      apply cong_symmetry.
      assumption.
      eapply cong_transitivity.
        apply H8.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H1.
      apply cong_symmetry.
      assumption.
      apply cong_commutativity.
      assumption.
    apply cong_commutativity.
    assumption.
Qed.



Lemma segment_construction_3 : forall A B X Y, A <> B -> X <> Y -> exists C, out A B C /\ Cong A C X Y.
Proof.
    intros.
    assert(exists C ,(Bet A B C \/ Bet A C B) /\ Cong A C X Y).
      apply segment_construction_2.
      auto.
    ex_and H1 C.
    exists C.
    repeat split.
      auto.
      intro.
      subst C.
      apply cong_symmetry in H2.
      apply cong_identity in H2.
      contradiction.
      assumption.
    assumption.
Qed.

Lemma ex_per_cong : forall A B C D X Y,
 A <> B -> X <> Y -> Col A B C -> ~Col A B D ->
 exists P, Per P C A /\ Cong P C X Y /\ one_side A B P D.
Proof.
    intros.
    assert (exists D', two_sides A B D D').
      apply l9_10.
        assumption.
      intro.
      apply H2.
      apply col_permutation_1.
      assumption.
    ex_and H3 D'.
    induction (eq_dec_points A C).
      subst C.
      assert(exists P, exists T, Perp A B P A /\ Col A B T /\ Bet D' T P).
        apply l8_21.
        assumption.
      ex_and H3 P.
      ex_and H5 T.
      assert(exists P0, out A P P0 /\ Cong A P0 X Y).
        apply segment_construction_3.
          unfold Perp in H3.
          unfold Perp_in in H3.
          ex_and H3 Z.
          auto.
        assumption.
      ex_and H7 P0.
      exists P0.
      repeat split.
        eapply l8_5.
        apply cong_left_commutativity.
        assumption.
      unfold one_side.
      exists D'.
      split.
        eapply l9_5.
          3: apply H7.
          unfold two_sides.
          repeat split.
            assumption.
            assert(~Col A B P -> ~Col P A B).
              intro.
              intro.
              apply H9.
              apply col_permutation_1.
              assumption.
            apply H9.
            eapply perp_not_col.
            assumption.
            unfold two_sides in H4.
            spliter.
            assumption.
          exists T.
          split.
            apply col_permutation_2.
            assumption.
          apply between_symmetry.
          assumption.
        apply col_trivial_1.
      assumption.
    assert(exists P, exists T, Perp C A P C /\ Col C A T /\ Bet D' T P).
      apply l8_21.
      auto.
    ex_and H5 P.
    ex_and H6 T.
    assert (HH5 := H5).
    assert(exists P0, out C P P0 /\ Cong C P0 X Y).
      apply segment_construction_3.
        unfold Perp in H5.
        unfold Perp_in in H5.
        ex_and H5 Z.
        auto.
      assumption.
    ex_and H8 P0.
    exists P0.
    repeat split.
      eapply perp_per_1 in H5.
        eapply l8_2.
        eapply per_col.
          2: apply H5.
          unfold Perp in HH5.
          unfold Perp_in in HH5.
          ex_and HH5 Z.
          auto.
        apply out_col.
        assumption.
      auto.
      apply cong_left_commutativity.
      assumption.
    unfold one_side.
    exists D'.
    split.
      eapply l9_5.
        3: apply H8.
        unfold two_sides.
        repeat split.
          assumption.
          assert(~Col C A P -> ~Col P A B).
            intro.
            intro.
            apply H10.
            apply col_permutation_2.
            eapply col_transitivity_1.
              apply H.
              apply col_permutation_1.
              assumption.
            assumption.
          apply H10.
          eapply perp_not_col.
          assumption.
          unfold two_sides in H4.
          spliter.
          assumption.
        exists T.
        split.
          apply col_permutation_2.
          eapply col_transitivity_1.
            apply H3.
            apply col_permutation_5.
            assumption.
          apply col_permutation_4.
          assumption.
        apply between_symmetry.
        assumption.
      apply col_permutation_2.
      assumption.
    assumption.
Qed.


Lemma not_out_bet : forall A B C, Col A B C -> ~ out B A C -> Bet A B C.
Proof.
    intros.
    unfold out in H0.
    induction (eq_dec_points A B).
      subst.
      Between.
    induction (eq_dec_points B C).
      subst.
      Between.
    unfold Col in *.
    decompose [or] H;clear H.
      assumption.
      exfalso.
      apply H0.
      intuition.
    exfalso.
    apply H0.
    intuition.
Qed.

Lemma angle_construction_1 : forall A B C A' B' P,
 ~Col A B C -> ~Col A' B' P ->
 exists C', Conga A B C A' B' C' /\ one_side A' B' C' P.
Proof.
    intros.
    assert (exists C0, Col B A C0 /\ Perp B A C C0).
      eapply l8_18_existence.
      intro.
      apply H.
      apply col_permutation_4.
      assumption.
    ex_and H1 C0.
    induction(eq_dec_points B C0).
      subst C0.
      assert (exists  C', Per C' B' A' /\ Cong C' B' C B /\ one_side A' B' C' P).
        apply ex_per_cong.
          intro.
          subst A'.
          apply H0.
          apply col_trivial_1.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          apply col_trivial_2.
        assumption.
      ex_and  H3 C'.
      exists C'.
      split.
        eapply l11_16.
          apply perp_perp_in in H2.
          apply perp_in_comm in H2.
          apply perp_in_per in H2.
          assumption.
          intro.
          subst A.
          apply H.
          apply col_trivial_1.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          apply l8_2.
          assumption.
          intro.
          subst A'.
          apply H0.
          apply col_trivial_1.
        intro.
        subst C'.
        apply cong_symmetry in H4.
        apply cong_identity in H4.
        subst C.
        apply H.
        apply col_trivial_2.
      assumption.
    (*********** B <> C0 ***********)
    induction (out_dec B A C0).
      assert (exists C0', out B' A' C0' /\ Cong B' C0' B C0).
        eapply segment_construction_3.
          intro.
          subst A'.
          apply H0.
          apply col_trivial_1.
        assert (Perp_in C0 C0 C B C0).
          eapply perp_perp_in.
          apply perp_sym.
          eapply perp_col.
            assumption.
            apply perp_right_comm.
            apply H2.
          assumption.
        assumption.
      ex_and H5 C0'.
      assert (exists C' , Per C' C0' B' /\ Cong C' C0' C C0 /\ one_side B' C0' C' P).
        apply ex_per_cong.
          intro.
          subst C0'.
          unfold out in H5.
          spliter.
          absurde.
          intro.
          subst C0.
          unfold Perp in H2.
          ex_and H2 X.
          unfold Perp_in in H7.
          spliter.
          absurde.
          apply col_trivial_2.
        intro.
        apply H0.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ C0').
          intro.
          subst C0'.
          unfold out in H5.
          spliter.
          absurde.
          assumption.
        apply out_col.
        apply l6_6.
        assumption.
      ex_and H7 C'.
      assert (Cong_3 C0 B C C0' B' C').
        unfold Cong_3.
        repeat split.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        eapply (l10_12 _ C0).
          assert(Perp  B C0 C C0 ).
            eapply perp_col.
              intro.
              subst C0.
              apply perp_distinct in H2.
              spliter.
              absurde.
              apply H2.
            assumption.
          apply perp_left_comm in H10.
          apply perp_perp_in in H10.
          apply perp_in_per.
          apply perp_in_comm.
          assumption.
          apply l8_2.
          apply H7.
          apply cong_symmetry.
          assumption.
        apply cong_symmetry.
        apply cong_commutativity.
        assumption.
      exists C'.
      split.
        eapply (l11_10 C0 _ _ C0').
          apply cong3_conga.
            3: apply H10.
            intro.
            subst C0.
            absurde.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          assumption.
          apply out_trivial.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          assumption.
        apply out_trivial.
        intro.
        subst C'.
        apply l8_8 in H7.
        subst C0'.
        unfold out in H5.
        spliter.
        absurde.
      apply invert_one_side.
      eapply col_one_side.
        3: apply H9.
        apply out_col.
        apply l6_6.
        assumption.
      intro.
      subst A'.
      apply H0.
      apply col_trivial_1.
    (*********************)
    apply not_out_bet in H4.
      prolong A' B' C0' B C0.
      assert (exists C' , Per C' C0' B' /\ Cong C' C0' C C0 /\ one_side B' C0' C' P).
        apply ex_per_cong.
          intro.
          subst C0'.
          apply cong_symmetry in H6.
          apply cong_identity in H6.
          subst C0.
          absurde.
          intro.
          subst C0.
          apply perp_distinct in H2.
          spliter.
          absurde.
          apply col_trivial_2.
        intro.
        apply H0.
        apply col_permutation_2.
        eapply col_transitivity_1.
          2:apply H7.
          intro.
          subst C0'.
          apply cong_symmetry in H6.
          apply cong_identity in H6.
          subst C0.
          absurde.
        unfold Col.
        right; right.
        assumption.
      ex_and H7 C'.
      exists C'.
      split.
        assert (Cong_3 C0 B C C0' B' C').
          repeat split.
            apply cong_symmetry.
            apply cong_commutativity.
            assumption.
            apply cong_symmetry.
            apply cong_commutativity.
            assumption.
          apply cong_commutativity.
          eapply (l10_12 _ C0 _ _ C0').
            assert(Perp  B C0 C C0 ).
              eapply perp_col.
                intro.
                subst C0.
                apply perp_distinct in H2.
                spliter.
                absurde.
                apply H2.
              assumption.
            apply perp_left_comm in H10.
            apply perp_perp_in in H10.
            apply perp_in_per.
            apply perp_in_sym.
            assumption.
            assumption.
            apply cong_symmetry.
            assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        eapply l11_13.
          apply cong3_conga.
            3: apply H10.
            auto.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          apply between_symmetry.
          assumption.
          intro.
          subst A.
          apply H.
          apply col_trivial_1.
          apply between_symmetry.
          assumption.
        intro.
        subst A'.
        apply H0.
        apply col_trivial_1.
      apply invert_one_side.
      eapply col_one_side.
        3: apply H9.
        unfold Col.
        right; right.
        assumption.
      intro.
      subst A'.
      apply H0.
      apply col_trivial_1.
    apply col_permutation_4.
    assumption.
Qed.

Lemma angle_construction_2 : forall A B C A' B' P,
 Distincts A B C -> A' <> B' -> ~Col A' B' P ->
 exists C', Conga A B C A' B' C' /\ (one_side A' B' C' P \/ Col A' B' C').
Proof.
    unfold Distincts.
    intros.
    spliter.
    induction (Col_dec A B C).
      induction (out_dec B A C).
        exists A'.
        split.
          assert(Conga A B A A B C).
            eapply l11_10.
              apply conga_refl.
                3: apply H5.
              auto.
              2: apply H5.
              auto.
              assumption.
            apply out_trivial.
            auto.
          assert (Conga A B A A' B' A').
            apply conga_trivial_1.
              assumption.
            assumption.
          apply conga_sym.
          eapply conga_trans.
            apply conga_sym.
            apply H7.
          assumption.
        right.
        apply col_trivial_3.
      apply not_out_bet in H5.
        prolong A' B' C' A'  B'.
        exists C'.
        split.
          eapply conga_line.
            repeat split; assumption.
            repeat split.
              assumption.
              intro.
              subst C'.
              apply between_identity in H6.
              subst A'.
              absurde.
            intro.
            subst C'.
            apply cong_symmetry in H7.
            apply  cong_identity in H7.
            subst A'.
            absurde.
            assumption.
          assumption.
        right.
        unfold Col.
        left.
        assumption.
      assumption.
    assert(exists C' , Conga A B C A' B' C' /\ one_side A' B' C' P).
      apply angle_construction_1.
        assumption.
      assumption.
    ex_and H5 C'.
    exists C'.
    split.
      assumption.
    left.
    assumption.
Qed.


Lemma l11_15 : forall A B C D E P, ~ Col A B C -> ~ Col D E P ->
 exists F, Conga A B C D E F /\ one_side E D F P /\
          (forall F1 F2, ((Conga A B C D E F1 /\ one_side E D F1 P) /\
                          (Conga A B C D E F2 /\ one_side E D F2 P)) -> out E F1 F2).
Proof.
    intros.
    assert(exists F, Conga A B C D E F /\  one_side D E F P)
      by (apply angle_construction_1; assumption).
    ex_and H1 F.
    exists F.
    split.
      assumption.
    split.
      apply invert_one_side.
      assumption.
    intros.
    spliter.
    assert(out E F1 F2 \/ two_sides D E F1 F2).
      apply l11_22_aux.
      eapply conga_trans.
        apply conga_sym.
        apply H3.
      assumption.
    induction H7.
      assumption.
    assert(one_side E D F1 F2).
      eapply one_side_transitivity.
        apply H6.
      apply one_side_symmetry.
      assumption.
    apply l9_9_bis in H8.
    apply invert_two_sides in H7.
    contradiction.
Qed.

Lemma l11_19 : forall A B P1 P2,
  Per A B P1 -> Per A B P2 -> one_side  A B P1 P2 ->
  out B P1 P2.
Proof.
    intros.
    induction (Col_dec A B P1).
      induction (l8_9 A B P1 H H2).
        subst.
        unfold one_side in *.
        decompose [ex and] H1.
        unfold two_sides in *.
        intuition.
      subst.
      unfold one_side in *.
      decompose [ex and] H1.
      unfold two_sides in *.
      spliter.
      assert (Col B A B) by Col.
      intuition.
    induction (Col_dec A B P2).
      induction (l8_9 A B P2 H0 ).
        subst.
        unfold one_side in *.
        decompose [ex and] H1.
        unfold two_sides in *.
        intuition.
        subst.
        unfold one_side in *.
        decompose [ex and] H1.
        unfold two_sides in *.
        spliter.
        assert (Col B A B) by Col.
        intuition.
      Col.
    assert (T:=l11_15 A B P1 A B P2 H2 H3).
    decompose [ex and] T.
    apply H7.
    split.
      split.
        apply conga_refl.
          intro;subst;Col.
        intro;subst;Col.
      apply invert_one_side;auto.
    split.
      apply l11_16;try assumption.
        intro;subst;Col.
        intro;subst;Col.
        intro;subst;Col.
      intro;subst;Col.
    apply one_side_reflexivity.
    Col.
Qed.

Lemma l11_22_bet :
 forall A B C P A' B' C' P',
  Bet A B C ->
  two_sides P' B' A' C' ->
  Conga A B P A' B' P' /\ Conga P B C  P' B' C' ->
  Bet A' B' C'.
Proof.
    intros.
    spliter.
    prolong A' B' C'' B C.
    assert(Conga C B P C'' B' P').
      eapply l11_13.
        2:apply H.
        apply H1.
        unfold Conga in H2.
        spliter.
        assumption.
        assumption.
      intro.
      subst C''.
      apply cong_symmetry in H4.
      apply cong_identity in H4.
      subst C.
      unfold Conga in H2.
      spliter.
      absurde.
    assert (Conga C'' B' P' C' B' P').
      eapply conga_trans.
        apply conga_sym.
        apply H5.
      apply conga_comm.
      assumption.
    assert(out B' C' C'' \/ two_sides P' B' C' C'').
      apply l11_22_aux.
      apply conga_comm.
      apply conga_sym.
      assumption.
    induction H7.
      unfold out in H7.
      spliter.
      induction H9.
        eapply between_inner_transitivity.
          apply H3.
        assumption.
      eapply outer_transitivity_between.
        apply H3.
        assumption.
      auto.
    induction (Col_dec C' B' P').
      unfold two_sides in H7.
      spliter.
      apply False_ind.
      apply H9.
      apply col_permutation_5.
      assumption.
    assert (B' <> P').
      intro.
      subst P'.
      apply H8.
      apply col_trivial_2.
    assert (two_sides B' P' A' C'').
      unfold two_sides.
      repeat split.
        assumption.
        unfold two_sides in H0.
        spliter.
        intro.
        apply H10.
        apply col_permutation_5.
        assumption.
        intro.
        unfold two_sides in H7.
        spliter.
        apply H12.
        apply col_permutation_5.
        assumption.
      exists B'.
      split.
        apply col_trivial_1.
      assumption.
    assert (one_side B' P' C' C'').
      eapply l9_8_1.
        apply l9_2.
        apply invert_two_sides.
        apply H0.
      apply l9_2.
      assumption.
    apply l9_9_bis in H11.
    apply invert_two_sides in H7.
    contradiction.
Qed.

Lemma not_bet_and_out :
 forall A B C,
 ~ (Bet A B C /\ out B A C).
Proof.
    intros.
    intro.
    spliter.
    unfold out in H0.
    spliter.
    induction H2.
      assert ( A = B).
        eapply between_egality.
          apply H.
        assumption.
      contradiction.
    assert(C = B).
      eapply between_egality.
        apply between_symmetry.
        apply H.
      assumption.
    contradiction.
Qed.


Lemma out_to_bet :
 forall A B C A' B' C',
  Col A' B' C' ->
 (out B A C <-> out B' A' C') ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    induction(out_dec B A C).
      unfold out in H2.
      spliter.
      induction H4.
        assert( A = B).
          eapply between_egality.
            apply H1.
          assumption.
        contradiction.
      assert(C = B).
        apply(between_symmetry) in H4.
        eapply between_egality.
          apply between_symmetry.
          apply H1.
        apply between_symmetry.
        assumption.
      contradiction.
    destruct H0.
    assert (~out B' A' C').
      intro.
      apply H2.
      apply H3.
      assumption.
    apply not_out_bet.
      assumption.
    assumption.
Qed.

Lemma l11_22a :
 forall A B C P A' B' C' P',
 two_sides B P A C /\ two_sides B' P' A' C' /\
 Conga A B P A' B' P' /\ Conga P B C  P' B' C' ->
 Conga A B C A' B' C'.
Proof.
    intros.
    spliter.
    assert (A <> B /\ A' <> B' /\ P <> B /\ P' <> B' /\ C <> B /\ C' <> B').
      unfold Conga in *.
      spliter.
      repeat split; assumption.
    assert(A <> C /\ A' <> C').
      unfold two_sides in *.
      spliter.
      ex_and H14 T.
      ex_and H11 T'.
      split.
        intro.
        subst C.
        apply between_identity in H15.
        subst T.
        contradiction.
      intro.
      subst C'.
      apply between_identity in H16.
      subst T'.
      contradiction.
    spliter.
    assert(exists A'', out B' A' A'' /\ Cong B' A'' B A).
      eapply segment_construction_3; auto.
    ex_and H11 A''.
    unfold two_sides in H.
    spliter.
    ex_and H15 T.
    induction (eq_dec_points B T).
      subst T.
      assert(Bet A' B' C').
        eapply l11_22_bet.
          apply H16.
          apply invert_two_sides.
          apply H0.
        split.
          apply H1.
        assumption.
      apply conga_line.
        repeat split.
          assumption.
          assumption.
        auto.
        repeat split; try assumption.
        auto.
        assumption.
      assumption.
    induction(Bet_dec P B T).
      assert(exists T'', Col B' P' T'' /\ (out B' P' T'' <-> out B P T) /\ Cong B' T'' B T).
        prolong P' B' T'' B T.
        exists T''.
        split.
          unfold Col.
          right; right.
          apply between_symmetry.
          assumption.
        split.
          split.
            intro.
            assert(Bet P' B' T'' /\ out B' P' T'').
              split; assumption.
            apply (not_bet_and_out _ _  _)in H22.
            contradiction.
          intro.
          assert(Bet P B T /\ out B P T).
            split; assumption.
          apply (not_bet_and_out _ _  _)in H22.
          contradiction.
        assumption.
      ex_and H19 T''.
      destruct H20.
      assert (B' <> T'').
        intro.
        subst T''.
        apply cong_symmetry in H21.
        apply cong_identity in H21.
        contradiction.
      assert(exists C'', Bet A'' T'' C'' /\ Cong T'' C'' T C).
        prolong A'' T'' C'' T C.
        exists C''.
        split; assumption.
      ex_and H24 C''.
      assert(Conga A B T A' B' T'').
        apply conga_comm.
        eapply l11_13.
          apply conga_comm.
          apply H1.
          assumption.
          auto.
          eapply out_to_bet.
            apply col_permutation_4.
            assumption.
            split.
              apply H22.
            assumption.
          assumption.
        auto.
      assert(Conga A B T A'' B'  T'').
        eapply l11_10.
          apply H26.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A T A'' T'').
        assert(HH:= l11_4_1 A B T A'' B' T'' H27).
        spliter.
        apply H32.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          intro.
          subst A''.
          absurde.
        split.
          apply out_trivial.
          assumption.
        split.
          apply cong_symmetry.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong A C A'' C'').
        eapply l2_11.
          apply H16.
          apply H24.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong C B C'' B').
        eapply (five_segments).
          5:apply H16.
          5: apply H24.
          assumption.
          apply cong_symmetry.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        intro.
        subst T.
        apply H13.
        assumption.
      assert(Conga A B C A'' B' C'').
        apply cong3_conga.
          assumption.
          assumption.
        repeat split.
          apply cong_commutativity.
          apply cong_symmetry.
          assumption.
          assumption.
        apply cong_commutativity.
        assumption.
      assert(Conga C B T  C'' B' T'').
        apply cong3_conga.
          assumption.
          auto.
        repeat split.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      assert (Conga P B C P' B' C'').
        eapply l11_13.
          apply conga_comm.
          apply H32.
          apply between_symmetry.
          assumption.
          assumption.
          apply between_symmetry.
          eapply out_to_bet.
            eapply col_permutation_4.
            assumption.
            split.
              apply H22.
            assumption.
          assumption.
        assumption.
      assert(Conga P' B' C' P' B' C'').
        eapply conga_trans.
          apply conga_sym.
          apply H2.
        assumption.
      assert(out B' C' C'' \/ two_sides P' B' C' C'').
        apply l11_22_aux.
        assumption.
      induction H35.
        eapply l11_10.
          apply H31.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          assumption.
        assumption.
      assert(two_sides B' P' A'' C').
        apply l9_2.
        eapply l9_5.
          eapply l9_2.
          eapply l9_5.
            apply H0.
            apply col_trivial_1.
          assumption.
          apply col_trivial_1.
        apply out_trivial.
        auto.
      apply invert_two_sides in H35.
      apply l9_2 in H35.
      assert(one_side B' P'  A'' C'').
        unfold one_side.
        exists C'.
        split; assumption.
      assert (two_sides B' P' A''  C'').
        unfold two_sides.
        repeat split.
          auto.
          intro.
          unfold two_sides in H0.
          spliter.
          apply H39.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ A'').
            intro.
            subst A''.
            unfold out in H11.
            spliter.
            absurde.
            apply col_permutation_4.
            assumption.
          apply out_col in H11.
          apply col_permutation_5.
          assumption.
          intro.
          unfold two_sides in H35.
          spliter.
          apply H39.
          assumption.
        exists T''.
        split.
          apply col_permutation_2.
          assumption.
        assumption.
      apply l9_9 in H38.
      contradiction.
    apply not_bet_out in H18.
      assert(exists T'', Col B' P' T'' /\ (out B' P' T'' <-> out B P T) /\ Cong B' T'' B T).
        assert (exists T'', out B' P' T'' /\ Cong B' T'' B T).
          apply segment_construction_3.
            auto.
          assumption.
        ex_and H19 T''.
        exists T''.
        split.
          apply out_col in H19.
          assumption.
        split.
          split.
            intro.
            assumption.
          intro.
          assumption.
        assumption.
      ex_and H19 T''.
      destruct H20.
      assert (B' <> T'').
        intro.
        subst T''.
        apply cong_symmetry in H21.
        apply cong_identity in H21.
        contradiction.
      assert(exists C'', Bet A'' T'' C'' /\ Cong T'' C'' T C).
        prolong A'' T'' C'' T C.
        exists C''.
        split; assumption.
      ex_and H24 C''.
      assert(Conga A B T A' B' T'').
        eapply l11_10.
          apply H1.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
          apply out_trivial.
          auto.
        apply l6_6.
        apply H22.
        assumption.
      assert(Conga A B T A'' B'  T'').
        eapply l11_10.
          apply H26.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A T A'' T'').
        assert(HH:= l11_4_1 A B T A'' B' T'' H27).
        spliter.
        apply H32.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          assumption.
        split.
          apply out_trivial.
          intro.
          subst A''.
          absurde.
        split.
          apply out_trivial.
          assumption.
        split.
          apply cong_symmetry.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong A C A'' C'').
        eapply l2_11.
          apply H16.
          apply H24.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong C B C'' B').
        eapply (five_segments).
          5:apply H16.
          5: apply H24.
          assumption.
          apply cong_symmetry.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        intro.
        apply H13.
        subst T.
        assumption.
      assert(Conga A B C A'' B' C'').
        apply cong3_conga.
          assumption.
          assumption.
        repeat split.
          apply cong_commutativity.
          apply cong_symmetry.
          assumption.
          assumption.
        apply cong_commutativity.
        assumption.
      assert(Conga C B T  C'' B' T'').
        apply cong3_conga.
          assumption.
          auto.
        repeat split.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      eapply l11_10.
        apply H31.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        assumption.
      assert(out B' C' C'' \/ two_sides P' B' C' C'').
        apply l11_22_aux.
        apply conga_comm.
        eapply conga_trans.
          apply conga_comm.
          apply conga_sym.
          apply H2.
        eapply l11_10.
          apply H32.
          apply out_trivial.
          auto.
          assumption.
          apply out_trivial.
          intro.
          subst C''.
          apply cong_identity in H30.
          contradiction.
        apply H22.
        assumption.
      induction H33.
        assumption.
      assert(two_sides B' P' A'' C').
        apply l9_2.
        eapply l9_5.
          eapply l9_2.
          eapply l9_5.
            apply H0.
            apply col_trivial_1.
          assumption.
          apply col_trivial_1.
        apply out_trivial.
        auto.
      assert(one_side B' P'  A'' C'').
        unfold one_side.
        exists C'.
        split.
          assumption.
        apply invert_two_sides in H33.
        apply l9_2 in H33.
        assumption.
      assert (two_sides B' P' A''  C'').
        unfold two_sides.
        repeat split.
          auto.
          intro.
          unfold two_sides in H34.
          spliter.
          apply H37.
          assumption.
          intro.
          unfold two_sides in H33.
          spliter.
          apply H38.
          apply col_permutation_5.
          assumption.
        exists T''.
        split.
          apply col_permutation_2.
          assumption.
        assumption.
      apply l9_9 in H36.
      contradiction.
      assumption.
      auto.
    apply col_permutation_3.
    assumption.
Qed.

Lemma l11_22b :
 forall A B C P A' B' C' P',
 one_side B P A C /\ one_side B' P' A' C' /\
 Conga A B P A' B' P' /\ Conga P B C  P' B' C' ->
 Conga A B C A' B' C'.
Proof.
    intros.
    spliter.
    prolong A B D A B.
    prolong A' B' D' A' B'.
    assert(Conga D B P D' B' P').
      eapply l11_13.
        apply H1.
        assumption.
        intro.
        subst D.
        apply cong_symmetry in H4.
        apply cong_identity in H4.
        subst A.
        unfold Conga in H1.
        spliter.
        absurde.
        assumption.
      intro.
      subst D'.
      apply cong_symmetry in H6.
      apply cong_identity in H6.
      subst A'.
      unfold Conga in H1.
      spliter.
      absurde.
    assert (Conga D B C D' B' C').
      eapply (l11_22a _ _ _ P _ _ _ P').
      split.
        eapply l9_2.
        eapply l9_8_2.
          2: apply H.
        unfold one_side in H.
        ex_and H T.
        unfold two_sides in H.
        unfold two_sides in H8.
        spliter.
        repeat split.
          assumption.
          assumption.
          intro.
          apply H12.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ D).
            intro.
            subst D.
            unfold Conga in H7.
            spliter.
            absurde.
            apply col_permutation_4.
            assumption.
          unfold Col.
          right; right.
          assumption.
        exists B.
        split.
          apply col_trivial_1.
        assumption.
      split.
        eapply l9_2.
        eapply l9_8_2.
          2: apply H0.
        unfold one_side in H0.
        ex_and H0 T'.
        unfold two_sides in H0.
        unfold two_sides in H8.
        spliter.
        repeat split.
          assumption.
          assumption.
          intro.
          apply H12.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ D').
            intro.
            subst D'.
            unfold Conga in H7.
            spliter.
            absurde.
            apply col_permutation_4.
            assumption.
          unfold Col.
          right; right.
          assumption.
        exists B'.
        split.
          apply col_trivial_1.
        assumption.
      split; assumption.
    eapply l11_13.
      apply H8.
      apply between_symmetry.
      assumption.
      intro.
      subst A.
      unfold Conga in H1.
      spliter.
      absurde.
      apply between_symmetry.
      assumption.
    intro.
    subst A'.
    unfold Conga in H1.
    spliter.
    absurde.
Qed.


Lemma l11_22 :
 forall A B C P A' B' C' P',
 ((two_sides B P A C /\ two_sides B' P' A' C')\/
  (one_side B P A C /\ one_side B' P' A' C')) /\
  Conga A B P A' B' P' /\ Conga P B C  P' B' C' ->
 Conga A B C A' B' C'.
Proof.
    intros.
    spliter.
    induction H.
      eapply (l11_22a _ _ _ P _ _ _ P');tauto.
    eapply (l11_22b _ _ _ P _ _ _ P');tauto.
Qed.

Definition InAngle P A B C :=
  A<>B /\ C<>B /\ P<>B /\ exists X, Bet A X C /\ (X=B \/ out B X P).

Lemma l11_24 :
 forall P A B C,
  InAngle P A B C ->
  InAngle P C B A.
Proof.
    unfold InAngle.
    intros.
    spliter.
    ex_and H2 X.
    repeat split; try assumption.
    exists X.
    split.
      apply between_symmetry.
      assumption.
    assumption.
Qed.

Lemma out_in_angle :
 forall A B C P,
  out B A C ->
  out B P A ->
  InAngle P A B C.
Proof.
    intros.
    unfold InAngle.
    unfold out in H.
    unfold out in H0.
    spliter.
    split.
      assumption.
    split.
      assumption.
    split.
      assumption.
    induction H4; induction H2.
      assert(exists X, is_midpoint X A C).
        eapply midpoint_existence.
      ex_and H5 X.
      exists X.
      split.
        apply midpoint_bet.
        assumption.
      right.
      repeat split.
        intro.
        subst X.
        apply midpoint_bet in H6.
        assert (A = B).
          eapply between_egality.
            apply H6.
          assumption.
        contradiction.
        assumption.
      right.
      induction (eq_dec_points P A).
        subst P.
        eapply between_inner_transitivity.
          apply H4.
        apply midpoint_bet.
        assumption.
      assert(Bet P A C).
        eapply between_exchange3.
          apply H2.
        assumption.
      assert(Bet P A X).
        eapply between_inner_transitivity.
          apply H7.
        apply midpoint_bet.
        assumption.
      eapply outer_transitivity_between.
        apply H2.
        assumption.
      assumption.
      assert(exists X, is_midpoint X A C).
        eapply midpoint_existence.
      ex_and H5 X.
      exists X.
      repeat split.
        apply midpoint_bet.
        assumption.
      right.
      repeat split.
        intro.
        subst X.
        apply midpoint_bet in H6.
        assert (A = B).
          eapply between_egality.
            apply H6.
          assumption.
        contradiction.
        assumption.
      assert(Bet B C P \/ Bet B P C).
        eapply l5_1.
          2: apply H4.
          auto.
        assumption.
      induction H5.
        left.
        assert(Bet B X C).
          eapply between_exchange2.
            apply H4.
          apply midpoint_bet.
          assumption.
        eapply between_exchange4.
          apply H7.
        assumption.
      assert(Bet B A X).
        eapply between_inner_transitivity.
          apply H4.
        apply  midpoint_bet.
        assumption.
      eapply l5_1.
        2:apply H7.
        auto.
      assumption.
      assert(Bet B P C \/ Bet B C P).
        eapply l5_3.
          apply H2.
        assumption.
      induction H5.
        assert(exists X, is_midpoint X A C).
          eapply midpoint_existence.
        ex_and H6 X.
        exists X.
        split.
          apply midpoint_bet.
          assumption.
        right.
        repeat split.
          intro.
          subst X.
          apply midpoint_bet in H7.
          apply between_symmetry in H7.
          assert (C = B).
            eapply between_egality.
              apply H7.
            assumption.
          contradiction.
          assumption.
        right.
        assert(Bet B C X).
          eapply between_inner_transitivity.
            apply H4.
          apply midpoint_bet.
          apply l7_2.
          assumption.
        eapply between_exchange4.
          apply H5.
        assumption.
      assert(exists X, is_midpoint X A C).
        eapply midpoint_existence.
      ex_and H6 X.
      exists X.
      repeat split.
        apply midpoint_bet.
        assumption.
      right.
      repeat split.
        intro.
        subst X.
        apply midpoint_bet in H7.
        apply between_symmetry in H7.
        assert (C = B).
          eapply between_egality.
            apply H7.
          assumption.
        contradiction.
        assumption.
      assert (Bet B C X).
        eapply between_inner_transitivity.
          apply H4.
        apply midpoint_bet.
        eapply l7_2.
        assumption.
      eapply l5_1.
        2:apply H6.
        auto.
      assumption.
    assert(exists X, is_midpoint X A C).
      eapply midpoint_existence.
    ex_and H5 X.
    exists X.
    split.
      apply midpoint_bet.
      assumption.
    right.
    repeat split.
      intro.
      subst X.
      apply midpoint_bet in H6.
      apply between_symmetry in H6.
      assert (C = B).
        eapply between_egality.
          apply H6.
        assumption.
      contradiction.
      assumption.
    left.
    assert(Bet B X A).
      eapply between_exchange2.
        apply H4.
      apply midpoint_bet.
      apply l7_2.
      assumption.
    eapply between_exchange4.
      apply H5.
    assumption.
Qed.


Lemma col_in_angle :
 forall A B C P,
  A <> B -> C <> B -> P <> B ->
  out B A P \/ out B C P ->
  InAngle P A B C.
Proof.
    intros.
    induction H2.
      repeat split; try assumption.
      exists A.
      split.
        apply between_symmetry.
        apply between_trivial.
      right.
      assumption.
    repeat split; try assumption.
    exists C.
    split.
      apply between_trivial.
    right.
    assumption.
Qed.


Lemma in_angle_two_sides :
 forall A B C P,
  ~ Col B A P -> ~ Col B C P ->
  InAngle P A B C ->
  two_sides P B A C.
Proof.
    intros.
    unfold InAngle in H1.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      unfold two_sides.
      repeat split.
        assumption.
        intro.
        apply H.
        apply col_permutation_2.
        assumption.
        intro.
        apply H0.
        apply col_permutation_2.
        assumption.
      exists B.
      split.
        apply col_trivial_3.
      assumption.
    repeat split.
      assumption.
      intro.
      apply H.
      apply col_permutation_2.
      assumption.
      intro.
      apply H0.
      apply col_permutation_2.
      assumption.
    exists X.
    split.
      apply out_col in H5.
      apply col_permutation_1.
      assumption.
    assumption.
Qed.

Lemma in_angle_out :
 forall A B C P,
  out B A C ->
  InAngle P A B C ->
  out B A P.
Proof.
    intros.
    unfold InAngle in H0.
    spliter.
    ex_and H3 X.
    induction H4.
      subst X.
      assert( Bet A B C /\ out B A C).
        split; assumption.
      apply not_bet_and_out in H4.
      contradiction.
    unfold out in *.
    spliter.
    induction H8; induction H6.
      repeat split; try assumption.
      left.
      assert(Bet B A X).
        eapply between_inner_transitivity.
          apply H8.
        apply H3.
      eapply between_exchange4.
        apply H9.
      assumption.
      repeat split; try assumption.
      assert(Bet B A X).
        eapply between_inner_transitivity.
          apply H8.
        assumption.
      eapply l5_3.
        apply H9.
      assumption.
      repeat split; try assumption.
      assert(Bet B X A).
        eapply between_exchange2.
          apply H8.
        apply between_symmetry.
        assumption.
      eapply l5_1.
        2: apply H9.
        auto.
      assumption.
    repeat split; try assumption.
    right.
    assert(Bet B X A).
      eapply between_exchange2.
        apply H8.
      apply between_symmetry.
      assumption.
    eapply between_exchange4.
      apply H6.
    assumption.
Qed.

Lemma col_in_angle_out :
 forall A B C P,
  Col B A P ->
  ~ Bet A B C ->
  InAngle P A B C ->
  out B A P.
Proof.
    intros.
    unfold InAngle in H1.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      contradiction.
    induction (eq_dec_points A X).
      subst X.
      assumption.
    apply not_bet_out in H0.
      assert(out B A P /\ out B C P).
        eapply out2_bet_out.
          assumption.
          apply H5.
        assumption.
      spliter.
      assumption.
      assumption.
      assumption.
    assert (Col B A X).
      eapply col_transitivity_1.
        2: apply col_permutation_5.
        2: apply H.
        auto.
      apply out_col in H5.
      apply col_permutation_5.
      assumption.
    eapply col_transitivity_2.
      2: apply col_permutation_3.
      2:apply H7.
      auto.
    unfold Col.
    right; right.
    apply between_symmetry.
    assumption.
Qed.


Lemma l11_25_aux : forall P A B C A' ,
 InAngle P A B C ->
 ~ Bet A B C ->
 out B A' A ->
 InAngle P A' B C.
Proof.
    intros.
    unfold out in H1.
    unfold InAngle in H.
    spliter.
    repeat  split ; try assumption.
    induction H3.
      ex_and H6 X.
      assert(exists T, Bet A' T C /\ Bet X T B).
        eapply inner_pasch.
          apply H3.
        apply between_symmetry.
        assumption.
      ex_and H8 T.
      exists T.
      split.
        assumption.
      right.
      induction H7.
        subst B.
        contradiction.
      unfold out in *.
      spliter.
      repeat split.
        intro.
        subst T.
        apply H0.
        apply between_symmetry.
        eapply outer_transitivity_between.
          apply between_symmetry.
          apply H8.
          assumption.
        auto.
        assumption.
      induction H11.
        left.
        eapply between_exchange4.
          apply between_symmetry.
          apply H9.
        assumption.
      eapply l5_3.
        apply between_symmetry.
        apply H9.
      assumption.
    ex_and H6 X.
    induction H7.
      subst X.
      contradiction.
    assert(exists T, Bet A' T C /\ Bet B X T).
      eapply outer_pasch.
        apply between_symmetry.
        apply H3.
      apply between_symmetry.
      assumption.
    ex_and H8 T.
    exists T.
    split.
      assumption.
    right.
    unfold out in H7.
    spliter.
    repeat split.
      intro.
      subst T.
      apply between_identity in H9.
      subst X.
      absurde.
      assumption.
    induction H11.
      eapply l5_1.
        2: apply H9.
        auto.
      assumption.
    right.
    eapply between_exchange4.
      apply H11.
    assumption.
Qed.

Lemma l11_25 : forall P A B C A' C' P',
 InAngle P A B C ->
 out B A' A ->
 out B C' C ->
 out B P' P ->
 InAngle P' A' B C'.
Proof.
    intros.
    induction (Bet_dec A B C).
      repeat split.
        unfold out in H0.
        spliter.
        assumption.
        unfold out in H1.
        spliter.
        assumption.
        unfold out in H2.
        spliter.
        assumption.
      exists B.
      split.
        eapply bet_out_out_bet.
          apply H3.
          apply l6_6.
          assumption.
        apply l6_6.
        assumption.
      left.
      reflexivity.
    assert(InAngle P A' B C).
      eapply l11_25_aux.
        apply H.
        assumption.
      assumption.
    assert(InAngle P A' B C').
      apply l11_24.
      eapply l11_25_aux.
        apply l11_24.
        apply H4.
        intro.
        apply H3.
        apply between_symmetry.
        eapply bet_out_out_bet.
          apply H5.
          apply out_trivial.
          unfold InAngle in H.
          spliter.
          auto.
        assumption.
      assumption.
    unfold InAngle in H5.
    spliter.
    ex_and H8 X.
    induction H9.
      subst X.
      apply False_ind.
      apply H3.
      eapply bet_out_out_bet.
        apply H8.
        assumption.
      assumption.
    repeat split.
      assumption.
      assumption.
      intro.
      subst P'.
      unfold out in H2.
      spliter.
      absurde.
    exists X.
    split.
      assumption.
    right.
    eapply l6_7.
      apply H9.
    apply l6_6.
    assumption.
Qed.

Definition lea := fun A B C D E F =>
   exists P, InAngle P D E F /\ Conga A B C D E P.

Lemma segment_construction_0 : forall A B A', exists B', Cong A' B' A B.
Proof.
    intros.
    induction (eq_dec_points A B).
      exists A'.
      subst B.
      apply cong_trivial_identity.
    assert(exists X : Tpoint, A' <> X).
      apply another_point.
    ex_and H0 X.
    assert(HH:=segment_construction_3 A' X A B H1 H).
    ex_and HH B'.
    exists B'.
    assumption.
Qed.

Lemma angle_construction_3 :
 forall A B C A' B',
  A <> B -> C <> B -> A' <> B' ->
  exists C', Conga A B C A' B' C'.
Proof.
    intros.
    assert(exists P, ~Col A' B' P).
      eapply l6_25.
      assumption.
    ex_and H2 P.
    induction (eq_dec_points A C).
      subst C.
      exists A'.
      apply conga_trivial_1; assumption.
    assert(exists C', Conga A B C A' B' C' /\ (one_side A' B' C' P \/ Col A' B' C')).
      apply angle_construction_2.
        repeat split; try assumption.
        auto.
        assumption.
      assumption.
    ex_and H4 C'.
    exists C'.
    assumption.
Qed.



Lemma l11_28 : forall A B C D A' B' C',
 Cong_3 A B C A' B' C' -> Col A C D ->
 exists D', Cong A D A' D' /\ Cong B D B' D' /\ Cong C D C' D'.
Proof.
    intros.
    induction (eq_dec_points A C).
      subst C.
      unfold Cong_3 in H.
      spliter.
      apply cong_symmetry in H1.
      apply cong_identity in H1.
      subst C'.
      induction(eq_dec_points A B).
        subst B.
        apply cong_symmetry in H2.
        apply cong_identity in H2.
        subst B'.
        assert(exists D', Cong A' D' A D).
          apply segment_construction_0.
        ex_and H1 D'.
        exists D'.
        apply cong_symmetry in H2.
        repeat split; assumption.
      induction (eq_dec_points A D).
        exists A'.
        subst D.
        repeat split.
          apply cong_trivial_identity.
          assumption.
        apply cong_trivial_identity.
      induction (eq_dec_points B D).
        subst D.
        exists B'.
        repeat split.
          assumption.
          apply cong_trivial_identity.
        assumption.
      assert(exists D'', Conga B A D B' A' D'').
        eapply angle_construction_3.
          auto.
          auto.
        intro.
        subst B'.
        apply cong_identity in H.
        contradiction.
      ex_and H5 D''.
      assert(exists D', out A' D'' D' /\ Cong A' D' A D).
        apply segment_construction_3.
          unfold Conga in H6.
          spliter.
          auto.
        assumption.
      ex_and H5 D'.
      exists D'.
      repeat split.
        apply cong_symmetry.
        assumption.
        assert(Conga B A D B' A' D').
          eapply (l11_10 B A D B' A' D''); try apply out_trivial; try solve [auto].
            intro.
            subst B'.
            unfold Conga in H6.
            spliter.
            absurde.
          apply l6_6.
          assumption.
        eapply (cong2_conga_cong _ A _ _ A' _).
          apply H8.
          assumption.
        Cong.
      Cong.
    unfold Cong_3 in H.
    spliter.
    (*****************)
    induction(eq_dec_points A D).
      subst D.
      exists A'.
      repeat split.
        apply cong_trivial_identity.
        apply cong_commutativity.
        assumption.
      apply cong_commutativity.
      assumption.
    unfold Col in H0.
    induction H0.
      prolong A' C' D' C D.
      exists D'.
      repeat split.
        eapply (l2_11 A C D A' C' D'); try assumption.
        apply cong_symmetry.
        assumption.
        apply cong_commutativity.
        eapply (five_segments_with_def A C D B A' C' D' B').
          repeat split; try assumption.
            apply cong_symmetry.
            assumption.
          apply cong_commutativity.
          assumption.
        assumption.
      apply cong_symmetry.
      assumption.
    induction H0.
      assert(exists D', Bet A' D' C' /\ Cong_3 A D C A' D' C').
        eapply l4_5.
          apply between_symmetry.
          assumption.
        assumption.
      ex_and H5 D'.
      unfold Cong_3 in H6.
      spliter.
      exists D'.
      repeat split.
        assumption.
        apply cong_commutativity.
        eapply (l4_2 A D C B A' D' C' B').
        repeat split; try assumption.
          apply between_symmetry.
          assumption.
        apply cong_commutativity.
        assumption.
      apply cong_commutativity.
      assumption.
    prolong C' A' D' A D.
    exists D'.
    repeat split.
      apply cong_symmetry.
      assumption.
      apply cong_commutativity.
      eapply (five_segments_with_def C A D B C' A' D' B').
        repeat split; try assumption.
          apply between_symmetry.
          assumption.
          apply cong_commutativity.
          assumption.
          apply cong_symmetry.
          assumption.
        apply cong_commutativity.
        assumption.
      auto.
    eapply l2_11.
      apply between_symmetry.
      apply H0.
      apply H5.
      apply cong_commutativity.
      assumption.
    apply cong_symmetry.
    assumption.
Qed.


Lemma bet_conga_bet :
 forall A B C A' B' C',
  Bet A B C ->
  Conga A B C A' B' C' ->
  Bet A' B' C'.
Proof.
    intros.
    unfold Conga in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert(Bet A0 B C0).
      eapply outer_transitivity_between.
        2:apply H6.
        apply between_symmetry.
        eapply outer_transitivity_between.
          2:apply H4.
          apply between_symmetry.
          assumption.
        auto.
      auto.
    assert(Cong_3 A0 B C0 A1 B' C1).
      repeat split.
        apply cong_right_commutativity.
        eapply l2_11.
          apply between_symmetry.
          apply H4.
          apply H8.
          apply cong_left_commutativity.
          assumption.
        apply cong_symmetry.
        apply cong_right_commutativity.
        assumption.
        assumption.
      apply cong_right_commutativity.
      eapply l2_11.
        apply H6.
        apply between_symmetry.
        apply H10.
        apply cong_symmetry.
        apply cong_left_commutativity.
        assumption.
      apply cong_right_commutativity.
      assumption.
    assert(Bet A1 B' C1).
      eapply l4_6.
        apply H13.
      assumption.
    eapply between_inner_transitivity.
      2:apply H10.
    eapply between_exchange3.
      apply between_symmetry.
      apply H8.
    assumption.
Qed.

Lemma out_in_angle_out :
 forall A B C P,
  out B A C ->
  InAngle P A B C ->
  out B A P.
Proof.
    intros.
    unfold InAngle in H0.
    spliter.
    ex_and H3 X.
    induction H4.
      subst X.
      unfold out in H.
      spliter.
      induction H5.
        assert (A = B).
          eapply between_egality.
            apply H3.
          assumption.
        contradiction.
      assert (C = B).
        eapply between_egality.
          apply between_symmetry.
          apply H3.
        assumption.
      contradiction.
    unfold out in H.
    spliter.
    induction H6.
      assert(Bet B A X).
        eapply between_inner_transitivity.
          apply H6.
        assumption.
      unfold out in H4.
      spliter.
      induction H9.
        assert(Bet B A P).
          eapply between_exchange4.
            apply H7.
          assumption.
        apply bet_out; assumption.
      assert(Bet B A P \/ Bet B P A).
        eapply l5_3.
          apply H7.
        assumption.
      unfold out.
      repeat split; assumption.
    assert (Bet B X A).
      eapply between_exchange2.
        apply H6.
      apply between_symmetry.
      assumption.
    unfold out in H4.
    spliter.
    induction H9.
      assert(Bet B A P \/ Bet B P A).
        eapply l5_1.
          2: apply H7.
          auto.
        assumption.
      unfold out.
      repeat split; try assumption.
    assert(Bet B P A).
      eapply between_exchange4.
        apply H9.
      assumption.
    eapply l6_6.
    apply bet_out; assumption.
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

Lemma in_angle_one_side :
 forall A B C P,
  ~ Col A B C ->
  ~ Col B A P ->
  InAngle P A B C ->
  one_side A B P C.
Proof.
    intros.
    unfold InAngle in H1.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      apply False_ind.
      apply H.
      unfold Col.
      left.
      assumption.
    unfold one_side.
    prolong C A C' C A.
    exists C'.
    assert(two_sides A B X C').
      repeat split.
        assumption.
        intro.
        apply H0.
        eapply (col_transitivity_1 _ X).
          intro.
          subst X.
          apply H.
          left.
          assumption.
          eapply (col_transitivity_1 _ A).
            auto.
            apply col_permutation_3.
            assumption.
          apply col_trivial_2.
        apply out_col.
        assumption.
        intro.
        apply H.
        eapply (col_transitivity_1 _  C').
          intro.
          subst C'.
          apply cong_symmetry in H7.
          apply cong_identity in H7.
          subst C.
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
      eapply between_exchange3.
        2: apply H6.
      apply between_symmetry.
      assumption.
    split.
      eapply l9_5.
        apply H8.
        2: apply H5.
      apply col_trivial_3.
    repeat split.
      assumption.
      intro.
      apply H.
      apply col_permutation_1.
      assumption.
      intro.
      apply H.
      eapply (col_transitivity_1 _ C').
        intro.
        subst C'.
        unfold two_sides in H8.
        spliter.
        apply H11.
        apply col_trivial_1.
        apply col_permutation_4.
        assumption.
      unfold Col.
      right; right.
      assumption.
    exists A.
    split.
      apply col_trivial_1.
    assumption.
Qed.

Lemma or_bet_out : forall A B C, A <> B -> C <> B -> (Bet A B C \/ out B A C \/ ~Col A B C).
Proof.
    intros.
    induction(Col_dec A B C).
      unfold Col in *.
      decompose [or] H1.
        left.
        assumption.
        right;left.
        apply not_bet_out.
          assumption.
          assumption.
          unfold Col.
          assumption.
        intro.
        assert (Bet C B A) by Between.
        apply H0.
        symmetry.
        apply (between_egality B C A).
          assumption.
        assumption.
      right;left.
      apply not_bet_out.
        assumption.
        assumption.
        unfold Col.
        assumption.
      intro.
      assert (Bet B A C) by Between.
      apply H.
      apply (between_egality A B C).
        assumption.
      assumption.
    right;right.
    assumption.
Qed.

Lemma in_angle_trivial_1 : forall A B C, A <> B -> C <> B -> InAngle A A B C.
Proof.
    intros.
    repeat split.
      assumption.
      assumption.
      assumption.
    exists A.
    split.
      apply between_symmetry.
      apply between_trivial.
    right.
    apply out_trivial.
    auto.
Qed.

Lemma in_angle_trivial_2 : forall A B C, A <> B -> C <> B -> InAngle C A B C.
Proof.
    intros.
    apply l11_24.
    apply in_angle_trivial_1; assumption.
Qed.

Lemma col_out2_col  : forall A B C AA CC, Col A B C -> out B A AA -> out B C CC -> Col AA B CC.
Proof.
    intros.
    induction H.
      assert (Bet AA B CC).
        eapply bet_out_out_bet.
          apply H.
          assumption.
        assumption.
      unfold Col.
      left.
      assumption.
    induction H.
      assert(out B AA CC).
        eapply l6_7.
          eapply l6_6.
          apply H0.
        apply l6_6.
        eapply l6_7.
          apply l6_6.
          apply H1.
        apply bet_out.
          unfold out in *.
          spliter.
          assumption.
          unfold out in *.
          spliter.
          assumption.
        assumption.
      apply col_permutation_4.
      apply out_col.
      assumption.
    assert(out B AA CC).
      eapply l6_6.
      eapply l6_7.
        eapply l6_6.
        apply H1.
      eapply l6_6.
      eapply l6_7.
        eapply l6_6.
        apply H0.
      apply bet_out.
        unfold out in *.
        spliter.
        assumption.
        unfold out in *.
        spliter.
        assumption.
      apply between_symmetry.
      assumption.
    apply col_permutation_4.
    apply out_col.
    assumption.
Qed.

Lemma col_conga_col : forall A B C D E F, Col A B C -> Conga A B C D E F -> Col D E F.
Proof.
    intros.
    induction H.
      assert (Bet D E F).
        eapply bet_conga_bet.
          apply H.
        assumption.
      unfold Col.
      left.
      assumption.
    induction H.
      assert (out E D F).
        eapply l11_21_a.
          2: apply H0.
        apply bet_out in H.
          apply l6_6.
          assumption.
          unfold Conga in H0.
          spliter.
          assumption.
        unfold Conga in H0.
        spliter.
        assumption.
      unfold out in H1.
      spliter.
      unfold Col.
      induction H3.
        right; right.
        apply between_symmetry.
        assumption.
      right; left.
      assumption.
    assert (out E D F).
      eapply l11_21_a.
        2: apply H0.
      apply between_symmetry in H.
      apply bet_out in H.
        assumption.
        unfold Conga in H0.
        spliter.
        assumption.
      unfold Conga in H0.
      spliter.
      assumption.
    unfold out in H1.
    spliter.
    unfold Col.
    induction H3.
      right; right.
      apply between_symmetry.
      assumption.
    right; left.
    assumption.
Qed.

Lemma ncol_conga_ncol : forall A B C D E F, ~Col A B C -> Conga A B C D E F -> ~Col D E F.
Proof.
    intros.
    intro.
    apply H.
    eapply col_conga_col.
      apply H1.
    apply conga_sym.
    assumption.
Qed.


Lemma l11_29_a : forall A B C D E F, lea A B C D E F -> exists Q, InAngle C A B Q /\ Conga A B Q D E F.
Proof.
    intros.
    unfold lea in H.
    ex_and H P.
    assert(E <> D /\ B <> A /\ E <> F /\ E <> P /\ B <> C).
      unfold Conga in *.
      unfold InAngle in H.
      spliter.
      repeat split.
        auto.
        auto.
        auto.
        auto.
      auto.
    spliter.
    assert(A <> B /\ C <> B).
      intuition.
    spliter.
    assert(HH:=or_bet_out A B C H6 H7).
    induction HH.
      assert(Bet D E P).
        eapply bet_conga_bet.
          apply H8.
        assumption.
      exists C.
      split.
        apply in_angle_trivial_2; assumption.
      assert(HH:=H).
      unfold InAngle in HH.
      spliter.
      ex_and H13 X.
      induction H14.
        subst X.
        assert(Bet E F P \/ Bet E P F).
          eapply (l5_2 D).
            auto.
            assumption.
          assumption.
        eapply l11_10.
          apply H0.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          assumption.
        repeat split.
          auto.
          auto.
        assumption.
      assert(out E P F).
        unfold out in H14.
        spliter.
        induction H16.
          assert( Bet D X P).
            eapply between_exchange2.
              apply H9.
            assumption.
          assert(Bet D E X).
            eapply between_inner_transitivity.
              apply H9.
            assumption.
          assert(Bet D E F).
            eapply between_exchange4.
              apply H18.
            assumption.
          unfold out.
          repeat split.
            auto.
            auto.
          eapply l5_2.
            2:apply H9.
            auto.
          assumption.
        assert(Bet D P X).
          eapply outer_transitivity_between2.
            apply H9.
            assumption.
          assumption.
        assert(Bet D P F).
          eapply between_exchange4.
            apply H17.
          assumption.
        assert(Bet E P F).
          eapply between_exchange3.
            apply H9.
          assumption.
        repeat split.
          auto.
          auto.
        left.
        assumption.
      eapply l11_10.
        apply H0.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        apply out_trivial.
        assumption.
      eapply l6_6.
      assumption.
    induction H8.
      assert(exists Q, Conga D E F A B Q).
        apply angle_construction_3.
          auto.
          auto.
        assumption.
      ex_and H9 Q.
      exists Q.
      split.
        repeat split.
          assumption.
          intro.
          subst Q.
          unfold Conga in H10.
          spliter.
          intuition.
          auto.
        (* absurde.
        assumption. *)
        exists A.
        split.
          apply between_trivial2.
        right.
        assumption.
      apply conga_sym.
      assumption.
    assert(D <> E /\ F <> E).
      intuition.
    spliter.
    assert(HH:=or_bet_out D E F H9 H10).
    induction HH.
      prolong A B Q E F.
      exists Q.
      split.
        repeat split.
          assumption.
          intro.
          treat_equalities.
          auto.
          assumption.
        exists B.
        split.
          assumption.
        left.
        reflexivity.
      eapply conga_line.
        repeat split.
          assumption.
          intro.
          treat_equalities.
          auto.
        intro.
        treat_equalities.
        auto.
        repeat split.
          assumption.
          intro.
          treat_equalities.
          auto.
        auto.
        assumption.
      assumption.
    induction H11.
      assert(out E D P).
        eapply in_angle_out.
          apply H11.
        assumption.
      assert (out B A C).
        eapply l11_21_a.
          apply H12.
        apply conga_sym.
        assumption.
      apply False_ind.
      apply H8.
      apply out_col in H13.
      Col.
    (************)
    assert(exists Q, Conga D E F A B Q /\ one_side A B Q C).
      apply angle_construction_1; assumption.
    ex_and H12 Q.
    exists Q.
    assert(exists DD, out E D DD /\ Cong E DD B A).
      eapply segment_construction_3; auto.
    ex_and H14 DD.
    assert(exists FF, out E F FF /\ Cong E FF B Q).
      eapply segment_construction_3.
        auto.
      unfold Conga in H12.
      spliter.
      auto.
    ex_and H16 FF.
    assert(InAngle P DD E FF).
      eapply l11_25.
        apply H.
        apply l6_6.
        assumption.
        apply l6_6.
        assumption.
      apply out_trivial.
      auto.
    assert(HH18:=H18).
    unfold InAngle in H18.
    spliter.
    ex_and H21 X.
    induction H22.
      subst X.
      assert (Bet D E F).
        eapply bet_out_out_bet.
          apply H21.
          apply l6_6.
          assumption.
        apply l6_6.
        assumption.
      apply False_ind.
      apply H11.
      unfold Col.
      left.
      assumption.
    assert(exists CC, out B C CC /\ Cong B CC E X).
      apply segment_construction_3.
        auto.
      unfold out in H22.
      spliter.
      auto.
    ex_and H23 CC.
    assert (Conga A B CC DD E X).
      eapply l11_10.
        apply H0.
        apply out_trivial.
        auto.
        apply l6_6.
        assumption.
        apply l6_6.
        assumption.
      assumption.
    assert(Cong A CC DD X).
      eapply cong2_conga_cong.
        apply H25.
        apply cong_symmetry.
        apply cong_commutativity.
        assumption.
      assumption.
    assert(Conga A B Q DD E FF).
      eapply l11_10.
        apply conga_sym.
        apply H12.
        apply out_trivial.
        auto.
        apply out_trivial.
        intro.
        subst Q.
        apply cong_identity in H17.
        subst FF.
        absurde.
        apply l6_6.
        assumption.
      apply l6_6.
      assumption.
    assert(Cong A Q DD FF).
      eapply cong2_conga_cong.
        apply H27.
        apply cong_symmetry.
        apply cong_commutativity.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Conga CC B Q X E FF).
      eapply (l11_22b _ _ _ A).
      split.
        apply one_side_symmetry.
        eapply out_out_one_side.
          apply invert_one_side.
          apply H13.
        assumption.
      split.
        assert(InAngle X DD E FF).
          eapply l11_25.
            apply HH18.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
          assumption.
        apply in_angle_one_side in H29.
          apply invert_one_side in H29.
          apply H29.
          intro.
          apply H11.
          eapply col_out2_col.
            apply H30.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
        intro.
        apply H8.
        eapply col_conga_col.
          2:apply conga_sym.
          2: apply H0.
        eapply col_out2_col.
          apply col_permutation_4.
          apply H30.
          apply l6_6.
          assumption.
        assumption.
      split.
        apply conga_sym.
        eapply l11_10.
          apply conga_sym.
          apply conga_comm.
          apply H0.
          assumption.
          apply l6_6.
          assumption.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assumption.
    assert(Cong CC Q X FF).
      eapply cong2_conga_cong.
        apply H29.
        apply cong_commutativity.
        assumption.
      apply cong_symmetry.
      assumption.
    split.
      assert(InAngle CC A B Q).
        repeat split.
          assumption.
          intro.
          subst Q.
          unfold Conga in H12.
          spliter.
          absurde.
          intro.
          subst CC.
          unfold Conga in H25.
          spliter.
          auto.
        exists CC.
        split.
          eapply l4_6.
            apply H21.
          repeat split.
            cong.
            cong.
          cong.
        right.
        apply out_trivial.
        unfold out in H23.
        spliter.
        auto.
      eapply l11_25.
        apply H31.
        apply out_trivial.
        auto.
        apply out_trivial.
        unfold Conga in H27.
        spliter.
        auto.
      assumption.
    apply conga_sym.
    assumption.
Qed.

Lemma in_angle_line : forall A B C P, P <> B -> A <> B -> C <> B -> Bet A B C -> InAngle P A B C.
Proof.
    intros.
    repeat split; try assumption.
    exists B.
    split.
      assumption.
    left.
    reflexivity.
Qed.


Lemma l11_29_b : forall A B C D E F, (exists Q, InAngle C A B Q /\ Conga A B Q D E F) -> lea A B C D E F.
Proof.
    intros.
    ex_and H Q.
    unfold lea.
    assert(HH:=H).
    unfold InAngle in HH.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      assert(exists P, Conga A B C D E P).
        apply angle_construction_3.
          assumption.
          assumption.
        unfold Conga in H0.
        spliter.
        assumption.
      ex_and H5 P.
      exists P.
      split.
        assert(Bet D E F).
          eapply bet_conga_bet.
            apply H4.
          assumption.
        apply in_angle_line.
          unfold Conga in H6.
          spliter.
          assumption.
          unfold Conga in H6.
          spliter.
          assumption.
          unfold Conga in H0.
          spliter.
          assumption.
        assumption.
      assumption.
    assert(exists DD, out E D DD /\ Cong E DD B A).
      apply segment_construction_3.
        unfold Conga in H0.
        spliter.
        auto.
      auto.
    ex_and H6 DD.
    assert(exists FF, out E F FF /\ Cong E FF B Q).
      apply segment_construction_3.
        unfold Conga in H0.
        spliter.
        auto.
      auto.
    ex_and H8 FF.
    assert(D <> E /\ DD <> E /\ F <> E /\ FF <> E).
      unfold out in *.
      spliter.
      repeat split; try assumption.
    spliter.
    assert(HI:=or_bet_out A B C H1 H3).
    induction HI.
      exists F.
      split.
        apply in_angle_trivial_2.
          assumption.
        assumption.
      assert(Conga A B C A B Q).
        eapply l11_10.
          apply conga_refl.
            apply H1.
          apply H3.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        unfold out in H5.
        spliter.
        induction H16.
          assert(Bet A B X).
            eapply between_inner_transitivity.
              apply H14.
            assumption.
          assert(Bet B X Q).
            eapply between_exchange3.
              apply H17.
            assumption.
          assert(Bet B Q C \/ Bet B C Q).
            eapply l5_1.
              2:apply H18.
              auto.
            assumption.
          unfold out.
          repeat split.
            assumption.
            assumption.
          assumption.
        assert(Bet A B X).
          eapply outer_transitivity_between.
            apply H14.
            assumption.
          auto.
        assert(Bet B X Q).
          eapply between_exchange3.
            apply H17.
          assumption.
        assert(Bet B C Q).
          eapply between_exchange4.
            apply H16.
          assumption.
        unfold out.
        repeat split.
          assumption.
          assumption.
        right.
        assumption.
      eapply conga_trans.
        apply H15.
      assumption.
    induction H14.
      exists D.
      split.
        apply in_angle_trivial_1.
          assumption.
        assumption.
      assert(Conga A B C A B A).
        eapply l11_10.
          apply conga_refl.
            apply H1.
          apply H3.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        assumption.
      eapply conga_trans.
        apply H15.
      apply conga_trivial_1.
        assumption.
      assumption.
    assert(HJ:=or_bet_out A B Q H1 H2).
    induction HJ.
      assert(exists P, Conga A B C D E P).
        apply angle_construction_3.
          assumption.
          assumption.
        unfold out in H6.
        spliter.
        assumption.
      ex_and H16 P.
      exists P.
      split.
        apply in_angle_line.
          unfold Conga in H17.
          spliter.
          assumption.
          assumption.
          assumption.
        eapply bet_conga_bet.
          apply H15.
        assumption.
      assumption.
    induction H15.
      assert(out B A C).
        eapply out_in_angle_out.
          apply H15.
        assumption.
      apply False_ind.
      apply H14.
      unfold out in H16.
      spliter.
      unfold Col.
      induction H18.
        right; right.
        apply between_symmetry.
        assumption.
      right; left.
      assumption.
    assert(exists P, Conga A B C D E P /\ one_side D E P F).
      eapply angle_construction_1.
        assumption.
      eapply ncol_conga_ncol.
        apply H15.
      apply H0.
    ex_and H16 P.
    exists P.
    split.
      assert(exists PP, out E P PP /\ Cong E PP B X).
        eapply segment_construction_3.
          unfold Conga in H16.
          spliter.
          auto.
        unfold out in H5.
        spliter.
        auto.
      ex_and H18 PP.
      eapply l11_25.
        2:apply H6.
        2:apply H8.
        2:apply H18.
      repeat split.
        assumption.
        assumption.
        unfold out in H18.
        spliter.
        assumption.
      exists PP.
      split.
        assert(Conga C B Q P E F).
          eapply (l11_22b _ _ _ A).
          split.
            apply invert_one_side.
            eapply in_angle_one_side.
              assumption.
              intro.
              apply H14.
              apply col_permutation_4.
              assumption.
            assumption.
          split.
            apply invert_one_side.
            apply H17.
          split.
            apply conga_comm.
            assumption.
          assumption.
        assert (Cong DD FF A Q).
          eapply cong2_conga_cong.
            eapply l11_10.
              apply conga_sym.
              apply H0.
              apply l6_6.
              assumption.
              apply l6_6.
              assumption.
              apply l6_6.
              apply out_trivial.
              auto.
            apply out_trivial.
            auto.
            apply cong_commutativity.
            assumption.
          assumption.
        assert(Cong A X DD PP).
          eapply cong2_conga_cong.
            eapply l11_10.
              apply H16.
              apply out_trivial.
              auto.
              assumption.
              apply l6_6.
              assumption.
            apply l6_6.
            assumption.
            apply cong_symmetry.
            apply cong_commutativity.
            assumption.
          apply cong_symmetry.
          assumption.
        assert(Cong X Q PP FF).
          eapply cong2_conga_cong.
            eapply l11_10.
              apply H20.
              assumption.
              apply out_trivial.
              auto.
              apply l6_6.
              assumption.
            apply l6_6.
            assumption.
            apply cong_symmetry.
            apply cong_commutativity.
            assumption.
          apply cong_symmetry.
          assumption.
        eapply l4_6.
          apply H4.
        repeat split.
          assumption.
          apply cong_symmetry.
          assumption.
        assumption.
      right.
      apply out_trivial.
      unfold out in H15.
      spliter.
      unfold out in H18.
      spliter.
      auto.
    assumption.
Qed.

Lemma bet_in_angle_bet : forall A B C P, Bet A B P -> InAngle P A B C -> Bet A B C.
Proof.
    intros.
    unfold InAngle in H0.
    spliter.
    ex_and H3 X.
    induction H4.
      subst X.
      assumption.
    unfold out in H4.
    spliter.
    induction H6.
      assert(Bet A X P).
        eapply between_exchange2.
          apply H.
        assumption.
      assert(Bet A P C \/ Bet A C P).
        eapply (l5_1 _ X).
          intro.
          subst X.
          assert(A = B).
            eapply between_egality.
              apply H.
            assumption.
          contradiction.
          assumption.
        assumption.
      induction H8.
        eapply between_exchange4.
          apply H.
        assumption.
      assert(Bet A B X).
        eapply between_inner_transitivity.
          apply H.
        assumption.
      eapply between_exchange4.
        apply H9.
      assumption.
    assert(Bet A B X).
      eapply outer_transitivity_between.
        apply H.
        assumption.
      auto.
    eapply between_exchange4.
      apply H7.
    assumption.
Qed.

Lemma lea_line : forall A B C P, Bet A B P -> lea A B P A B C -> Bet A B C.
Proof.
    intros.
    unfold lea in H0.
    ex_and H0 PP.
    assert (HH:=H0).
    unfold InAngle in H0.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      assumption.
    assert (Bet A B PP).
      eapply bet_conga_bet.
        apply H.
      assumption.
    eapply bet_in_angle_bet.
      apply H6.
    assumption.
Qed.

Lemma bet2_out_out : forall A B C B' C', B <> A -> B' <> A -> out A C C' -> Bet A B C -> Bet A B' C' -> out A B B'.
Proof.
    intros.
    induction(eq_dec_points B' C').
      subst C'.
      unfold out in *.
      spliter.
      repeat split; try assumption.
      induction H5.
        left.
        eapply between_exchange4.
          apply H2.
        assumption.
      eapply l5_3.
        apply H2.
      assumption.
    unfold out in *.
    spliter.
    repeat split.
      assumption.
      assumption.
    induction H6.
      assert(Bet A B C').
        eapply between_exchange4.
          apply H2.
        assumption.
      eapply l5_3.
        apply H7.
      assumption.
    assert(Bet B' C' C).
      eapply between_exchange3.
        apply H3.
      assumption.
    assert(Bet A B' C).
      eapply outer_transitivity_between.
        apply H3.
        assumption.
      assumption.
    eapply l5_3.
      apply H2.
    assumption.
Qed.

Lemma eq_conga_out : forall A B D E F, Conga A B A D E F -> out E D F.
Proof.
    intros.
    assert(HH:=H).
    unfold Conga in H.
    spliter.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H3 D'.
    ex_and H4 F'.
    assert(Cong_3 B A' C' E D' F').
      repeat split.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H3.
          apply between_symmetry.
          apply H7.
          apply cong_right_commutativity.
          apply cong_symmetry.
          assumption.
        apply cong_right_commutativity.
        assumption.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H5.
          apply between_symmetry.
          apply H9.
          apply cong_right_commutativity.
          apply cong_symmetry.
          assumption.
        apply cong_right_commutativity.
        assumption.
      assumption.
    assert(out E D' F').
      eapply cong3_preserves_out.
        2:apply H12.
      unfold out.
      repeat split.
        intro.
        subst A'.
        apply between_identity in H3.
        subst A.
        absurde.
        intro.
        subst C'.
        apply between_identity in H5.
        subst A.
        absurde.
      eapply l5_1.
        2:apply H3.
        auto.
      assumption.
    eapply bet2_out_out.
      assumption.
      assumption.
      apply H13.
      assumption.
    assumption.
Qed.

Lemma out_conga_out : forall A B C D E F, out B A C -> Conga A B C D E F -> out E D F.
Proof.
    intros.
    assert(HH:=H).
    unfold out in H.
    spliter.
    assert(D <> E /\ F <> E).
      unfold Conga in H0.
      spliter.
      split; assumption.
    spliter.
    assert(Conga A B A A B C).
      eapply l11_10.
        apply conga_refl.
          apply H.
        apply H1.
        apply out_trivial.
        auto.
        assumption.
        apply out_trivial.
        auto.
      apply out_trivial.
      auto.
    assert(Conga A B A D E F).
      eapply conga_trans.
        apply H5.
      assumption.
    eapply eq_conga_out.
    apply H6.
Qed.

Lemma conga_ex_cong3 : forall A B C A' B' C',
            Conga A B C A' B' C' -> exists AA, exists CC, out B A AA -> out B C CC -> Cong_3 AA B CC A' B' C'.
Proof.
    intros.
    assert(B <> A /\ B <> C /\ B' <> A' /\ B' <> C').
      unfold Conga in H.
      spliter.
      repeat split; auto.
    spliter.
    assert(exists AA, out B A AA /\ Cong B AA B' A').
      apply segment_construction_3; assumption.
    assert(exists CC, out B C CC /\ Cong B CC B' C').
      apply segment_construction_3; assumption.
    ex_and H4 AA.
    ex_and H5 CC.
    exists AA.
    exists CC.
    intros.
    repeat split.
      apply cong_commutativity.
      assumption.
      eapply cong2_conga_cong.
        eapply l11_10.
          apply H.
          apply l6_6.
          assumption.
          apply l6_6.
          assumption.
          apply out_trivial.
          auto.
        apply out_trivial.
        auto.
        Cong.
      assumption.
    assumption.
Qed.

Lemma conga_preserves_in_angle : forall A B C I A' B' C' I',
 Conga A B C A' B' C' -> Conga A B I A' B' I' ->
 InAngle I A B C -> one_side A' B' I' C' ->
 InAngle I' A' B' C'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B' /\ I <> B /\ I' <> B').
      unfold Conga in *.
      spliter.
      repeat split; assumption.
    spliter.
    assert(HH1:= or_bet_out A B C H3 H4).
    induction HH1.
      assert(Bet A' B' C').
        eapply bet_conga_bet.
          apply H9.
        assumption.
      apply in_angle_line; assumption.
    induction H9.
      assert(out B A I).
        eapply out_in_angle_out.
          apply H9.
        assumption.
      assert(out B' A' I').
        eapply out_conga_out.
          apply H10.
        assumption.
      apply out_in_angle.
        eapply out_conga_out.
          apply H9.
        assumption.
      apply l6_6.
      assumption.
    assert(HH2:= or_bet_out A B I H3 H7).
    induction HH2.
      assert(Bet A B C).
        eapply bet_in_angle_bet.
          apply H10.
        assumption.
      apply False_ind.
      apply H9.
      unfold Col.
      left.
      assumption.
    induction H10.
      assert(out B' A' I').
        eapply out_conga_out.
          apply H10.
        assumption.
      eapply col_in_angle; try assumption.
      left.
      assumption.
    (*****************************)
    assert(exists AA', out B' A' AA' /\ Cong B' AA' B A).
      apply segment_construction_3; auto.
    assert(exists CC', out B' C' CC' /\ Cong B' CC' B C).
      apply segment_construction_3; auto.
    ex_and H11 AA'.
    ex_and H12 CC'.
    assert(HH:=H1).
    unfold InAngle in H1.
    spliter.
    ex_and H17 J.
    induction H18.
      subst J.
      eapply in_angle_line; try assumption.
      eapply bet_conga_bet.
        apply H17.
      assumption.
    assert(B <> J).
      unfold out in H18.
      spliter.
      auto.
    assert(~Col A B J).
      intro.
      apply H10.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ J).
        assumption.
        apply out_col.
        assumption.
      apply col_permutation_1.
      assumption.
    assert(exists J', Conga A B J  A' B' J' /\ one_side A' B' J' I').
      apply angle_construction_1.
        intro.
        apply H10.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ J).
          unfold out in H18.
          spliter.
          auto.
          apply out_col.
          assumption.
        apply col_permutation_1.
        assumption.
      eapply ncol_conga_ncol.
        apply H10.
      assumption.
    ex_and H21 J'.
    assert(B' <> J').
      unfold Conga in H21.
      spliter.
      auto.
    assert(exists JJ', out B' J' JJ' /\ Cong B' JJ' B J).
      apply segment_construction_3.
        assumption.
      assumption.
    ex_and H24 JJ'.
    assert(~Col A' B' J').
      intro.
      apply H20.
      eapply col_conga_col.
        apply H26.
      apply conga_sym.
      assumption.
    assert(A' <> JJ').
      intro.
      subst JJ'.
      apply H20.
      eapply col_conga_col.
        apply out_col in H24.
        apply col_permutation_2.
        apply H24.
      apply conga_sym.
      assumption.
    assert(B' <> JJ').
      unfold out in H24.
      spliter.
      auto.
    assert(~Col A' B' JJ').
      intro.
      apply H26.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ JJ').
        assumption.
        apply col_permutation_5.
        apply out_col.
        assumption.
      apply col_permutation_1.
      assumption.
    (****************************************************************)
    assert(Conga A B C AA' B' CC').
      eapply l11_10.
        apply H.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        apply l6_6.
        assumption.
      apply l6_6.
      assumption.
    assert(Conga A' B' J' A' B' JJ').
      eapply l11_10.
        apply conga_refl.
          apply H5.
        3: apply H24.
        auto.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
      apply out_trivial.
      auto.
    assert(out B' I' JJ' \/ two_sides A' B' I' JJ').
      apply l11_22_aux.
      eapply conga_trans.
        apply conga_sym.
        apply H0.
      apply conga_sym.
      eapply conga_trans.
        apply conga_sym.
        apply H31.
      eapply conga_trans.
        apply conga_sym.
        apply H21.
      eapply l11_10.
        apply (conga_refl A B I).
          assumption.
        assumption.
        apply out_trivial.
        auto.
        assumption.
        apply out_trivial.
        auto.
      apply out_trivial.
      auto.
    induction H32.
      assert(Conga J B C J' B' C').
        eapply (l11_22b _ _ _ A _ _ _ A').
        split.
          apply invert_one_side.
          apply in_angle_one_side.
            assumption.
            intro.
            apply H10.
            apply col_permutation_2.
            eapply (col_transitivity_1 _ J).
              assumption.
              apply out_col.
              assumption.
            apply col_permutation_5.
            assumption.
          eapply l11_25.
            apply HH.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
          assumption.
        split.
          eapply one_side_transitivity.
            2:apply invert_one_side.
            2:apply H2.
          apply invert_one_side.
          assumption.
        split.
          apply conga_comm.
          assumption.
        assumption.
      assert(Cong A C AA' CC').
        eapply cong2_conga_cong.
          eapply l11_10.
            apply H.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong A J AA' JJ').
        eapply cong2_conga_cong.
          eapply l11_10.
            apply H0.
            apply out_trivial.
            auto.
            assumption.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Conga J' B' C' JJ' B' CC').
        eapply l11_10.
          apply conga_refl.
            4:apply H12.
          3:apply H24.
          auto.
          unfold Conga in H30.
          spliter.
          assumption.
          apply out_trivial.
          auto.
        apply out_trivial.
        unfold Conga in H30.
        spliter.
        auto.
      assert(Cong J C JJ' CC').
        eapply (cong2_conga_cong).
          eapply conga_trans.
            apply H33.
          apply H36.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Bet AA' JJ' CC').
        eapply l4_6.
          apply H17.
        repeat split.
          assumption.
          assumption.
        assumption.
      eapply l11_25.
        2: apply H11.
        2: apply H12.
        unfold InAngle.
        repeat split; try assumption.
          unfold out in H11.
          spliter.
          assumption.
          unfold out in H12.
          spliter.
          assumption.
          3:apply H32.
        auto.
      exists JJ'.
      split.
        assumption.
      right.
      apply out_trivial.
      auto.
    assert(one_side B' A' I' JJ').
      eapply out_out_one_side.
        apply invert_one_side.
        apply one_side_symmetry.
        apply H22.
      assumption.
    apply invert_two_sides in H32.
    apply l9_9 in H32.
    contradiction.
Qed.


Lemma l11_30 : forall A B C D E F A' B' C' D' E' F',
 lea A B C D E F ->
 Conga A B C A' B' C' ->
 Conga D E F D' E' F' ->
 lea A' B' C' D' E' F'.
Proof.
    intros.
    assert(HH:=H).
    apply l11_29_a in H.
    ex_and H Q.
    apply l11_29_b.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B' /\ D <> E /\ F <> E /\ D' <> E' /\ F' <> E').
      unfold Conga in *.
      spliter.
      repeat split; assumption.
    spliter.
    assert(Hi:=or_bet_out A' B' C' H5 H6).
    induction Hi.
      prolong A' B' Q' A' B'.
      exists Q'.
      assert(B' <> Q').
        intro.
        subst Q'.
        apply cong_symmetry in H13.
        apply cong_identity in H13.
        contradiction.
      assert(A' <> Q').
        intro.
        subst Q'.
        apply between_identity in H12.
        contradiction.
      assert(Conga A' B' Q' A' B' C').
        apply conga_line.
          repeat split; try assumption.
          repeat split ; try assumption.
            intro.
            subst C'.
            apply between_identity in H11.
            contradiction.
          auto.
          assumption.
        assumption.
      split.
        apply in_angle_line; try assumption.
        auto.
      assert(Bet A B C).
        eapply bet_conga_bet.
          apply H11.
        apply conga_sym.
        assumption.
      assert(Bet A B Q).
        eapply lea_line.
          apply H17.
        apply l11_29_b.
        exists Q.
        split.
          assumption.
        apply conga_refl.
          assumption.
        unfold Conga in H2.
        spliter.
        assumption.
      assert(Bet D E F).
        eapply bet_conga_bet.
          apply H18.
        assumption.
      assert (Bet D' E' F').
        eapply bet_conga_bet.
          apply H19.
        assumption.
      eapply conga_line.
        repeat split; try assumption.
        repeat split; try assumption.
          intro.
          subst F'.
          apply between_identity in H20.
          contradiction.
        auto.
        assumption.
      assumption.
    (************************)
    induction H11.
      assert(exists Q', Conga D' E' F' A' B' Q').
        eapply angle_construction_3; assumption.
      ex_and H12 Q'.
      exists Q'.
      split.
        apply col_in_angle; try assumption.
          unfold Conga in H13.
          spliter.
          assumption.
        left.
        assumption.
      apply conga_sym.
      assumption.
    assert(Hi:=or_bet_out D' E' F' H9 H10).
    induction Hi.
      assert(exists Q', Conga  D' E' F' A' B' Q').
        eapply angle_construction_3; try assumption.
      ex_and H13 Q'.
      exists Q'.
      assert(Bet A' B' Q').
        eapply bet_conga_bet.
          apply H12.
        assumption.
      split.
        apply in_angle_line; try assumption.
        unfold Conga in H14.
        spliter.
        assumption.
      apply conga_sym.
      assumption.
    induction H12.
      assert(exists Q', Conga  D' E' F' A' B' Q').
        eapply angle_construction_3; try assumption.
      ex_and H13 Q'.
      exists Q'.
      assert(out B' A' Q').
        eapply out_conga_out.
          apply H12.
        assumption.
      assert(Conga A B Q D' E' F').
        eapply conga_trans.
          apply H2.
        assumption.
      assert(out B A Q).
        eapply out_conga_out.
          apply H12.
        apply conga_sym.
        assumption.
      assert(out B A C).
        eapply out_in_angle_out.
          apply H16.
        assumption.
      assert(out  B' A' C').
        eapply out_conga_out.
          apply H17.
        assumption.
      split.
        eapply out_in_angle.
          assumption.
        apply l6_6.
        assumption.
      apply conga_sym.
      assumption.
    assert(exists QQ, Conga D' E' F' A' B' QQ /\ one_side A' B' QQ C').
      eapply angle_construction_1.
        assumption.
      assumption.
    ex_and H13 Q'.
    exists Q'.
    split.
      eapply conga_preserves_in_angle.
        3: apply H.
        eapply conga_trans.
          apply H2.
        eapply conga_trans.
          apply H1.
        assumption.
        apply H0.
      (************** etrange ****************)
      try assumption.
      apply one_side_symmetry.
      assumption.
    apply conga_sym.
    assumption.
Qed.



Lemma l11_31_1 : forall A B C D E F,
 out B A C -> D <> E -> F <> E ->
 lea A B C D E F.
Proof.
    intros.
    unfold lea.
    exists D.
    split.
      apply in_angle_trivial_1; assumption.
    apply l11_21_b.
      assumption.
    apply out_trivial.
    auto.
Qed.


Lemma l11_31_2 : forall A B C D E F,
 A <> B -> C <> B -> D <> E -> F <> E ->
 Bet D E F ->
 lea A B C D E F.
Proof.
    intros.
    unfold lea.
    assert(exists P, Conga A B C D E P).
      apply angle_construction_3; assumption.
    ex_and H4 P.
    exists P.
    split.
      apply in_angle_line.
        unfold Conga in H5.
        spliter.
        assumption.
        assumption.
        assumption.
      assumption.
    assumption.
Qed.

Lemma lea_refl : forall A B C,
 A <> B -> C <> B -> lea A B C A B C.
Proof.
    intros.
    unfold lea.
    exists C .
    split.
      apply in_angle_trivial_2; assumption.
    apply conga_refl; assumption.
Qed.

Lemma in_angle_trans : forall A B C D E,
 InAngle C A B D -> InAngle D A B E -> InAngle C A B E.
Proof.
    intros.
    assert(HA1 :=H).
    assert(HA2:= H0).
    unfold InAngle in H.
    unfold InAngle in H0.
    spliter.
    ex_and H3 DD.
    ex_and H6 CC.
    induction H8; induction H7.
      subst CC.
      subst DD.
      apply in_angle_line; assumption.
      subst CC.
      assert(Bet A B E).
        eapply bet_in_angle_bet.
          apply H6.
        assumption.
      apply in_angle_line; assumption.
      subst DD.
      apply in_angle_line; assumption.
    assert(InAngle C A B DD).
      eapply l11_25.
        apply HA1.
        apply out_trivial.
        auto.
        assumption.
      apply out_trivial.
      auto.
    unfold InAngle in H9.
    spliter.
    ex_and H12 CC'.
    induction H13.
      subst CC'.
      assert(Bet A B E).
        eapply between_exchange4.
          apply H12.
        assumption.
      apply in_angle_line; assumption.
    eapply l11_25.
      4: apply l6_6.
      4:apply H13.
      2: apply out_trivial.
      3: apply out_trivial.
      unfold InAngle.
      repeat split; try assumption.
        unfold out in H13.
        spliter.
        assumption.
      exists CC'.
      split.
        eapply between_exchange4.
          apply H12.
        assumption.
      right.
      apply out_trivial.
      unfold out in H13.
      spliter.
      auto.
      auto.
    auto.
Qed.

Lemma lea_trans : forall A B C A1 B1 C1 A2 B2 C2,
 lea A B C A1 B1 C1 ->
 lea A1 B1 C1 A2 B2 C2 ->
 lea A B C A2 B2 C2.
Proof.
    intros.
    assert(Hlea1 := H).
    assert (Hlea2 := H0).
    unfold lea in H.
    unfold lea in H0.
    ex_and H P1.
    ex_and H0 P2.
    assert( A <> B /\ C <> B /\ A1 <> B1 /\ C1 <> B1 /\ A2 <> B2 /\ C2 <> B2).
      unfold Conga in *.
      unfold InAngle in H0.
      spliter.
      repeat split; assumption.
    spliter.
    assert(HH1 := or_bet_out A B C H3 H4).
    induction HH1.
      assert(Bet A1 B1 P1).
        eapply bet_conga_bet.
          apply H9.
        assumption.
      assert(Bet A1 B1 C1).
        eapply bet_in_angle_bet.
          apply H10.
        assumption.
      assert(Bet A2 B2 P2).
        eapply bet_conga_bet.
          apply H11.
        assumption.
      assert(Bet A2 B2 C2).
        eapply bet_in_angle_bet.
          apply H12.
        assumption.
      apply l11_31_2; assumption.
    induction H9.
      apply l11_31_1; assumption.
    assert(HH2 := or_bet_out A2 B2 C2 H7 H8).
    induction HH2.
      apply l11_31_2; assumption.
    induction H10.
      assert(out B2 A2 P2).
        eapply in_angle_out.
          apply H10.
        assumption.
      assert(out B1 A1 C1).
        eapply out_conga_out.
          apply H11.
        apply conga_sym.
        assumption.
      assert(out B1 A1 P1).
        eapply in_angle_out.
          apply H12.
        assumption.
      assert(out B A C).
        eapply out_conga_out.
          apply H13.
        apply conga_sym.
        assumption.
      apply l11_31_1; assumption.
    assert(exists P, Conga A B C A2 B2 P /\ one_side A2 B2 P C2).
      apply angle_construction_1; assumption.
    ex_and H11 P.
    assert (one_side A2 B2 P2 C2).
      apply in_angle_one_side.
        assumption.
        assert (B2 <> A2).
          auto.
        assert(P2 <> A2).
          intro.
          subst P2.
          assert(out B1 A1 C1).
            eapply out_conga_out.
              2: apply conga_sym.
              2:apply H2.
            apply out_trivial.
            assumption.
          assert(out B1 A1 P1).
            eapply out_in_angle_out.
              apply H14.
            assumption.
          assert(out B A C).
            eapply out_conga_out.
              apply H15.
            apply conga_sym.
            assumption.
          apply H9.
          apply out_col in H16.
          apply col_permutation_4.
          assumption.
        assert(HH:=or_bet_out A2 B2 P2 ).
        induction HH.
          assert (Bet A2 B2 C2).
            eapply bet_in_angle_bet.
              apply H15.
            apply H0.
          intro.
          apply H10.
          unfold Col.
          left.
          assumption.
          induction H15.
            assert(out B1 A1 C1).
              eapply out_conga_out.
                apply H15.
              apply conga_sym.
              assumption.
            assert( out B1 A1 P1).
              eapply in_angle_out.
                apply H16.
              assumption.
            assert (out B A C).
              eapply out_conga_out.
                apply H17.
              apply conga_sym.
              assumption.
            apply False_ind.
            apply H9.
            apply out_col in H18.
            apply col_permutation_4.
            assumption.
          intro.
          apply H15.
          apply col_permutation_4.
          assumption.
          assumption.
        unfold Conga in H2.
        spliter.
        assumption.
      assumption.
    assert(one_side A2 B2 P P2).
      eapply one_side_transitivity.
        apply H12; eapply out_conga_out.
      apply one_side_symmetry.
      assumption.
    unfold lea.
    exists P.
    split.
      eapply (in_angle_trans _ _ _ P2).
        eapply conga_preserves_in_angle.
          apply H2.
          2: apply H.
          eapply conga_trans.
            apply conga_sym.
            apply H1.
          assumption.
        assumption.
      assumption.
    assumption.
Qed.

Lemma out2_out_1 : forall B C D X,
 out B X C -> out B X D -> out B C D.
Proof.
    intros.
    unfold out in *.
    spliter.
    repeat split.
      assumption.
      assumption.
    induction H2; induction H4.
      eapply l5_1.
        2: apply H4.
        auto.
      assumption.
      left.
      eapply between_exchange4.
        apply H4.
      assumption.
      right.
      eapply between_exchange4.
        apply H2.
      assumption.
    eapply l5_3.
      apply H4.
    apply H2.
Qed.

Lemma out2_out_2 : forall B C D X,
 out B C X -> out B D X -> out B C D.
Proof.
    intros.
    eapply out2_out_1.
      apply l6_6.
      apply H.
    apply l6_6.
    assumption.
Qed.

Lemma out_bet_out_1 : forall A B C P,
 out P A C -> Bet A B C -> out P A B.
Proof.
    intros.
    induction (eq_dec_points B P).
      subst P.
      apply False_ind.
      apply (not_bet_and_out A B C).
      split; assumption.
    unfold out in *.
    spliter.
    repeat split.
      assumption.
      assumption.
    induction H3.
      left.
      eapply between_inner_transitivity.
        apply H3.
      assumption.
    right.
    eapply between_exchange2.
      apply H3.
    apply between_symmetry.
    assumption.
Qed.

Lemma out_bet_out_2 : forall A B C P,
 out P A C -> Bet A B C -> out P B C.
Proof.
    intros.
    apply l6_6.
    eapply out_bet_out_1.
      apply l6_6.
      apply H.
    apply between_symmetry.
    assumption.
Qed.


Lemma in_angle_asym : forall A B C D,
 InAngle D A B C -> InAngle C A B D -> Conga A B C A B D.
Proof.
    intros.
    unfold InAngle in *.
    spliter.
    ex_and H3 CC.
    ex_and H6 DD.
    induction H7; induction H8.
      subst DD.
      subst CC.
      apply conga_line.
        repeat split.
          assumption.
          intro.
          subst C.
          apply between_identity in H6.
          contradiction.
        auto.
        repeat split.
          assumption.
          intro.
          subst D.
          apply between_identity in H3.
          contradiction.
        auto.
        assumption.
      assumption.
      subst CC.
      unfold out in H8.
      spliter.
      induction H9.
        assert(Bet A B C).
          eapply between_exchange4.
            2: apply H6.
          eapply between_inner_transitivity.
            apply H3.
          assumption.
        apply conga_line.
          repeat split.
            assumption.
            intro.
            subst C.
            apply between_identity in H10.
            contradiction.
          auto.
          repeat split.
            assumption.
            intro.
            subst D.
            apply between_identity in H3.
            contradiction.
          auto; apply H9.
          assumption.
        assumption.
      assert(Bet A B C).
        eapply between_exchange4.
          eapply outer_transitivity_between.
            apply H3.
            apply H9.
          auto.
        assumption.
      apply conga_line.
        repeat split.
          assumption.
          intro.
          subst C.
          apply between_identity in H10.
          contradiction.
        auto.
        repeat split.
          assumption.
          intro.
          subst D.
          apply between_identity in H3.
          contradiction.
        auto.
        assumption.
      assumption.
      subst DD.
      assert(Bet A B D).
        unfold out in H7.
        spliter.
        induction H9.
          eapply between_exchange4.
            eapply between_inner_transitivity.
              apply H6.
            apply H9.
          assumption.
        eapply between_exchange4.
          eapply outer_transitivity_between.
            apply H6.
            apply H9.
          auto.
        assumption.
      apply conga_line.
        repeat split.
          assumption.
          intro.
          subst C.
          apply between_identity in H6.
          contradiction.
        auto.
        repeat split.
          assumption.
          intro.
          subst D.
          apply between_identity in H8.
          contradiction.
        auto.
        assumption.
      assumption.
    assert(exists B', Bet CC B' C /\ Bet DD B' D).
      eapply inner_pasch.
        apply between_symmetry.
        apply H3.
      apply between_symmetry.
      assumption.
    ex_and H9 X.
    assert (out B X C).
      eapply out_bet_out_2.
        apply H7.
      assumption.
    assert(out B X D).
      eapply out_bet_out_2.
        apply H8.
      assumption.
    assert (out B C D).
      eapply out2_out_1.
        apply H11.
      assumption.
    eapply l11_10.
      apply conga_refl.
        4:apply H13.
      3: apply out_trivial.
      assumption.
      assumption; apply H7.
      auto.
      apply out_trivial.
      auto.
    apply out_trivial.
    auto.
Qed.


Lemma lea_asym : forall A B C D E F,
 lea A B C D E F -> lea D E F A B C -> Conga A B C D E F.
Proof.
    intros.
    apply l11_29_a in H.
    unfold lea in *.
    ex_and H Q.
    ex_and H0 P.
    assert(A <> B /\ Q <> B /\ P <> B /\ D <> E /\ F <> E).
      unfold Conga in *.
      spliter.
      repeat split; assumption.
    spliter.
    assert(Conga A B Q A B P).
      eapply conga_trans.
        apply H1.
      assumption.
    assert(HH1:= or_bet_out A B Q H3 H4).
    induction HH1.
      assert(Bet A B P).
        eapply bet_conga_bet.
          apply H9.
        assumption.
      assert(Bet A B C).
        eapply bet_in_angle_bet.
          apply H10.
        assumption.
      assert(Bet D E F).
        eapply bet_conga_bet.
          apply H9.
        assumption.
      eapply conga_line.
        repeat split.
          assumption.
          intro.
          subst C.
          apply between_identity in H11.
          contradiction.
        unfold InAngle in H0.
        spliter.
        auto.
        repeat split.
          assumption.
          intro.
          subst F.
          apply between_identity in H12.
          contradiction.
        auto.
        assumption.
      assumption.
    induction H9.
      assert(out E D F).
        eapply out_conga_out.
          apply H9.
        assumption.
      assert(out B A P).
        eapply out_conga_out.
          apply H10.
        apply H2.
      assert(out B A C).
        eapply in_angle_out.
          apply H9.
        assumption.
      eapply l11_21_b.
        assumption.
      assumption.
    assert(HH2:= or_bet_out A B P H3 H5).
    induction HH2.
      assert(Bet A B C).
        eapply bet_in_angle_bet.
          apply H10.
        assumption.
      assert(Bet D E F).
        eapply bet_conga_bet.
          apply H10.
        apply conga_sym.
        assumption.
      apply conga_line.
        repeat split.
          assumption.
          intro.
          subst C.
          apply between_identity in H11.
          contradiction.
        unfold InAngle in H0.
        spliter.
        auto.
        repeat split.
          assumption.
          intro.
          subst F.
          apply between_identity in H12.
          contradiction.
        auto.
        assumption.
      assumption.
    induction H10.
      assert(out B A Q).
        eapply out_conga_out.
          apply H10.
        apply conga_sym.
        assumption.
      assert (out B A C).
        eapply in_angle_out.
          apply H11.
        assumption.
      assert(out E D F).
        eapply out_conga_out.
          apply H11.
        assumption.
      apply l11_21_b.
        assumption.
      assumption.
    assert(out B P Q \/ two_sides A B P Q).
      apply l11_22_aux.
      apply conga_sym.
      assumption.
    induction H11.
      assert(InAngle C A B P).
        eapply l11_25.
          3: apply H11.
          apply H.
          apply out_trivial.
          auto.
        apply out_trivial.
        intro.
        subst C.
        unfold InAngle in H0.
        spliter.
        absurde.
      assert(Conga A B C A B P).
        apply in_angle_asym; assumption.
      eapply conga_trans.
        apply H13.
      eapply conga_trans.
        apply conga_sym.
        apply H8.
      assumption.
    assert(C <> B).
      unfold InAngle in H0.
      spliter.
      assumption.
    assert(HH:=or_bet_out A B C H3 H12).
    induction HH.
      assert(Bet A B Q).
        eapply bet_in_angle_bet.
          apply H13.
        apply H.
      apply False_ind.
      apply H9.
      unfold Col.
      left.
      assumption.
    induction H13.
      assert(out B A P).
        eapply in_angle_out.
          apply H13.
        assumption.
      apply False_ind.
      apply H10.
      apply out_col in H14.
      apply col_permutation_4.
      assumption.
    apply in_angle_one_side in H.
      apply in_angle_one_side in H0.
        assert(one_side A B P Q).
          eapply one_side_transitivity.
            apply H0.
          assumption.
        apply l9_9 in H14.
          contradiction.
        assumption.
        assumption.
      intro.
      apply H10.
      apply col_permutation_4.
      assumption.
      assumption.
    intro.
    apply H13.
    apply col_permutation_4.
    assumption.
Qed.

Lemma two_sides_in_angle : forall A B C P P',
 B <> P' ->
 two_sides B P A C ->
 Bet P B P' ->
 InAngle P A B C \/ InAngle P' A B C.
Proof.
    intros.
    unfold two_sides in H0.
    spliter.
    ex_and H4 T.
    assert(A <> B).
      intro.
      subst A.
      apply H2.
      apply col_trivial_1.
    assert(C <> B).
      intro.
      subst C.
      apply H3.
      apply col_trivial_1.
    induction (eq_dec_points B T).
      subst T.
      left.
      repeat split.
        assumption.
        assumption.
        auto.
      exists B.
      split.
        assumption.
      left.
      reflexivity.
    assert(P <> B /\ T <> B).
      auto.
    spliter.
    assert(HH:= or_bet_out P B T H9 H10).
    induction HH.
      right.
      unfold InAngle.
      repeat split; try assumption.
        unfold out in H1.
        spliter.
        auto.
      exists T.
      split.
        assumption.
      right.
      unfold out.
      repeat split.
        auto.
        auto.
      eapply l5_2.
        2:apply H11.
        auto.
      assumption.
    induction H11.
      left.
      unfold InAngle.
      repeat split; try assumption.
      auto.
      exists T.
      split.
        assumption.
      right.
      apply l6_6.
      assumption.
    apply col_permutation_3 in H4.
    contradiction.
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
          eapply between_egality.
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
          eapply between_egality.
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

Lemma col_perp_perp_col :
 forall A B X Y P,
  P <> A ->
  Col A B P ->
  Perp A B X P ->
  Perp P A Y P ->
  Col Y X P.
Proof.
    intros.
    eapply per_per_col.
      apply perp_in_per.
      apply perp_in_sym.
      apply perp_perp_in.
      apply H2.
      assumption.
    apply perp_in_per.
    apply perp_in_sym.
    apply perp_perp_in.
    apply perp_left_comm.
    eapply perp_col.
      auto.
      apply H1.
    assumption.
Qed.

Lemma out_two_sides_two_sides :
 forall A B X Y P PX,
  A <> PX ->
  Col A B PX ->
  out PX X P ->
  two_sides A B P Y ->
  two_sides A B X Y.
Proof.
    intros.
    assert(one_side A B P X).
      eapply (col_one_side _ PX).
        Col.
        unfold two_sides in H2.
        spliter.
        auto.
      apply invert_one_side.
      apply out_one_side.
        left.
        intro.
        unfold two_sides in H2.
        spliter.
        apply H4.
        ColR.
      apply l6_6.
      assumption.
    eapply l9_8_2.
      apply H2.
    assumption.
Qed.

Lemma not_two_sides_one_side_aux :
 forall A B X Y PX,
  A <> B -> PX <> A ->
  Perp A B X PX ->
  Col A B PX ->
  ~ Col X A B ->
  ~ Col Y A B ->
  ~ two_sides A B X Y ->
  one_side A B X Y.
Proof.
    intros.
    assert(exists P, exists T, Perp PX A P PX /\ Col PX A T /\ Bet Y T P).
      apply l8_21.
      assumption.
    ex_elim H6 P.
    ex_and H7 T.
    assert(HH:= col_perp_perp_col A B X P PX H0 H2 H1 H6).
    assert(~Col P A B).
      apply perp_not_col in H6.
      intro.
      apply H6.
      ColR.
    assert(two_sides PX A P Y).
      repeat split.
        assumption.
        intro.
        apply H9.
        ColR.
        intro.
        apply H4.
        ColR.
      exists T.
      split.
        apply col_permutation_2.
        assumption.
      apply between_symmetry.
      assumption.
    assert(X <> PX).
      apply perp_not_eq_2 in H1.
      assumption.
    assert(P <> PX).
      apply perp_not_eq_2 in H6.
      assumption.
    assert(HA:= (or_bet_out X PX P H11 H12)).
    induction HA.
      assert(two_sides PX A P X).
        repeat split; try assumption.
          intro.
          apply H9.
          ColR.
          intro.
          apply H3.
          ColR.
        exists PX.
        split.
          apply col_trivial_1.
        apply between_symmetry.
        assumption.
      eapply l9_8_1.
        apply l9_2.
        eapply (col_two_sides _ PX).
          apply col_permutation_5.
          assumption.
          assumption.
        apply invert_two_sides.
        apply H14.
      eapply (col_two_sides _ PX).
        apply col_permutation_5.
        assumption.
        assumption.
      apply invert_two_sides.
      apply l9_2.
      assumption.
    induction H13.
      assert(two_sides A B P Y).
        eapply (col_two_sides _ PX).
          Col.
          assumption.
        apply  invert_two_sides.
        assumption.
      assert(HO:= out_two_sides_two_sides A B X Y P PX (sym_not_eq H0) H2 H13 H14).
      contradiction.
    apply col_permutation_1 in HH.
    contradiction.
Qed.

Lemma not_two_sides_one_side :
 forall A B X Y,
  A <> B ->
  ~ Col X A B ->
  ~ Col Y A B ->
  ~ two_sides A B X Y ->
  one_side A B X Y.
Proof.
    intros.
    assert(exists PX, Col A B PX /\ Perp A B X PX).
      apply l8_18_existence.
      intro.
      apply H0.
      apply col_permutation_2.
      assumption.
    ex_and H3 PX.
    induction(eq_dec_points PX A).
      subst PX.
      apply invert_one_side.
      eapply (not_two_sides_one_side_aux _ _ _ _ A); auto.
        apply perp_left_comm.
        assumption.
        Col.
        intro.
        apply H0.
        Col.
        intro.
        apply H1.
        Col.
      intro.
      apply H2.
      apply invert_two_sides.
      assumption.
    apply (not_two_sides_one_side_aux _ _ _ _ PX); auto.
Qed.

Lemma in_angle_reverse :
 forall A B A' C D,
  A <> B -> C <> B -> D <> B -> A' <> B ->
  Bet A B A' ->
  InAngle C A B D ->
  InAngle D A' B C.
Proof.
    intros.
    induction (Col_dec B A C).
      assert(HH:=or_bet_out C B A H0 H).
      induction HH.
        assert(Bet A B D).
          eapply bet_in_angle_bet.
            apply between_symmetry.
            apply H6.
          assumption.
        assert(out B A' C).
          repeat split; try assumption.
          eapply l5_2.
            apply H.
            assumption.
          apply between_symmetry.
          assumption.
        assert( out B D A').
          repeat split; try assumption.
          eapply l5_2.
            apply H.
            assumption.
          assumption.
        apply out_in_angle.
          assumption.
        assumption.
      induction H6.
        repeat split; try assumption.
        exists B.
        split.
          unfold out in H6.
          spliter.
          induction H8.
            eapply between_inner_transitivity.
              apply between_symmetry.
              apply H3.
            assumption.
          eapply outer_transitivity_between.
            apply between_symmetry.
            apply H3.
            assumption.
          auto.
        left.
        reflexivity.
      apply False_ind.
      apply H6.
      apply col_permutation_2.
      assumption.
    induction (Col_dec B D C).
      assert(HH:=or_bet_out C B D H0 H1).
      induction HH.
        assert(one_side A B C D).
          apply in_angle_one_side.
            intro.
            apply H5.
            eapply (col_transitivity_1 _ D).
              auto.
              apply col_permutation_1.
              assumption.
            assumption.
            assumption.
          assumption.
        assert(two_sides A B C D).
          repeat split; try assumption.
            intro.
            apply H5.
            apply col_permutation_3.
            assumption.
            intro.
            apply H5.
            eapply (col_transitivity_1 _ D).
              auto.
              apply col_permutation_2.
              assumption.
            assumption.
          exists B.
          split.
            apply col_trivial_3.
          assumption.
        apply l9_9 in H9.
        contradiction.
      induction H7.
        assert(InAngle C A' B C).
          apply in_angle_trivial_2; assumption.
        eapply l11_25.
          apply H8.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        apply l6_6.
        assumption.
      apply False_ind.
      apply H7.
      apply col_permutation_2.
      assumption.
    assert( HH:= H4).
    apply in_angle_two_sides in HH.
      assert(HH1:=H4).
      unfold InAngle in H4.
      spliter.
      ex_and H9 X.
      induction H10.
        subst X.
        apply col_in_angle; try assumption.
        left.
        repeat split; try assumption.
        eapply l5_2.
          apply H.
          assumption.
        assumption.
      assert(HH0:= HH).
      unfold two_sides in HH.
      spliter.
      assert(one_side D B C A).
        apply in_angle_one_side.
          intro.
          apply H12.
          apply col_permutation_1.
          eapply (col_transitivity_1 _ X).
            unfold out in H10.
            spliter.
            auto.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ D).
              intro.
              subst D.
              apply between_identity in H9.
              subst X.
              ex_and H14 T.
              apply between_identity in H14.
              subst T.
              contradiction.
              apply col_permutation_2.
              assumption.
            apply col_permutation_5.
            apply bet_col.
            assumption.
          apply out_col.
          assumption.
          intro.
          apply H13.
          apply col_permutation_1.
          assumption.
        apply l11_24.
        assumption.
      assert(~Col A D B).
        intro.
        apply H12.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ X).
          unfold out in H10.
          spliter.
          auto.
          apply col_permutation_1.
          eapply (col_transitivity_1 _ D).
            intro.
            subst D.
            apply between_identity in H9.
            subst X.
            apply H13.
            apply col_permutation_1.
            apply out_col.
            assumption.
            assumption.
          apply col_permutation_5.
          apply bet_col.
          assumption.
        apply out_col.
        assumption.
      assert(~Col A' D B).
        intro.
        apply H16.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ A').
          auto.
          apply col_permutation_1.
          apply bet_col.
          assumption.
        apply col_permutation_2.
        assumption.
      assert(two_sides D B A A').
        repeat split; try assumption.
        exists B.
        split.
          apply col_trivial_3.
        assumption.
      assert(two_sides D B C A' ).
        eapply l9_8_2.
          apply H18.
        apply one_side_symmetry.
        assumption.
      unfold two_sides in H19.
      spliter.
      ex_and H22 Y.
      repeat split; try assumption.
      exists Y.
      split.
        apply between_symmetry.
        assumption.
      right.
      apply col_permutation_1 in H22.
      unfold Col in H22.
      induction H22.
        assert(one_side C B A' Y).
          apply out_one_side.
            left.
            intro.
            apply H12.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ A').
              auto.
              apply col_permutation_1.
              apply bet_col.
              assumption.
            apply col_permutation_1.
            assumption.
          apply l6_6.
          apply bet_out.
            intro.
            subst Y.
            apply H13.
            apply col_permutation_5.
            apply bet_col.
            assumption.
            intro.
            subst A'.
            apply between_identity in H23.
            subst Y.
            apply H21.
            apply col_permutation_2.
            apply bet_col.
            assumption.
          assumption.
        assert(two_sides C B Y D).
          repeat split.
            assumption.
            intro.
            apply H20.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ Y).
              intro.
              subst Y.
              unfold one_side in H24.
              ex_and H24 C0.
              unfold two_sides in H26.
              spliter.
              apply H27.
              apply col_trivial_3.
              apply col_permutation_2.
              assumption.
            apply col_permutation_1.
            apply bet_col.
            assumption.
            intro.
            apply H20.
            apply col_permutation_4.
            assumption.
          exists B.
          split.
            apply col_trivial_3.
          apply between_symmetry.
          assumption.
        assert(two_sides C B A A').
          repeat split; try assumption.
            intro.
            apply H12.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ A').
              auto.
              apply col_permutation_1.
              apply bet_col.
              assumption.
            apply col_permutation_2.
            assumption.
          exists B.
          split.
            apply col_trivial_3.
          assumption.
        assert(two_sides C B Y A).
          eapply l9_8_2.
            apply l9_2.
            apply H26.
          assumption.
        assert(one_side C B A D).
          eapply l9_8_1.
            apply l9_2.
            apply H27.
          apply l9_2.
          assumption.
        apply l9_9 in HH0.
        contradiction.
      repeat split.
        intro.
        subst Y.
        apply H12.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ A').
          auto.
          apply col_permutation_1.
          apply bet_col.
          assumption.
        apply col_permutation_1.
        apply bet_col.
        assumption.
        assumption.
      induction H22.
        left.
        assumption.
      right.
      apply between_symmetry.
      assumption.
      intro.
      apply H5.
      assumption.
    assumption.
Qed.

Lemma l11_36 : forall A B C D E F A' D',
 A <> B -> A' <> B -> D <> E -> D' <> E ->
 Bet A B A' -> Bet D E D' ->
 (lea A B C D E F <-> lea D' E F A' B C).
Proof.
    intros.
    split.
      intro.
      assert(HH:=H5).
      apply l11_29_a in H5.
      unfold lea.
      ex_and H5 P.
      exists P.
      split.
        eapply (in_angle_reverse A); try assumption.
          unfold lea in HH.
          ex_and HH X.
          unfold Conga in H8.
          spliter.
          assumption.
        unfold Conga in H6.
        spliter.
        assumption.
      eapply l11_13.
        apply conga_sym.
        apply H6.
        assumption.
        assumption.
        assumption.
      assumption.
    intro.
    assert(HH:=H5).
    unfold lea in H5.
    apply l11_29_b.
    ex_and H5 P.
    exists P.
    split.
      eapply (in_angle_reverse A'); try assumption.
        unfold Conga in H6.
        spliter.
        assumption.
        apply l11_29_a in HH.
        ex_and HH X.
        unfold Conga in H8.
        spliter.
        assumption.
      apply between_symmetry.
      assumption.
    eapply l11_13.
      apply conga_sym.
      apply H6.
      apply between_symmetry.
      assumption.
      assumption.
      apply between_symmetry.
      assumption.
    assumption.
Qed.


Definition lta := fun A B C D E F => lea A B C D E F /\ ~Conga A B C D E F.

Definition gta := fun A B C D E F => lta D E F A B C.

Definition acute := fun A B C => exists A', exists B', exists C', Per A' B' C' /\ lta A B C A' B' C'.

Definition obtuse := fun A B C => exists A', exists B', exists C', Per A' B' C' /\ gta A B C A' B' C'.

Lemma l11_41_aux : forall A B C D,
 ~ Col A B C ->
 Bet B A D ->
 A <> D ->
 lta A C B C A D.
Proof.
    intros.
    assert(exists M , is_midpoint M A C).
      apply midpoint_existence.
    ex_and H2 M.
    double B M P.
    assert(Cong_3 A C B C A P).
      repeat split.
        apply cong_pseudo_reflexivity.
        eapply l7_13.
          apply l7_2.
          apply H3.
        apply l7_2.
        assumption.
      eapply l7_13.
        apply H3.
      apply l7_2.
      assumption.
    assert(A <> C).
      intro.
      subst C.
      apply H.
      apply col_trivial_3.
    assert(B <> C).
      intro.
      subst C.
      apply H.
      apply col_trivial_2.
    assert(C <> D).
      intro.
      subst C.
      apply H.
      apply col_permutation_4.
      apply bet_col.
      assumption.
    assert(A <> M).
      intro.
      subst M.
      apply is_midpoint_id in H3.
      contradiction.
    assert(Conga A C B C A P).
      apply cong3_conga; assumption.
    assert(exists X, Bet A X P /\ Bet M X D).
      eapply inner_pasch.
        apply between_symmetry.
        apply H0.
      apply midpoint_bet.
      apply l7_2.
      assumption.
    ex_and H10 X.
    split.
      unfold lea.
      exists P.
      split.
        assert(InAngle P M A D).
          repeat split.
            auto.
            auto.
            intro.
            subst P.
            unfold Conga in H9.
            spliter.
            absurde.
          exists X.
          split.
            assumption.
          right.
          apply bet_out.
            intro.
            subst X.
            apply H.
            eapply (col_transitivity_1 _ M).
              assumption.
              eapply (col_transitivity_1 _ D).
                assumption.
                apply col_permutation_1.
                apply bet_col.
                assumption.
              apply col_permutation_1.
              apply bet_col.
              assumption.
            apply bet_col.
            apply midpoint_bet.
            assumption.
            unfold Conga in H9.
            spliter.
            assumption.
          assumption.
        eapply l11_25.
          apply H12.
          apply l6_6.
          apply bet_out.
            auto.
            auto.
          apply midpoint_bet.
          assumption.
          apply out_trivial.
          auto.
        apply out_trivial.
        unfold Conga in H9.
        spliter.
        auto.
      assumption.
    intro.
    assert(Conga C A D C A P).
      eapply conga_trans.
        apply conga_sym.
        apply H12.
      assumption.
    apply l11_22_aux in H13.
    induction H13.
      apply H.
      assert(Col B A P).
        apply col_permutation_2.
        eapply (col_transitivity_1 _ D).
          assumption.
          apply out_col.
          assumption.
        apply col_permutation_1.
        apply bet_col.
        assumption.
      assert(B <> P).
        intro.
        subst P.
        apply l7_3 in H2.
        subst M.
        apply H.
        apply bet_col.
        apply midpoint_bet.
        assumption.
      assert(Col M B A).
        apply col_permutation_2.
        eapply (col_transitivity_1 _ P).
          assumption.
          apply col_permutation_5.
          assumption.
        apply col_permutation_5.
        apply bet_col.
        apply midpoint_bet.
        assumption.
      eapply col_transitivity_1.
        apply H8.
        apply col_permutation_2.
        assumption.
      apply bet_col.
      apply midpoint_bet.
      assumption.
    assert(two_sides A C B P).
      repeat split.
        assumption.
        intro.
        apply H.
        apply col_permutation_4.
        assumption.
        intro.
        apply H.
        assert(Col M C P).
          apply col_permutation_2.
          eapply (col_transitivity_1 _ A).
            auto.
            apply col_permutation_3.
            assumption.
          apply col_permutation_2.
          apply bet_col.
          apply midpoint_bet.
          assumption.
        assert(Col M B C).
          eapply (col_transitivity_1 _ P).
            intro.
            subst M.
            apply l7_2 in H2.
            apply is_midpoint_id in H2.
            subst P.
            apply H.
            apply col_permutation_4.
            assumption.
            apply col_permutation_1.
            apply bet_col.
            apply midpoint_bet.
            assumption.
          apply col_permutation_5.
          assumption.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ M).
          intro.
          subst M.
          apply l7_2 in H3.
          apply is_midpoint_id in H3.
          subst C.
          absurde.
          apply col_permutation_3.
          apply bet_col.
          apply midpoint_bet.
          assumption.
        apply col_permutation_2.
        assumption.
      exists M.
      split.
        apply col_permutation_4.
        apply bet_col.
        apply midpoint_bet.
        assumption.
      apply midpoint_bet.
      assumption.
    assert(two_sides A C B D).
      repeat split.
        assumption.
        intro.
        apply H.
        apply col_permutation_4.
        assumption.
        intro.
        apply H.
        eapply (col_transitivity_1 _ D).
          assumption.
          apply col_permutation_1.
          apply bet_col.
          assumption.
        apply col_permutation_4.
        assumption.
      exists A.
      split.
        apply col_trivial_1.
      assumption.
    assert(one_side A C D P).
      unfold one_side.
      exists B.
      split.
        apply l9_2.
        assumption.
      apply l9_2.
      assumption.
    apply invert_two_sides in H13.
    apply l9_9 in H13.
    contradiction.
Qed.

Lemma l11_41 : forall A B C D,
 ~ Col A B C ->
  Bet B A D ->
  A <> D ->
  lta A C B C A D /\ lta A B C C A D.
Proof.
    intros.
    split.
      apply l11_41_aux.
        assumption.
        assumption.
      assumption.
    prolong C A E C A.
    assert(lta A B C B A E).
      eapply l11_41_aux.
        intro.
        apply H.
        apply col_permutation_5.
        assumption.
        assumption.
      intro.
      subst E.
      apply cong_symmetry in H3.
      apply cong_identity in H3.
      subst C.
      apply H.
      apply col_trivial_3.
    assert(Conga B A C C A B).
      apply conga_left_comm.
      apply conga_refl.
        intro.
        subst C.
        apply cong_identity in H3.
        subst E.
        apply H.
        apply col_trivial_3.
      intro.
      subst B.
      apply H.
      apply col_trivial_1.
    assert(Conga D A C E A B).
      eapply l11_13.
        apply H5.
        assumption.
        auto.
        assumption.
      intro.
      subst E.
      apply cong_symmetry in H3.
      apply cong_identity in H3.
      subst C.
      apply H.
      apply col_trivial_3.
    unfold lta in *.
    spliter.
    repeat split.
      eapply l11_30.
        apply H4.
        apply conga_refl.
          intro.
          subst B.
          apply H.
          apply col_trivial_1.
        intro.
        subst C.
        apply H.
        apply col_trivial_2.
      apply conga_sym.
      apply conga_comm.
      assumption.
    intro.
    apply H7.
    eapply conga_trans.
      apply H8.
    apply conga_comm.
    assumption.
Qed.

Lemma not_conga : forall A B C A' B' C' D E F ,
 Conga A B C A' B' C' ->
 ~ Conga A B C D E F ->
 ~ Conga A' B' C' D E F.
Proof.
    intros.
    intro.
    apply H0.
    eapply conga_trans.
      apply H.
    assumption.
Qed.

Lemma not_conga_sym : forall A B C D E F,
 ~ Conga A B C D E F ->
 ~ Conga D E F A B C.
Proof.
    intros.
    intro.
    apply H.
    apply conga_sym.
    assumption.
Qed.

Lemma not_and_lta : forall A B C D E F, ~(lta A B C D E F /\ lta D E F A B C).
Proof.
    intros.
    intro.
    unfold lta in *.
    spliter.
    assert(Conga A B C D E F).
      apply lea_asym.
        assumption.
      assumption.
    contradiction.
Qed.

Lemma conga_preserves_lta : forall A B C D E F A' B' C' D' E' F',
 Conga A B C A' B' C' ->
 Conga D E F D' E' F' ->
 lta A B C D E F ->
 lta A' B' C' D' E' F'.
Proof.
    intros.
    unfold lta in *.
    spliter.
    split.
      eapply l11_30.
        apply H1.
        assumption.
      assumption.
    intro.
    apply H2.
    eapply conga_trans.
      apply H.
    eapply conga_trans.
      apply H3.
    apply conga_sym.
    assumption.
Qed.

Lemma conga_preserves_gta : forall A B C D E F A' B' C' D' E' F' ,
 Conga A B C A' B' C' ->
 Conga D E F D' E' F' ->
 gta A B C D E F ->
 gta A' B' C' D' E' F'.
Proof.
    intros.
    unfold gta in *.
    eapply conga_preserves_lta.
      apply H0.
      apply H.
    assumption.
Qed.

Lemma lta_trans : forall A B C A1 B1 C1 A2 B2 C2,
 lta A B C A1 B1 C1 ->
 lta A1 B1 C1 A2 B2 C2 ->
 lta A B C A2 B2 C2.
Proof.
    intros.
    assert(HH1:= H).
    assert(HH2:= H0).
    unfold lta in H.
    unfold lta in H0.
    spliter.
    assert(lea A B C A2 B2 C2).
      eapply lea_trans.
        apply H.
      assumption.
    split.
      assumption.
    intro.
    assert(lta A2 B2 C2 A1 B1 C1).
      eapply conga_preserves_lta.
        apply H4.
        apply conga_refl.
          unfold lea in H0.
          ex_and H0 X.
          unfold Conga in H5.
          spliter.
          assumption.
        unfold lea in H0.
        ex_and H0 X.
        unfold Conga in H5.
        spliter.
        assumption.
      assumption.
    apply (not_and_lta A1 B1 C1 A2 B2 C2).
    split; assumption.
Qed.

Lemma gta_trans : forall A B C A1 B1 C1 A2 B2 C2,
 gta A B C A1 B1 C1 ->
 gta A1 B1 C1 A2 B2 C2 ->
 gta A B C A2 B2 C2.
Proof.
    intros.
    unfold gta in *.
    eapply lta_trans.
      apply H0.
    assumption.
Qed.

Lemma lea_left_comm : forall A B C D E F, lea A B C D E F -> lea C B A D E F.
Proof.
    intros.
    unfold lea in *.
    ex_and H P.
    exists P.
    split.
      assumption.
    apply conga_left_comm.
    assumption.
Qed.

Lemma lea_right_comm : forall A B C D E F, lea A B C D E F -> lea A B C F E D.
Proof.
    intros.
    apply l11_29_b.
    apply l11_29_a in H.
    ex_and H P.
    exists P.
    split.
      assumption.
    apply conga_right_comm.
    assumption.
Qed.

Lemma lea_comm : forall A B C D E F, lea A B C D E F -> lea C B A F E D.
Proof.
    intros.
    apply lea_left_comm.
    apply lea_right_comm.
    assumption.
Qed.

Lemma lta_left_comm : forall A B C D E F, lta A B C D E F -> lta C B A D E F.
Proof.
    unfold lta.
    intros.
    spliter.
    split.
      apply lea_left_comm.
      assumption.
    intro.
    apply H0.
    apply conga_left_comm.
    assumption.
Qed.

Lemma lta_right_comm : forall A B C D E F, lta A B C D E F -> lta A B C F E D.
Proof.
    unfold lta.
    intros.
    spliter.
    split.
      apply lea_right_comm.
      assumption.
    intro.
    apply H0.
    apply conga_right_comm.
    assumption.
Qed.

Lemma lta_comm : forall A B C D E F, lta A B C D E F -> lta C B A F E D.
Proof.
    intros.
    apply lta_left_comm.
    apply lta_right_comm.
    assumption.
Qed.

Lemma l11_43_aux : forall A B C, ~Col A B C -> (Per B A C \/ obtuse B A C) -> acute A B C.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    prolong B A B' B A.
    assert(~ Col B' A C).
      intro.
      apply H.
      eapply (col_transitivity_1 _ B').
        intro.
        subst B'.
        apply cong_symmetry in H5.
        apply cong_identity in H5.
        subst A.
        apply H.
        apply col_trivial_1.
        apply col_permutation_1.
        apply bet_col.
        assumption.
      apply col_permutation_4.
      assumption.
    apply not_col_distincts in H6.
    spliter.
    assert(lta A C B C A B'/\ lta A B C C A B').
      apply l11_41.
        assumption.
        assumption.
      auto.
    spliter.
    induction H0.
      unfold acute.
      exists C.
      exists A.
      exists B.
      split.
        apply l8_2.
        assumption.
      spliter.
      unfold lta.
      unfold lta in H11.
      spliter.
      assert(Per B' A C).
        apply l8_2.
        eapply (per_col _ _ B).
          assumption.
          apply l8_2.
          assumption.
        apply col_permutation_4.
        apply bet_col.
        assumption.
      assert(Conga B A C B' A C).
        apply l11_16.
          assumption.
          auto.
          auto.
          assumption.
          assumption.
        auto.
      split.
        eapply l11_30.
          apply H11.
          apply conga_refl.
            assumption.
          auto.
        apply conga_comm.
        apply conga_sym.
        assumption.
      intro.
      apply H12.
      eapply conga_trans.
        apply H15.
      apply conga_comm.
      assumption.
    unfold acute.
    unfold obtuse in H0.
    ex_and H0 a.
    ex_and H12 b.
    ex_and H0 c.
    unfold gta in H12.
    assert(HH1:= H12).
    unfold lta in H12.
    spliter.
    unfold lea in H12.
    ex_and H12 P.
    exists B.
    exists A.
    exists P.
    assert(Per B A P).
      eapply l11_17.
        apply H0.
      assumption.
    split.
      assumption.
    assert(Per P A B').
      eapply per_col.
        apply H1.
        eapply l11_17.
          apply H0.
        apply conga_right_comm.
        assumption.
      apply col_permutation_4.
      apply bet_col.
      assumption.
    assert(Conga B A P B' A P).
      eapply l11_16.
        assumption.
        auto.
        intro.
        subst P.
        unfold Conga in H14.
        spliter.
        absurde.
        apply l8_2.
        assumption.
        assumption.
      intro.
      subst P.
      unfold Conga in H14.
      spliter.
      absurde.
    assert(lta C A B' P A B).
      assert(B <> A).
        auto.
      assert(HH := l11_36 B A P B A C B' B' H18 H7 H18 H7 H4 H4).
      destruct HH.
      unfold lta.
      split.
        eapply l11_30.
          apply H19.
          unfold lta in HH1.
          spliter.
          eapply l11_30.
            apply H21.
            assumption.
          apply conga_refl.
            auto.
          auto.
          apply conga_left_comm.
          apply conga_refl.
            auto.
          assumption.
        apply conga_right_comm.
        apply conga_sym.
        assumption.
      intro.
      apply H13.
      assert(Per B' A C).
        eapply l11_17.
          apply H15.
        apply conga_comm.
        apply conga_sym.
        assumption.
      assert(Per C A B).
        eapply (per_col _ _ B').
          auto.
          apply l8_2.
          assumption.
        apply col_permutation_1.
        apply bet_col.
        assumption.
      apply l11_16.
        assumption.
        unfold Conga in H14.
        spliter.
        assumption.
        unfold Conga in H14.
        spliter.
        assumption.
        apply l8_2.
        assumption.
        auto.
      auto.
    eapply lta_trans.
      apply H11.
    apply lta_right_comm.
    assumption.
Qed.

Lemma obtuse_sym : forall A B C, obtuse A B C -> obtuse C B A.
Proof.
    unfold obtuse.
    intros.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split.
      assumption.
    unfold gta in *.
    apply lta_right_comm.
    assumption.
Qed.

Lemma acute_sym : forall A B C, acute A B C -> acute C B A.
Proof.
    unfold acute.
    intros.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split.
      assumption.
    apply lta_left_comm.
    assumption.
Qed.


Lemma l11_43 : forall A B C, ~Col A B C -> (Per B A C \/ obtuse B A C) -> acute A B C /\ acute A C B.
Proof.
    intros.
    split.
      apply l11_43_aux.
        assumption.
      assumption.
    apply l11_43_aux.
      intro.
      apply H.
      apply col_permutation_5.
      assumption.
    induction H0.
      left.
      apply l8_2.
      assumption.
    right.
    apply obtuse_sym.
    assumption.
Qed.

Lemma acute_lea_acute : forall A B C D E F, acute D E F -> lea A B C D E F -> acute A B C.
Proof.
    intros.
    unfold acute in *.
    ex_and H A'.
    ex_and H1 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split.
      assumption.
    assert(HH1:=H1).
    unfold lta in H1.
    spliter.
    unfold lta.
    split.
      eapply lea_trans.
        apply H0.
      assumption.
    intro.
    assert(lta A' B' C' D E F).
      eapply conga_preserves_lta.
        apply H3.
        apply conga_refl.
          unfold lea in H0.
          ex_and H0 X.
          unfold Conga in H4.
          spliter.
          assumption.
        apply lea_comm in H0.
        unfold lea in H0.
        ex_and H0 X.
        unfold Conga in H4.
        spliter.
        assumption.
      split.
        assumption.
      intro.
      apply H2.
      eapply conga_trans.
        apply conga_sym.
        apply H4.
      assumption.
    apply (not_and_lta A' B' C' D E F).
    split; assumption.
Qed.

Definition gea := fun A B C D E F => lea D E F A B C.


Lemma obtuse_gea_obtuse : forall A B C D E F, obtuse D E F -> gea A B C D E F -> obtuse A B C.
Proof.
    intros.
    ex_and H A'.
    ex_and H1 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split.
      assumption.
    assert(HH1:=H1).
    unfold gta in H1.
    unfold lta in H1.
    spliter.
    unfold gta.
    unfold lta.
    split.
      eapply lea_trans.
        apply H1.
      assumption.
    intro.
    assert(gta A' B' C' D E F).
      eapply conga_preserves_gta.
        apply conga_sym.
        apply H3; apply H3.
        apply conga_refl.
          unfold lea in H0.
          ex_and H0 X.
          unfold Conga in H4.
          spliter.
          assumption.
        apply lea_comm in H0.
        unfold lea in H0.
        ex_and H0 X.
        unfold Conga in H4.
        spliter.
        assumption.
      unfold gta.
      split.
        assumption.
      intro.
      apply H2.
      eapply conga_trans.
        apply H3.
      apply conga_sym.
      assumption.
    unfold gta in *.
    apply (not_and_lta A' B' C' D E F).
    split; assumption.
Qed.

Lemma lea_acute_obtuse : forall A B C D E F, acute A B C -> obtuse D E F -> lea A B C D E F.
Proof.
    intros.
    unfold acute in H.
    unfold obtuse in H0.
    ex_and H A1.
    ex_and H1 B1.
    ex_and H C1.
    ex_and H0 A2.
    ex_and H2 B2.
    ex_and H0 C2.
    assert(A1 <> B1 /\ C1 <> B1 /\ A2 <> B2 /\ C2 <> B2 /\ A <> B /\ C <> B).
      unfold lta in H1.
      unfold gta in H2.
      unfold lta in H2.
      spliter.
      unfold lea in *.
      ex_and H1 X.
      ex_and H2 Y.
      unfold Conga in H6.
      unfold Conga in H5.
      unfold InAngle in H1.
      spliter.
      repeat split; assumption.
    spliter.
    assert(Conga A1 B1 C1 A2 B2 C2).
      apply l11_16; assumption.
    unfold gta in H2.
    assert(lta A B C A2 B2 C2).
      eapply conga_preserves_lta.
        apply conga_refl.
          assumption.
        assumption.
        apply H9.
      assumption.
    assert(lta A B C D E F).
      eapply lta_trans.
        apply H10.
      apply H2.
    unfold lta in H11.
    spliter.
    assumption.
Qed.

(** In an isosceles triangle the two base angle are equal.
This is Euclid: Book 1, Proposition 5.
 *)

Lemma l11_44_1_a : forall A B C, ~Col A B C -> Cong B A B C -> Conga B A C B C A.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    assert(exists P, is_midpoint P A C).
      apply midpoint_existence.
    ex_and H4 P.
    assert(P <> C).
      intro.
      subst C.
      apply l7_2 in H5.
      apply is_midpoint_id in H5.
      subst A.
      apply H.
      apply col_trivial_3.
    assert(Cong_3 B C P B A P).
      repeat split.
        apply cong_symmetry.
        assumption.
        apply cong_reflexivity.
      unfold is_midpoint in H5.
      spliter.
      apply cong_symmetry.
      apply cong_right_commutativity.
      assumption.
    assert(Conga B C P B A P).
      apply cong3_conga.
        assumption.
        assumption.
      assumption.
    apply conga_sym.
    eapply l11_10.
      apply H7.
      apply out_trivial.
      auto.
      repeat split.
        assumption.
        assumption.
      unfold is_midpoint in H5.
      spliter.
      right.
      apply between_symmetry.
      assumption.
      apply out_trivial.
      auto.
    repeat split.
      auto.
      intro.
      subst A.
      apply is_midpoint_id in H5.
      subst C.
      apply H.
      apply col_trivial_3.
    unfold is_midpoint in H5.
    spliter.
    right.
    assumption.
Qed.

(** This is Euclid: Book 1, Proposition 18. *)

Lemma l11_44_2_a : forall A B C, ~Col A B C -> lt B A B C -> lta B C A B A C.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    unfold lt in H0.
    spliter.
    unfold le in H0.
    ex_and H0 C'.
    assert(C <> C').
      intro.
      subst C'.
      contradiction.
    assert(C' <> A).
      intro.
      subst C'.
      apply H.
      apply col_permutation_4.
      apply bet_col.
      assumption.
    assert(C' <> B).
      intro.
      subst C'.
      apply cong_identity in H5.
      subst A.
      absurde.
    assert(InAngle C' B A C).
      repeat split.
        auto.
        auto.
        assumption.
      exists C'.
      split.
        assumption.
      right.
      apply out_trivial.
      auto.
    assert(HH:=l11_41 C' C A B).
    assert(lta C' A C A C' B /\ lta C' C A A C' B).
      apply HH.
        intro.
        apply H.
        apply col_permutation_1.
        eapply col_transitivity_1.
          apply H6.
          apply col_permutation_4.
          assumption.
        apply col_permutation_3.
        apply bet_col.
        assumption.
        apply between_symmetry.
        assumption.
      assumption.
    clear HH.
    spliter.
    assert(lta B A C' B A C).
      split.
        unfold lea.
        exists C'.
        split.
          assumption.
        apply conga_refl.
          auto.
        assumption.
      intro.
      apply l11_22_aux in H12.
      induction H12.
        apply H.
        apply out_col in H12.
        apply bet_col in H0.
        apply col_permutation_1.
        eapply col_transitivity_1.
          apply H6.
          Col.
        Col.
      assert(one_side B A C' C).
        apply out_one_side.
          right.
          intro.
          apply H.
          Col.
        apply bet_out;auto.
      apply l9_9 in H12.
      contradiction.
    assert(lta B C A A C' B).
      eapply conga_preserves_lta.
        3: apply H11.
        eapply out_conga.
          apply conga_refl.
            apply H2. (* *)
          apply H3.
          apply l6_6.
          apply bet_out.
            auto.
            assumption.
          apply between_symmetry.
          assumption.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        apply out_trivial.
        auto.
      apply conga_refl.
        auto.
      auto.
    assert(Conga B A C' B C' A).
      assert(HH := l11_44_1_a A B C').
      apply HH.
        intro.
        apply H.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ C').
          auto.
          apply bet_col.
          assumption.
        Col.
      assumption.
    apply conga_right_comm in H14.
    assert(lta B C A B A C').
      eapply conga_preserves_lta.
        2: apply conga_sym.
        2: apply H14.
        apply conga_refl.
          assumption.
        assumption.
      assumption.
    eapply lta_trans.
      apply H15.
    assumption.
Qed.

Lemma not_lta_and_cong : forall A B C D E F, ~(lta A B C D E F /\ Conga A B C D E F).
Proof.
    intros.
    intro.
    spliter.
    unfold lta in H.
    spliter.
    contradiction.
Qed.

Lemma not_gta_and_cong : forall A B C D E F, ~(gta A B C D E F /\ Conga A B C D E F).
Proof.
    intros.
    intro.
    spliter.
    unfold gta in H.
    unfold lta in H.
    spliter.
    apply conga_sym in H0.
    contradiction.
Qed.

Lemma not_lta_and_gta : forall  A B C D E F, ~(lta A B C D E F /\ gta A B C D E F).
Proof.
    intros.
    intro.
    spliter.
    unfold gta in H0.
    unfold lta in *.
    spliter.
    apply H2.
    apply lea_asym.
      assumption.
    assumption.
Qed.

Lemma conga_sym_equiv : forall A B C A' B' C', Conga A B C A' B' C' <-> Conga A' B' C' A B C.
Proof.
    intros.
    split; apply conga_sym.
Qed.

Lemma Conga_dec :
  forall A B C D E F,
   Conga A B C D E F \/ ~ Conga A B C D E F.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst;right;intro;unfold Conga in *;intuition.
    induction (eq_dec_points C B).
      subst;right;intro;unfold Conga in *;intuition.
    induction (eq_dec_points D E).
      subst;right;intro;unfold Conga in *;intuition.
    induction (eq_dec_points F E).
      subst;right;intro;unfold Conga in *;intuition.
    assert (exists A' : Tpoint, Bet B A A' /\ Cong A A' E D) by (apply segment_construction).
    decompose [ex and] H3; clear H3.
    assert (exists C' : Tpoint, Bet B C C' /\ Cong C C' E F) by (apply segment_construction).
    decompose [ex and] H3; clear H3.
    assert (exists D' : Tpoint, Bet E D D' /\ Cong D D' B A) by (apply segment_construction).
    decompose [ex and] H3; clear H3.
    assert (exists F' : Tpoint, Bet E F F' /\ Cong F F' B C) by (apply segment_construction).
    decompose [ex and] H3; clear H3.
    induction (Cong_dec x x0 x1 x2).
      left.
      unfold Conga.
      repeat split; try assumption.
      exists x; exists x0; exists x1; exists x2.
      repeat split; assumption.
    right.
    unfold Conga.
    intro.
    decompose [and ex] H4; clear H4.
    assert (x3 = x) by (apply construction_unicity with B A E D; intuition).
    assert (x4 = x0) by (apply construction_unicity with B C E F; intuition).
    assert (x5 = x1) by (apply construction_unicity with E D B A; intuition).
    assert (x6 = x2) by (apply construction_unicity with E F B C; intuition).
    subst.
    contradiction.
Qed.

Lemma or_lt_cong_gt : forall A B C D, lt A B C D \/ gt A B C D \/ Cong A B C D.
Proof.
    intros.
    assert(HH:= le_cases A B C D).
    induction HH.
      induction(Cong_dec A B C D).
        right; right.
        assumption.
      left.
      unfold lt.
      split; assumption.
    induction(Cong_dec A B C D).
      right; right.
      assumption.
    right; left.
    unfold gt.
    unfold lt.
    split.
      assumption.
    intro.
    apply H0.
    apply cong_symmetry.
    assumption.
Qed.

Lemma lta_not_conga : forall A B C D E F, A <> B -> C <> B -> D <> E -> F <> E -> lta A B C D E F -> ~ Conga A B C D E F.
Proof.
    intros.
    intro.
    unfold lta in H3.
    spliter.
    contradiction.
Qed.

(** If the base angles are equal the triangle is isosceles. *)


Lemma l11_44_1_b : forall A B C, ~Col A B C -> Conga B A C B C A -> Cong B A B C.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    assert(HH:= or_lt_cong_gt B A B C).
    induction HH.
      apply l11_44_2_a in H4.
        apply lta_not_conga in H4.
          apply conga_sym in H0.
          contradiction.
          assumption.
          assumption.
          auto.
        auto.
      assumption.
    induction H4.
      unfold gt in H4.
      apply l11_44_2_a in H4.
        apply lta_not_conga in H4.
          contradiction.
          auto.
          auto.
          assumption.
        assumption.
      intro.
      apply H.
      apply col_permutation_3.
      assumption.
    assumption.
Qed.

(** This is Euclid Book I, Proposition 19. *)

Lemma l11_44_2_b : forall A B C, ~Col A B C -> lta B A C B C A -> lt B C B A.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    assert(HH:= or_lt_cong_gt B A B C).
    induction HH.
      apply l11_44_2_a in H4.
        assert(HH:= not_lta_and_gta B A C B C A).
        apply False_ind.
        apply HH.
        split; assumption.
      assumption.
    induction H4.
      unfold gt in H4.
      assumption.
    apply l11_44_1_a in H4.
      apply lta_not_conga in H0.
        contradiction.
        auto.
        auto.
        assumption.
      assumption.
    assumption.
Qed.

Lemma l11_44_1 : forall A B C, ~Col A B C -> (Conga B A C B C A <-> Cong B A B C).
Proof.
    intros.
    split.
      intro.
      apply l11_44_1_b.
        assumption.
      assumption.
    intro.
    apply l11_44_1_a.
      assumption.
    assumption.
Qed.

Lemma l11_44_2 : forall A B C, ~Col A B C -> (lta B A C B C A <-> lt B C B A).
Proof.
    intros.
    split.
      intro.
      apply l11_44_2_b.
        assumption.
      assumption.
    intro.
    apply l11_44_2_a.
      intro.
      apply H.
      apply col_permutation_3.
      assumption.
    assumption.
Qed.

Lemma between_symmetric : forall A B X Y P, Bet A P B -> Cong A P X Y -> (exists P', Bet A P' B /\ Cong B P' X Y).
Proof.
    intros.
    assert(exists M, is_midpoint M A B).
      apply midpoint_existence.
    ex_and H1 M.
    double P M P'.
    exists P'.
    assert(Cong P A P' B).
      eapply l7_13.
        apply l7_2.
        apply H1.
      apply l7_2.
      assumption.
    split.
      eapply l4_6.
        apply between_symmetry.
        apply H.
      repeat split.
        eapply l7_13.
          apply H2.
        apply l7_2.
        assumption.
        apply cong_pseudo_reflexivity.
      assumption.
    apply cong_symmetry.
    eapply cong_transitivity.
      apply cong_symmetry.
      apply H0.
    eapply l7_13.
      apply l7_2.
      apply H2.
    apply l7_2.
    assumption.
Qed.


Lemma le_left_comm : forall A B C D, le A B C D -> le B A C D.
Proof.
    intros.
    unfold le in *.
    ex_and H P.
    exists P.
    split.
      assumption.
    apply cong_left_commutativity.
    assumption.
Qed.

Lemma le_right_comm : forall A B C D, le A B C D -> le A B D C.
Proof.
    intros.
    assert(Hle:=H).
    unfold le in H.
    unfold le.
    ex_and H P.
    apply cong_symmetry in H0.
    assert(HH:=between_symmetric C D A B P H H0).
    ex_and HH P'.
    exists P'.
    split.
      apply between_symmetry.
      assumption.
    apply cong_symmetry.
    assumption.
Qed.

Lemma le_comm : forall A B C D, le A B C D -> le B A D C.
Proof.
    intros.
    apply le_left_comm.
    apply le_right_comm.
    assumption.
Qed.

Lemma ge_left_comm : forall A B C D, ge A B C D -> ge B A C D.
Proof.
    intros.
    unfold ge in *.
    apply le_right_comm.
    assumption.
Qed.

Lemma ge_right_comm : forall A B C D, ge A B C D -> ge A B D C.
Proof.
    intros.
    unfold ge in *.
    apply le_left_comm.
    assumption.
Qed.

Lemma ge_comm :  forall A B C D, ge A B C D -> ge B A D C.
Proof.
    intros.
    apply ge_left_comm.
    apply ge_right_comm.
    assumption; unfold ge in *.
Qed.


Lemma lt_right_comm : forall A B C D, lt A B C D -> lt A B D C.
Proof.
    intros.
    unfold lt in *.
    spliter.
    split.
      apply le_right_comm.
      assumption.
    intro.
    apply H0.
    apply cong_right_commutativity.
    assumption.
Qed.

Lemma lt_left_comm : forall A B  C D, lt A B C D -> lt B A C D.
Proof.
    intros.
    unfold lt in *.
    spliter.
    split.
      unfold le in *.
      ex_and H P.
      exists P.
      apply cong_left_commutativity in H1.
      split; assumption.
    intro.
    apply H0.
    apply cong_left_commutativity.
    assumption.
Qed.

Lemma lt_comm : forall A B  C D, lt A B C D -> lt B A D C.
Proof.
    intros.
    apply lt_left_comm.
    apply lt_right_comm.
    assumption.
Qed.

Lemma gt_left_comm : forall A B C D, gt A B C D -> gt B A C D.
Proof.
    intros.
    unfold gt in *.
    apply lt_right_comm.
    assumption.
Qed.

Lemma gt_right_comm : forall A B C D, gt A B C D -> gt A B D C.
Proof.
    intros.
    unfold gt in *.
    apply lt_left_comm.
    assumption.
Qed.

Lemma gt_comm : forall A B C D, gt A B C D -> gt B A D C.
Proof.
    intros.
    apply gt_left_comm.
    apply gt_right_comm.
    assumption.
Qed.

Lemma acute_distinct : forall A B C, acute A B C -> acute A B C /\ A <> B /\ C <> B.
Proof.
    intros.
    split.
      assumption.
    unfold acute in H.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    unfold lta in H0.
    spliter.
    unfold lea in H0.
    ex_and H0 P.
    unfold Conga in H2.
    spliter.
    split; assumption.
Qed.

Lemma lta_diff : forall A B C D E F, lta A B C D E F -> lta A B C D E F /\ A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
    intros.
    split.
      assumption.
    unfold lta in H.
    spliter.
    unfold lea in H.
    ex_and H P.
    unfold Conga in H1.
    unfold InAngle in H.
    spliter.
    repeat split; assumption.
Qed.

Lemma l5_12_a : forall A B C, Bet A B C -> le A B A C /\ le B C A C.
Proof.
    intros.
    split.
      unfold le.
      exists B; split.
        assumption.
      apply cong_reflexivity.
    apply le_comm.
    unfold le.
    exists B.
    split.
      apply between_symmetry.
      assumption.
    apply cong_reflexivity.
Qed.

Lemma l5_12_b : forall A B C, Col A B C -> (le A B A C /\ le B C A C) -> Bet A B C.
Proof.
    intros.
    spliter.
    unfold Col in H.
    induction H.
      assumption.
    induction H.
      assert(le B C B A /\ le C A B A).
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
    assert(le B A B C /\ le A C B C).
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

Lemma l11_46 : forall A B C, ~Col A B C -> (Per A B C \/ obtuse A B C) -> lt B A A C /\ lt B C A C.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    assert(HH:= H0).
    apply l11_43 in H0.
      spliter.
      split.
        apply lt_left_comm.
        eapply l11_44_2_b.
          intro.
          apply H.
          apply col_permutation_1.
          assumption.
        unfold acute in H4.
        ex_and H4 A'.
        ex_and H5 B'.
        ex_and H4 C'.
        apply lta_diff in H5.
        spliter.
        induction HH.
          eapply conga_preserves_lta.
            apply conga_refl.
              assumption.
            assumption.
            apply l11_16.
              apply H4.
              assumption.
              assumption.
              assumption.
              assumption.
            auto.
          apply lta_left_comm.
          assumption.
        unfold obtuse in H10.
        ex_and H10 A''.
        ex_and H11 B''.
        ex_and H10 C''.
        unfold gta in H11.
        eapply lta_trans.
          apply lta_left_comm.
          apply H5.
        eapply conga_preserves_lta.
          apply lta_diff in H11.
          spliter.
          apply l11_16.
            apply H10.
            assumption.
            assumption.
            assumption.
            assumption.
          assumption.
          apply conga_refl.
            assumption.
          auto.
        assumption.
      apply lt_left_comm.
      apply lt_right_comm.
      eapply l11_44_2_b.
        intro.
        apply H.
        apply col_permutation_5.
        assumption.
      unfold acute in H0.
      ex_and H0 A'.
      ex_and H5 B'.
      ex_and H0 C'.
      apply lta_diff in H5.
      spliter.
      induction HH.
        eapply conga_preserves_lta.
          apply conga_refl.
            auto.
          auto.
          apply l11_16.
            apply H0.
            assumption.
            assumption.
            apply l8_2.
            assumption.
            auto.
          assumption.
        apply lta_left_comm.
        assumption.
      unfold obtuse in H10.
      ex_and H10 A''.
      ex_and H11 B''.
      ex_and H10 C''.
      unfold gta in H11.
      eapply lta_trans.
        apply lta_left_comm.
        apply H5.
      eapply conga_preserves_lta.
        apply lta_diff in H11.
        spliter.
        apply l11_16.
          apply H10.
          assumption.
          assumption.
          assumption.
          assumption.
        assumption.
        apply conga_refl.
          auto.
        assumption.
      apply lta_right_comm.
      assumption.
    intro.
    apply H.
    apply col_permutation_4.
    assumption.
Qed.

Lemma l11_47 : forall A B C H , Per A C B -> Perp_in H C H A B -> Bet A H B /\ Distincts A H B.
Proof.
    intros.
    assert(HH1:= H1).
    unfold Perp_in in H1.
    spliter.
    assert(Per C H A).
      apply H5.
        apply col_trivial_1.
      apply col_trivial_1.
    assert(Perp C H A B).
      eapply l8_14_2_1a.
      apply HH1.
    induction (Col_dec A C B).
      assert(A <> H).
        intro.
        subst H.
        apply H1.
        apply sym_equal.
        eapply per_col_eq.
          apply H0.
          assumption.
        intro.
        subst B.
        assert(Perp_in C C A A C).
          apply perp_perp_in.
          assumption.
        apply H2.
        eapply l8_14_3.
          apply HH1.
        assumption.
      apply False_ind.
      apply H9.
      eapply per_col_eq.
        apply l8_2.
        apply H6.
        eapply (col_transitivity_1 _ B).
          assumption.
          apply col_permutation_1.
          assumption.
        apply col_permutation_5.
        assumption.
      auto.
    apply not_col_distincts in H8.
    spliter.
    assert(A <> H).
      intro.
      subst A.
      assert(Per C H B).
        apply perp_in_per.
        assumption.
      apply H1.
      eapply l8_7.
        apply l8_2.
        apply H0.
      apply l8_2.
      assumption.
    assert(Per C H B).
      eapply per_col.
        2: apply H6.
        auto.
      assumption.
    assert(H <> B).
      intro.
      subst B.
      apply H10.
      eapply l8_7.
        apply H0.
      apply l8_2.
      assumption.
    assert(lt H A A C /\ lt H C A C).
      apply l11_46.
        intro.
        apply H8.
        eapply (col_transitivity_1 _ ).
          apply H12.
          assumption.
        apply col_permutation_4.
        assumption.
      left.
      apply l8_2.
      assumption.
    assert(lt C A A B /\ lt C B A B).
      apply l11_46.
        assumption.
      left.
      assumption.
    assert(lt H B B C /\ lt H C B C).
      eapply l11_46.
        intro.
        apply H8.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ H).
          auto.
          apply col_permutation_2.
          assumption.
        assumption.
      left.
      apply l8_2.
      assumption.
    split.
      apply l5_12_b.
        apply col_permutation_4.
        assumption.
      unfold lt in *.
      spliter.
      split.
        eapply le_transitivity.
          apply le_left_comm.
          apply H15.
        apply le_left_comm.
        assumption.
      eapply le_transitivity.
        apply H17.
      apply le_left_comm.
      assumption.
    repeat split.
      assumption.
      assumption.
    assumption.
Qed.

Lemma l11_49 : forall A B C A' B' C',
 Conga A B C A' B' C' -> Cong B A B' A' -> Cong B C B' C' ->
 Cong A C A' C' /\ (A <> C -> Conga B A C B' A' C' /\ Conga B C A B' C' A').
Proof.
    intros.
    assert(Cong A C A' C').
      eapply cong2_conga_cong.
        apply H.
        apply cong_commutativity.
        assumption.
      assumption.
    split.
      assumption.
    intro.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B').
      unfold Conga in H.
      spliter.
      repeat split; assumption.
    spliter.
    split.
      apply l11_3_bis.
      exists B.
      exists C.
      exists B'.
      exists C'.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        intro.
        subst C'.
        apply cong_identity in H2.
        contradiction.
      repeat split; assumption.
    apply l11_3_bis.
    exists B.
    exists A.
    exists B'.
    exists A'.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      intro.
      subst C'.
      apply cong_identity in H2.
      contradiction.
    repeat split.
      assumption.
      assumption.
    apply cong_commutativity.
    assumption.
Qed.


Lemma l11_50_1  : forall A B C A' B' C',
  ~Col A B C -> Conga B A C B' A' C' -> Conga A B C A' B' C' -> Cong A B A' B' ->
  Cong A C A' C' /\ Cong B C B' C' /\ Conga A C B A' C' B'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B') by (unfold Conga in *;intuition).
    spliter.
    assert(exists C'', out B' C'' C' /\ Cong B' C'' B C).
      apply l6_11_existence;auto.
    ex_and H7 C''.
    assert(B' <> C'') by (unfold out in *;intuition).
    assert(~ Col A' B' C') by (eapply ncol_conga_ncol;eauto).
    assert(~ Col A' B' C'').
      intro.
      apply H10.
      apply out_col in H7.
      eapply col_permutation_2.
      eapply (col_transitivity_1 _ C'').
        assumption.
        assumption.
      apply col_permutation_1.
      assumption.
    assert(HH:=l11_4_1 A B C A' B' C' H1).
    spliter.
    assert(Cong A C A' C'').
      apply H16.
      assert (C''<> B') by auto.
      repeat split;try assumption.
        left.
        apply between_trivial.
        left.
        apply between_trivial.
        left.
        apply between_trivial.
        auto.
        unfold out in  H7.
        spliter.
        assumption.
        apply cong_commutativity.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Cong_3 B A C B' A' C'').
      repeat split.
        apply cong_commutativity.
        assumption.
        apply cong_symmetry.
        assumption.
      assumption.
    assert(Conga B A C B' A' C'').
      apply cong3_conga.
        auto.
        apply not_col_distincts in H.
        spliter.
        auto.
      assumption.
    assert(Conga B' A' C' B' A' C'').
      eapply conga_trans.
        apply conga_sym.
        apply H0.
      assumption.
    assert(C' = C'').
      assert(HH:= l11_22_aux B' A' C' C'' H20).
      induction HH.
        eapply inter_unicity.
          5: apply H10.
          apply col_trivial_2.
          apply out_col in H7.
          apply H7.
          apply out_col.
          assumption.
          apply col_trivial_2.
        assumption.
      assert(one_side B' A' C' C'').
        apply out_one_side.
          left.
          intro.
          apply H10.
          apply col_permutation_4.
          assumption.
        apply l6_6.
        assumption.
      apply l9_9 in H21.
      contradiction.
    subst C''.
    clear H20.
    split.
      assumption.
    split.
      eapply cong2_conga_cong.
        apply H19.
        apply cong_commutativity.
        assumption.
      assumption.
    apply cong3_conga.
      apply not_col_distincts in H.
      spliter.
      assumption.
      auto.
    unfold Cong_3.
    repeat split.
      assumption.
      assumption.
    apply cong_symmetry.
    apply cong_commutativity.
    assumption.
Qed.

Lemma l11_50_2  : forall A B C A' B' C',
  ~Col A B C -> Conga B C A B' C' A' -> Conga A B C A' B' C' -> Cong A B A' B' ->
  Cong A C A' C' /\ Cong B C B' C' /\ Conga C A B C' A' B'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B').
      unfold Conga in H1.
      spliter.
      repeat split; assumption.
    spliter.
    assert(exists C'',  out B' C'' C' /\ Cong B' C'' B C).
      apply l6_11_existence.
        assumption.
      auto.
    ex_and H7 C''.
    assert(B' <> C'').
      unfold out in H7.
      spliter.
      auto.
    assert(~Col A' B' C').
      eapply ncol_conga_ncol.
        apply H.
      assumption.
    assert(~Col A' B' C'').
      intro.
      apply H10.
      apply out_col in H7.
      eapply col_permutation_2.
      eapply (col_transitivity_1 _ C'').
        assumption.
        assumption.
      apply col_permutation_1.
      assumption.
    assert(HH:=l11_4_1 A B C A' B' C' H1).
    spliter.
    assert(Cong A C A' C'').
      apply H16.
      repeat split; try assumption.
        left.
        apply between_trivial.
        left.
        apply between_trivial.
        left.
        apply between_trivial.
        auto.
        unfold out in  H7.
        spliter.
        assumption.
        apply cong_commutativity.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Cong_3 B C A B' C'' A').
      repeat split.
        apply cong_symmetry.
        assumption.
        apply cong_commutativity.
        assumption.
      apply cong_commutativity.
      assumption.
    assert(Conga B C A B' C'' A').
      apply cong3_conga.
        auto.
        apply not_col_distincts in H.
        spliter.
        assumption.
      assumption.
    assert(Conga B' C' A' B' C'' A').
      eapply conga_trans.
        apply conga_sym.
        apply H0.
      assumption.
    apply not_col_distincts in H.
    apply not_col_distincts in H10.
    spliter.
    clear H16.
    induction(eq_dec_points C' C'').
      induction (eq_dec_points C' C'').
        subst C''.
        split.
          assumption.
        split.
          apply cong_symmetry.
          assumption.
        assert(Cong_3 C A B C' A' B').
          repeat split.
            apply cong_commutativity.
            assumption.
            apply cong_commutativity.
            apply cong_symmetry.
            assumption.
          assumption.
        apply cong3_conga.
          auto.
          auto.
        assumption.
      apply False_ind.
      apply H27.
      assumption.
    assert(~Col C'' C' A').
      intro.
      apply H10.
      apply col_permutation_1.
      eapply col_transitivity_1.
        apply H16.
        apply col_permutation_4.
        assumption.
      apply col_permutation_3.
      apply out_col.
      assumption.
    apply not_col_distincts in H27.
    spliter.
    unfold out in H7.
    spliter.
    induction H32.
      assert(HH:=l11_41 ).
      assert(HH1:=l11_41 C'' C' A' B' H27 (between_symmetry _ _ _ H32) H7).
      spliter.
      assert(Conga B' C' A' C'' C' A').
        eapply (l11_10 B' C' A' B' C' A').
          apply conga_refl.
            auto.
          assumption.
          apply out_trivial.
          assumption.
          apply out_trivial.
          auto.
          apply bet_out.
            auto.
            assumption.
          apply  between_symmetry.
          assumption.
        apply out_trivial.
        auto.
      assert(lta B' C' A' A' C'' B').
        eapply conga_preserves_lta.
          apply conga_sym.
          apply H35.
          apply conga_refl.
            auto.
          auto.
        assumption.
      unfold lta in H36.
      spliter.
      apply conga_right_comm in H20.
      contradiction.
    assert(~Col C' C'' A').
      intro.
      apply H27.
      apply col_permutation_4.
      assumption.
    assert(HH1:=l11_41 C' C'' A' B' H33 (between_symmetry _ _ _ H32) H15).
    spliter.
    assert(Conga B' C'' A' C' C'' A').
      eapply (l11_10 B' C'' A' B' C'' A').
        apply conga_refl.
          auto.
        auto.
        apply out_trivial.
        assumption.
        apply out_trivial.
        auto.
        apply bet_out.
          auto.
          assumption.
        apply  between_symmetry.
        assumption.
      apply out_trivial.
      auto.
    assert(lta B' C'' A' A' C' B').
      eapply conga_preserves_lta.
        apply conga_sym.
        apply H36.
        apply conga_refl.
          auto.
        auto.
      assumption.
    unfold lta in H37.
    spliter.
    apply conga_sym in H20.
    apply conga_right_comm in H20.
    contradiction.
Qed.

Lemma l11_51 : forall A B C A' B' C',
  Distincts A B C -> Cong A B A' B' -> Cong A C A' C' -> Cong B C B' C' ->
  Conga B A C B' A' C' /\ Conga A B C A' B' C' /\ Conga B C A B' C' A'.
Proof.
    intros.
    assert(Cong_3 B A C B' A' C' /\ Cong_3 A B C A' B' C' /\ Cong_3 B C A B' C' A').
      repeat split; cong.
    spliter.
    unfold Distincts in H.
    spliter.
    split.
      apply cong3_conga.
        auto.
        auto.
      assumption.
    split.
      apply cong3_conga.
        assumption.
        auto.
      assumption.
    apply cong3_conga.
      assumption.
      assumption.
    assumption.
Qed.

Lemma conga_distinct : forall A B C D E F, Conga A B C D E F -> Conga A B C D E F /\ A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
    intros.
    split.
      assumption.
    unfold Conga in H.
    spliter.
    repeat split; assumption.
Qed.

Definition cong_preserves_le := l5_6.


Lemma bet_le_eq : forall A B C, Bet A B C -> le A C B C -> A = B.
Proof.
    intros.
    assert(le C B C A).
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

Lemma l11_52 : forall A B C A' B' C',
  Conga A B C A' B' C' -> Cong A C A' C' -> Cong B C B' C' -> le B C A C ->
  Cong B A B' A' /\ Conga B A C B' A' C' /\ Conga B C A B' C' A'.
Proof.
    intros.
    apply conga_distinct in H.
    spliter.
    assert(Cong B A B' A').
      induction(Col_dec A B C).
        unfold Col in H7.
        induction H7.
          assert(Bet A' B' C').
            eapply bet_conga_bet.
              apply H7.
            assumption.
          apply cong_commutativity.
          eapply l4_3.
            apply H7.
            apply H8.
            assumption.
          assumption.
        induction H7.
          assert(out B' A' C').
            eapply out_conga_out.
              apply bet_out.
                apply H4.
                apply H3.
              assumption.
            apply conga_left_comm.
            assumption.
          unfold out in H8.
          spliter.
          induction H10.
            assert(le B' C' A' C').
              eapply l5_6.
              repeat split.
                apply H2.
                assumption.
              assumption.
            assert(B'=A').
              eapply bet_le_eq.
                apply H10.
              assumption.
            subst B'.
            absurde.
          eapply l2_11.
            apply H7.
            apply H10.
            assumption.
          cong.
        assert(B = A).
          eapply bet_le_eq.
            apply between_symmetry.
            apply H7.
          assumption.
        subst B.
        absurde.
      assert(exists A'', out B' A'' A' /\ Cong B' A'' B A).
        apply l6_11_existence.
          assumption.
        auto.
      ex_and H8 A''.
      assert(Conga A' B' C' A'' B' C').
        eapply (l11_10  A'' _ C' A'' _ C' ).
          apply conga_refl.
            unfold out in H8.
            spliter.
            assumption.
          assumption.
          apply l6_6.
          assumption.
          apply out_trivial.
          auto.
          apply out_trivial.
          unfold out in H8.
          spliter.
          auto.
        apply out_trivial.
        auto.
      assert(Conga A B C A'' B' C').
        eapply l11_10.
          apply H.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A'' C' A C).
        eapply cong2_conga_cong.
          apply conga_sym.
          apply H11.
          cong.
        cong.
      assert(Cong_3 A'' B' C' A B C).
        repeat split; cong.
      assert(Cong A'' C' A' C').
        eapply cong_transitivity.
          apply H12.
        assumption.
      assert(~Col A' B' C').
        eapply ncol_conga_ncol.
          apply H7.
        assumption.
      assert(~Col A'' B' C').
        intro.
        apply H15.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ A'').
          intro.
          subst A''.
          unfold out in H8.
          spliter.
          absurde.
          permut.
        apply out_col in H8.
        permut.
      induction(eq_dec_points A'' A').
        subst A''.
        unfold Cong_3 in H13.
        spliter.
        cong.
      unfold out in H8.
      spliter.
      induction H19.
        assert(HH:= l11_41 A'' B' C' A' H16 H19 H17).
        spliter.
        assert(Cong A' C' A'' C').
          eapply (cong_transitivity _ _ A C).
            cong.
          unfold Cong_3 in H13.
          spliter.
          cong.
        assert(~Col A'' C' A').
          intro.
          apply H15.
          eapply (col_transitivity_1 _ A'' ).
            auto.
            apply bet_col in H19.
            permut.
          permut.
        assert (HH:= l11_44_1 A'' C' A' H23 ).
        destruct HH.
        apply cong_commutativity in H22.
        apply cong_symmetry in H22.
        apply H25 in H22.
        assert(~Col B' C' A'').
          intro.
          apply H16.
          permut.
        assert(Conga B' A' C' A'' A' C').
          eapply l11_10.
            apply conga_refl.
              3:apply out_trivial.
              auto.
            3:apply out_trivial.
            intro.
            subst C'.
            apply H15.
            apply col_trivial_3.
            auto.
            intro.
            subst C'.
            apply H15.
            apply col_trivial_3.
            apply between_symmetry in H19.
            apply bet_out in H19.
              assumption.
              assumption.
            auto.
          apply out_trivial.
          intro.
          subst C'.
          apply H15.
          apply col_trivial_3.
        assert(~Col B' C' A').
          intro.
          apply H15.
          permut.
        assert(HH:=l11_44_2 B' C' A' H28).
        destruct HH.
        assert(lt C' A'  C' B').
          apply H29.
          eapply conga_preserves_lta.
            apply conga_right_comm.
            apply conga_sym.
            apply H10.
            2:apply H21.
          eapply conga_trans.
            apply H22.
          apply conga_comm.
          apply conga_sym.
          assumption.
        assert(lt C' A'' C' B').
          unfold lt in H31.
          spliter.
          unfold lt.
          split.
            eapply l5_6.
            split.
              apply H31.
            split.
              apply cong_commutativity.
              cong.
            cong.
          intro.
          apply H32.
          eapply cong_transitivity.
            apply cong_commutativity.
            apply cong_symmetry.
            apply H14.
          assumption.
        unfold lt in H32.
        spliter.
        assert(le C A C B).
          eapply l5_6.
          repeat split.
            apply H32.
            apply cong_commutativity.
            assumption.
          apply cong_commutativity.
          cong.
        assert(Cong C A C B).
          apply le_anti_symmetry.
            assumption.
          apply le_comm.
          assumption.
        apply False_ind.
        apply H33.
        apply cong_symmetry.
        eapply cong_transitivity.
          apply cong_commutativity.
          apply cong_symmetry.
          apply H1.
        eapply cong_transitivity.
          apply cong_symmetry.
          apply H35.
        apply cong_commutativity.
        cong.
      assert(A' <> A'').
        auto.
      assert(HH:= l11_41 A' B' C' A'' H15 H19 H20).
      spliter.
      assert(Cong A' C' A'' C').
        eapply (cong_transitivity _ _ A C).
          cong.
        unfold Cong_3 in H13.
        spliter.
        cong.
      assert(~Col A'' C' A').
        intro.
        apply H15.
        eapply (col_transitivity_1 _ A'' ).
          auto.
          apply bet_col in H19.
          permut.
        permut.
      assert (HH:= l11_44_1 A'' C' A' H24 ).
      destruct HH.
      apply cong_commutativity in H23.
      apply cong_symmetry in H23.
      apply H26 in H23.
      assert(~Col B' C' A'').
        intro.
        apply H16.
        permut.
      assert(Conga B' A'' C' A' A'' C').
        eapply l11_10.
          apply conga_refl.
            3:apply out_trivial.
            auto.
          3:apply out_trivial.
          intro.
          subst C'.
          apply H16.
          apply col_trivial_3.
          auto.
          intro.
          subst C'.
          apply H16.
          apply col_trivial_3.
          apply between_symmetry in H19.
          apply bet_out in H19.
            assumption.
            assumption.
          auto.
        apply out_trivial.
        intro.
        subst C'.
        apply H16.
        apply col_trivial_3.
      assert(~Col B' C' A'').
        intro.
        apply H16.
        permut.
      assert(HH:=l11_44_2 B' C' A'' H29).
      destruct HH.
      assert(lt C' A''  C' B').
        apply H30.
        eapply conga_preserves_lta.
          apply conga_right_comm.
          apply conga_sym.
          apply conga_sym.
          apply H10.
          2:apply H22.
        eapply conga_trans.
          apply conga_sym.
          apply H23.
        apply conga_comm.
        apply conga_sym.
        assumption.
      assert(lt C' A' C' B').
        unfold lt in H32.
        spliter.
        unfold lt.
        split.
          eapply l5_6.
          split.
            apply H32.
          split.
            apply cong_commutativity.
            cong.
          cong.
        intro.
        apply H33.
        eapply cong_transitivity.
          apply cong_commutativity.
          apply H14.
        assumption.
      unfold lt in H33.
      spliter.
      assert(le C A C B).
        eapply l5_6.
        repeat split.
          apply H32.
          apply cong_commutativity.
          assumption.
        apply cong_commutativity.
        cong.
      assert(Cong C A C B).
        apply le_anti_symmetry.
          assumption.
        apply le_comm.
        assumption.
      apply False_ind.
      apply H34.
      apply cong_symmetry.
      eapply cong_transitivity.
        apply cong_commutativity.
        apply cong_symmetry.
        apply H1.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H36.
      apply cong_commutativity.
      cong.
    assert(Cong_3 A B C A' B' C').
      repeat split; cong.
    split.
      assumption.
    split.
      apply cong3_conga.
        auto.
        intro.
        subst C.
        apply le_zero in H2.
        subst B.
        absurde.
      auto with cong3.
    apply cong3_conga.
      auto.
      intro.
      subst C.
      apply le_zero in H2.
      subst B.
      absurde.
    auto with cong3.
Qed.

Lemma l11_53 : forall A B C D,
 Per D C B -> C <> D -> Distincts A B C -> Bet A B C ->
 lta C A D C B D /\ lt B D A D.
Proof.
    intros.
    unfold Distincts in H1.
    spliter.
    assert(~Col B A D).
      intro.
      assert(Col B C D).
        eapply (col_transitivity_1 _ A).
          auto.
          apply bet_col in H2.
          permut.
        permut.
      assert(~Col  B C D).
        apply per_not_col.
          assumption.
          assumption.
        apply l8_2.
        assumption.
      contradiction.
    assert(A <> D).
      intro.
      subst D.
      apply H5.
      apply col_trivial_2.
    assert( lta C A D C B D).
      assert(HH:=l11_41 B A D C H5 H2 H4).
      spliter.
      assert(Conga C A D B A D).
        eapply (l11_10  C A D C _ D).
          apply conga_refl.
            auto.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply bet_out.
            auto.
            auto.
          assumption.
        apply out_trivial.
        auto.
      eapply conga_preserves_lta.
        apply conga_sym.
        apply H9.
        apply conga_right_comm.
        apply conga_refl.
          intro.
          subst D.
          apply H5.
          apply col_trivial_3.
        auto.
      assumption.
    split.
      assumption.
    unfold Per in H.
    ex_and H B'.
    unfold is_midpoint in H.
    spliter.
    assert(HH:= H8).
    assert(~Col B D B').
      intro.
      apply H5.
      apply (col_transitivity_1 _ B').
        intro.
        subst B'.
        apply between_identity in H.
        contradiction.
        apply (col_transitivity_1 _ C).
          assumption.
          apply bet_col.
          assumption.
        apply bet_col in H2.
        permut.
      permut.
    destruct(l11_44_1 B D B').
      assumption.
    apply H12 in H8.
    destruct(l11_44_2 A D B').
      intro.
      apply H10.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ A).
        intro.
        subst B'.
        apply between_symmetry in H2.
        assert(B = C).
          eapply (between_egality _ _ A); assumption.
        contradiction.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ C).
          assumption.
          apply bet_col.
          assumption.
        apply bet_col in H2.
        permut.
      permut.
    assert(lta C A D C B' D).
      eapply conga_preserves_lta.
        apply conga_refl.
          auto.
        auto.
        apply conga_sym.
        eapply l11_10.
          3: apply out_trivial.
          apply conga_sym in H8.
          apply conga_comm in H8.
          apply H8.
          apply bet_out.
            intro.
            subst B'.
            apply cong_identity in H9.
            contradiction.
            intro.
            subst B'.
            apply between_identity in H.
            contradiction.
          apply between_symmetry.
          assumption.
          intro.
          subst B'.
          apply H10.
          apply col_trivial_2.
          apply bet_out.
            3: apply H.
            auto.
          intro.
          subst B'.
          apply between_identity in H.
          contradiction.
        apply out_trivial.
        intro.
        subst D.
        apply H10.
        apply col_trivial_1.
      assumption.
    assert(B' <> A).
      intro.
      subst B'.
      apply between_symmetry in H2.
      assert(B=C).
        eapply between_egality.
          apply H.
        assumption.
      contradiction.
    assert (lt D B' D A).
      apply l11_44_2_b.
        intro.
        apply H10.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ A).
          assumption.
          apply col_permutation_1.
          eapply (col_transitivity_1 _ C).
            assumption.
            apply bet_col.
            assumption.
          apply bet_col in H2.
          permut.
        permut.
      eapply (conga_preserves_lta D A C D B' C).
        eapply (l11_10).
          2: apply out_trivial.
          4: apply out_trivial.
          apply conga_refl.
            auto.
          5:apply out_trivial.
          assumption.
          auto.
          apply bet_out.
            auto.
            assumption.
          eapply outer_transitivity_between2.
            apply H2.
            assumption.
          assumption.
          auto.
        auto.
        eapply (l11_10).
          2: apply out_trivial.
          4: apply out_trivial.
          apply conga_refl.
            intro.
            subst B'.
            apply H10.
            apply col_trivial_2.
          5:apply out_trivial.
          auto.
          intro.
          subst B'.
          apply H10.
          apply col_trivial_2.
          apply bet_out.
            intro.
            subst B'.
            apply cong_identity in H9.
            contradiction.
            auto.
          eapply outer_transitivity_between.
            apply between_symmetry.
            apply H.
            apply between_symmetry.
            assumption.
          auto.
          intro.
          subst B'.
          apply H10.
          apply col_trivial_2.
        auto.
      apply lta_comm.
      assumption.
    unfold lt in H17.
    spliter.
    unfold lt.
    split.
      eapply l5_6.
      repeat split.
        apply H17.
        cong.
      apply cong_pseudo_reflexivity.
    intro.
    apply H18.
    eapply cong_transitivity.
      apply cong_symmetry.
      apply HH.
    apply cong_commutativity.
    assumption.
Qed.

Lemma hilbert_s_version_of_pasch_aux : forall A B C I P,
  ~ Col A I P -> ~ Col B C P -> Bet B I C -> B <> I -> I <> C -> B <> C ->
  exists X, Col I P X /\
            ((Bet A X B /\ A <> X /\ X <> B /\ A <> B) \/
             (Bet A X C /\ A <> X /\ X <> C /\ A <> C)).
Proof.
intros A B C I P HNC HNC' HBet HBI HIC HBC.
assert (HTS : two_sides I P B C).
  {
  assert_diffs; split; Col.
  assert_cols; split; try (intro; apply HNC'; ColR).
  split; try (intro; apply HNC'; ColR).
  exists I; Col.
  }
elim (two_sides_dec I P A B); intro HTS'.

  {
  destruct HTS' as [Hc1 [Hc2 [Hc3 [T [HCol HBet']]]]].
  exists T; split; Col.
  left; split; Col.
  split; try (intro; treat_equalities; Col).
  split; intro; treat_equalities; Col.
  }

  {
  rename HTS' into HOS.
  assert (HTS' : two_sides I P A C).
    {
    apply l9_8_2 with B; Col.
    apply not_two_sides_one_side; unfold two_sides in HTS; spliter; assert_diffs; Col.
    intro; apply HOS; apply l9_2; Col.
    }
  destruct HTS' as [Hc1 [Hc2 [Hc3 [T [HCol HBet']]]]].
  exists T; split; Col.
  right; split; Col.
  split; try (intro; treat_equalities; Col).
  split; intro; treat_equalities; Col.
  }
Qed.

Lemma not_one_side_two_sides :
 forall A B X Y,
  A <> B ->
  ~ Col X A B ->
  ~ Col Y A B ->
  ~ one_side A B X Y ->
  two_sides A B X Y.
Proof.
    intros.
    intros.
    induction(two_sides_dec A B X Y).
      assumption.
    apply not_two_sides_one_side in H3; try assumption.
    contradiction.
Qed.

Lemma one_or_two_sides :
 forall A B X Y,
  ~ Col X A B ->
  ~ Col Y A B ->
  two_sides A B X Y \/ one_side A B X Y.
Proof.
intros.
induction(two_sides_dec A B X Y).
left.
assumption.
right.
apply not_two_sides_one_side in H1; try assumption.
intro;subst;Col.
Qed.

Lemma all_coplanar : forall A B C D, coplanar A B C D.
Proof.
intros.
elim (Col_dec A B C); Cop; intro HABC.
elim (Col_dec A B D); Cop; intro HABD.
elim (Col_dec A C D); Cop; intro HACD.
elim (one_or_two_sides A B C D); Col; elim (one_or_two_sides A C B D); Col.

  {
  intros HTS1 HTS2; destruct HTS1 as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]].
  clear Hc1; clear Hc2; clear Hc3; exists I; right; left; assert_cols; Col.
  }

  {
  intros HOS HTS; destruct HTS as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]].
  clear Hc1; clear Hc2; clear Hc3; exists I; left; assert_cols; Col.
  }

  {
  intros HTS HOS; destruct HTS as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]].
  clear Hc1; clear Hc2; clear Hc3; exists I; right; left; assert_cols; Col.
  }

  {
  intros HOS1 HOS2; destruct (l9_31 A B D C) as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]];
  try (apply one_side_symmetry; auto); clear Hc1; clear Hc2; clear Hc3;
  exists I; right; right; assert_cols; Col.
  }
Qed.

End T11.
