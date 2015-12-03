Require Export GeoCoq.Meta_theory.Decidability.equivalence_between_decidability_properties_of_basic_relations.

Section T5.

Context `{M:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma l5_1 : forall A B C D,
  A<>B -> Bet A B C -> Bet A B D -> Bet A C D \/ Bet A D C.
Proof.
apply eq_dec_implies_l5_1; apply eq_dec_points.
Qed.

Lemma l5_2 : forall A B C D,
  A<>B -> Bet A B C -> Bet A B D -> Bet B C D \/ Bet B D C.
Proof.
apply eq_dec_implies_l5_2; apply eq_dec_points.
Qed.

Lemma segment_construction_2 :
  forall A Q B C, A<>Q -> exists X, (Bet Q A X \/ Bet Q X A) /\ Cong Q X B C.
Proof.
apply eq_dec_implies_segment_construction_2; apply eq_dec_points.
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
 le A B C D -> Cong A B A' B' -> Cong C D C' D' -> le A' B' C' D'.
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

Definition cong_preserves_le := l5_6.

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
apply eq_dec_implies_between_cong; apply eq_dec_points.
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
apply eq_dec_implies_between_cong_3; apply eq_dec_points.
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
    assert (T=D) by (eapply between_equality;eBetween).
    subst T.
    Cong.
Qed.

Lemma Cong_dec : forall A B C D,
  Cong A B C D \/ ~ Cong A B C D.
Proof.
apply eq_dec_cong_dec; apply eq_dec_points.
Qed.

Lemma Bet_dec : forall A B C, Bet A B C  \/  ~ Bet A B C.
Proof.
apply eq_dec_bet_dec; apply eq_dec_points.
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

Lemma cong__le : forall A B C D, Cong A B C D -> le A B C D.
Proof.
  intros A B C D H.
  exists D.
  split.
  Between.
  Cong.
Qed.

Lemma le1221 : forall A B, le A B B A.
Proof.
  intros A B.
  apply cong__le; Cong.
Qed.

Lemma le_left_comm : forall A B C D, le A B C D -> le B A C D.
Proof.
  intros A B C D Hle.
  apply (le_transitivity _ _ A B); auto.
  apply le1221; auto.
Qed.

Lemma le_right_comm : forall A B C D, le A B C D -> le A B D C.
Proof.
  intros A B C D Hle.
  apply (le_transitivity _ _ C D); auto.
  apply le1221; auto.
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
    assumption.
Qed.


Definition lt := fun A B C D => le A B C D /\ ~ Cong A B C D.
Definition gt := fun A B C D => lt C D A B.

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

Lemma cong2_lt__lt : forall A B C D A' B' C' D',
 lt A B C D -> Cong A B A' B' -> Cong C D C' D' -> lt A' B' C' D'.
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

Lemma l5_12_b : forall A B C, Col A B C -> le A B A C -> le B C A C -> Bet A B C.
Proof.
    intros.
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

Lemma lt__le : forall A B C D, lt A B C D -> le A B C D.
Proof.
    intros A B C D Hlt.
    destruct Hlt.
    assumption.
Qed.

Lemma le1234_lt__lt : forall A B C D E F, le A B C D -> lt C D E F -> lt A B E F.
Proof.
    intros A B C D E F Hle Hlt.
    destruct Hlt as [Hle' HNCong].
    split.
      apply (le_transitivity _ _ C D); auto.
    intro.
    apply HNCong.
    apply le_anti_symmetry; auto.
    apply (cong_preserves_le A B C D); Cong.
Qed.

Lemma le3456_lt__lt : forall A B C D E F, lt A B C D -> le C D E F -> lt A B E F.
Proof.
    intros A B C D E F Hlt Hle.
    destruct Hlt as [Hle' HNCong].
    split.
      apply (le_transitivity _ _ C D); auto.
    intro.
    apply HNCong.
    apply le_anti_symmetry; auto.
    apply (cong_preserves_le C D E F); Cong.
Qed.

Lemma not_and_lt : forall A B C D, ~ (lt A B C D /\ lt C D A B).
Proof.
    intros A B C D.
    intro HInter.
    destruct HInter as [[Hle HNCong] []].
    apply HNCong.
    apply le_anti_symmetry; assumption.
Qed.

Lemma nlt : forall A B, ~ lt A B A B.
Proof.
    intros A B Hlt.
    apply (not_and_lt A B A B).
    split; assumption.
Qed.

End T5.

Hint Resolve le_reflexivity le_anti_symmetry le_trivial le_zero cong__le le1221
             le_left_comm le_right_comm le_comm lt__le : le.

Ltac Le := auto with le.