Require Export Ch05_bet_le.

Ltac eCol := eauto with col.

Section T6_1.

Context `{M:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Definition out P A B := A<>P /\ B<>P /\ (Bet P A B \/ Bet P B A).

Lemma bet_out : forall A B C, B <> A -> C <> A -> Bet A B C -> out A B C.
Proof.
    intros.
    unfold out.
    tauto.
Qed.

Lemma out_dec : forall P A B, out P A B \/ ~ out P A B.
Proof.
    intros.
    unfold out.
    elim (Bet_dec P A B);intro; elim (Bet_dec P B A);intro; elim (eq_dec_points A P);intro; elim (eq_dec_points B P);intro; tauto.
Qed.

Lemma out_diff1 : forall A B C, out A B C -> B <> A.
Proof.
    intros.
    unfold out in H.
    spliter.
    assumption.
Qed.

Lemma out_diff2 : forall A B C, out A B C -> C <> A.
Proof.
    intros.
    unfold out in H.
    spliter.
    assumption.
Qed.

Lemma out_distinct : forall A B C, out A B C -> B <> A /\ C <> A.
Proof.
    intros.
    split.
      eapply out_diff1;eauto.
    eapply out_diff2;eauto.
Qed.

Lemma out_col : forall A B C, out A B C -> Col A B C.
Proof.
    intros.
    unfold Col.
    unfold out in H.
    spliter.
    induction H1;Between.
Qed.

Lemma l6_2 : forall A B C P,  A<>P -> B<>P -> C<>P -> Bet A P C -> (Bet B P C <-> out P A B).
Proof.
    intros.
    unfold out.
    split.
      intros.
      repeat split; try assumption; eapply l5_2;eBetween.
    intro; spliter; induction H5; eBetween.
Qed.

Lemma l6_3_1 : forall A B P, out P A B -> (A<>P /\ B<>P /\ exists C, C<>P /\ Bet A P C /\ Bet B P C).
Proof.
    unfold out.
    intros.
    spliter.
    repeat split; try assumption.
    induction H1.
      assert(exists C, Bet A P C /\ P <> C) by (apply point_construction_different).
      ex_and H2 C.
      exists C.
      repeat split; eBetween.
    assert(exists C, Bet B P C /\ P <> C) by (apply point_construction_different).
    ex_and H2 C.
    exists C.
    repeat split;eBetween.
Qed.

Lemma l6_3_2 : forall A B P,
  (A<>P /\ B<>P /\ exists C, C<>P /\ Bet A P C /\ Bet B P C) -> out P A B.
Proof.
    intros.
    spliter.
    ex_and H1 C.
    unfold out.
    repeat split; try assumption; eapply l5_2; eBetween.
Qed.

Lemma l6_4_1 : forall A B P, out P A B -> Col A P B /\ ~ Bet A P B.
Proof.
    unfold out.
    intros.
    spliter.
    unfold Col.
    induction H1; split.
      Between.
      intro; apply H; eapply between_egality;eauto.
      right; left; assumption.
    intro; apply H0; eapply between_egality; eBetween.
Qed.

Lemma l6_4_2 : forall A B P, Col A P B /\ ~ Bet A P B -> out P A B.
Proof.
    unfold Col.
    intros.
    spliter.
    unfold out.
    induction H.
      contradiction.
    induction (eq_dec_points A P).
      subst P; intuition.
    induction (eq_dec_points B P).
      subst P; intuition.
    induction H; repeat split; Between.
Qed.

(** out reflexivity. l6_5 *)

Lemma out_trivial : forall P A, A<>P -> out P A A.
Proof.
    intros.
    unfold out.
    repeat split; Between.
Qed.

(** out symmetry. *)

Lemma l6_6 : forall P A B, out P A B -> out P B A.
Proof.
    unfold out.
    intuition.
Qed.

(** out transitivity. *)

Lemma l6_7 : forall P A B C, out P A B -> out P B C -> out P A C.
Proof.
    unfold out.
    intros.
    spliter.
    repeat split; try assumption.
    induction H4; induction H2.
      left; eapply between_exchange4; eauto.
      eapply l5_3; eauto.
      eapply (l5_1 P B); auto.
    right; eBetween.
Qed.

Lemma bet_out_out_bet : forall A B C A' C',
 Bet A B C -> out B A A' -> out B C C' -> Bet A' B C'.
Proof.
    intros.
    unfold out in *.
    spliter.
    induction H5; induction H3.
      assert(Bet A' B C) by (apply outer_transitivity_between2 with A; Between).
      apply outer_transitivity_between with C; auto.
      assert(Bet A' B C) by (apply outer_transitivity_between2 with A; Between).
      apply between_inner_transitivity with C; assumption.
      assert(Bet A' B C) by (apply between_exchange3 with A; Between).
      apply outer_transitivity_between with C; auto.
    assert(Bet A' B C) by (apply between_exchange3 with A; Between).
    eapply between_inner_transitivity with C; assumption.
Qed.

Lemma out2_bet_out : forall A B C X P,
 out B A C -> out B X P -> Bet A X C -> out B A P /\ out B C P.
Proof.
    intros.
    unfold out in *.
    spliter.
    induction H5; induction H3.
      repeat split; try assumption.
        left; eapply between_exchange4 with X; try assumption.
        apply between_inner_transitivity with C; assumption.
      apply l5_1 with X; try auto.
      apply between_exchange2 with A; assumption.
      repeat split; try assumption.
        apply l5_3 with X; try assumption.
        apply between_inner_transitivity with C; assumption.
      right; apply between_exchange4 with X; try assumption.
      apply between_exchange2 with A; assumption.
      repeat split; try assumption.
        apply l5_1 with X; try auto.
        apply between_exchange2 with C; Between.
      left; apply between_exchange4 with X; try assumption.
      apply between_inner_transitivity with A; Between.
    repeat split; try assumption.
      right; apply between_exchange4 with X; try assumption.
      apply between_exchange2 with C; Between.
    apply l5_3 with X; try assumption.
    apply between_inner_transitivity with A; Between.
Qed.

Lemma l6_11_unicity : forall A B C R X Y,
  R<>A -> B<>C ->
  out A X R -> Cong A X B C ->
  out A Y R -> Cong A Y B C ->
  X=Y.
Proof.
    unfold out.
    intros.
    spliter.
    assert (Cong A X A Y) by eCong.
    induction H8; induction H6.
      apply l4_19 with A R; try assumption.
      apply l4_3 with A A; Between; Cong.
      assert (Bet A X Y) by eBetween.
      eapply between_cong; eauto.
      assert (Bet A Y X) by eBetween.
      apply sym_equal; apply between_cong with A; Cong.
    assert (Bet A X Y \/ Bet A Y X) by (eapply l5_1; eauto).
    induction H10.
      apply between_cong with A; assumption.
    apply sym_equal; apply between_cong with A; Cong.
Qed.

Lemma l6_11_existence : forall A B C R,
  R<>A -> B<>C -> exists X, out A X R /\ Cong A X B C.
Proof.
    intros.
    assert (exists X : Tpoint, (Bet A R X \/ Bet A X R) /\ Cong A X B C) by (apply (segment_construction_2);assumption).
    ex_and H1 X.
    exists X.
    unfold out;repeat split; try intro;treat_equalities;intuition.
Qed.

Lemma l6_13_1 : forall P A B, out P A B -> le P A P B -> Bet P A B.
Proof.
    unfold out.
    intros.
    spliter.
    induction H2; try assumption.
    unfold le in H0.
    ex_and H0 Y.
    assert(Y = A).
      apply (l6_11_unicity P P A B); Between; Cong.
        unfold out; repeat split; auto.
        intro; treat_equalities; auto.
      unfold out; repeat split; auto.
    subst Y; assumption.
Qed.

Lemma l6_13_2 : forall P A B, out P A B -> Bet P A B -> le P A P B.
Proof.
    intros.
    unfold le.
    exists A.
    split; eCong.
Qed.

Lemma l6_16_1 : forall P Q S X, P<>Q -> S<>P -> Col S P Q -> Col X P Q -> Col X P S.
Proof.
    intros.
    assert((Bet P S X \/ Bet P X S) -> (Bet P S X \/ Bet S X P)) by (intro; induction H3; Between).
    unfold Col.
    induction H1;induction H2.
      right; apply H3; eapply (l5_2 Q P); Between.
      induction H2; left; eBetween.
      induction H1; left; eBetween.
    induction H1; induction H2.
      right; apply H3; eapply l5_1; eauto.
      right; right; eBetween.
      right; left; eBetween.
    right; apply H3; eapply l5_3; eBetween.
Qed.

Lemma col_transitivity_1 : forall P Q A B,
  P<>Q -> Col P Q A -> Col P Q B -> Col P A B.
Proof.
    intros.
    induction (eq_dec_points A P).
      subst; unfold Col; Between.
    assert (T:=l6_16_1 P Q A B).
    apply col_permutation_1; apply T; Col.
Qed.

Lemma col_transitivity_2 : forall P Q A B,
 P<>Q -> Col P Q A -> Col P Q B -> Col Q A B.
Proof.
    intros.
    apply (col_transitivity_1 Q P A B);Col.
Qed.

(** Unicity of intersection *)

Lemma l6_21 : forall A B C D P Q,
  ~ Col A B C -> C<>D -> Col A B P -> Col A B Q -> Col C D P -> Col C D Q -> P=Q.
Proof.
    intros.
    elim (eq_dec_points P Q); intro; try assumption.
    cut False.
      intro; intuition.
    apply not_col_distincts in H.
    spliter.
    assert (Col C P Q) by (apply col_transitivity_1 with D; Col).
    assert (Col Q B C).
      induction (eq_dec_points Q A).
        subst; apply col_transitivity_1 with P; Col.
      apply col_transitivity_1 with P; try Col; apply col_permutation_1; apply col_transitivity_1 with A; Col.
    assert (Col A B C).
      induction (eq_dec_points Q A).
        subst Q; assumption.
      induction (eq_dec_points Q B).
        subst; apply col_permutation_2; apply col_transitivity_1 with P; try Col.
      apply col_permutation_2; apply col_transitivity_1 with Q; try Col.
    contradiction.
Qed.

End T6_1.

Hint Resolve col_transitivity_1 col_transitivity_2 : col.

Section T6_2.

Context `{M:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma l6_25 : forall A B,
 A<>B -> exists C, ~ Col A B C.
Proof.
    intros.
    assert (T:=lower_dim).
    induction T.
    induction H0.
    induction H0.
    induction (Col_dec A B x).
      induction(Col_dec A B x0).
        induction(Col_dec A B x1).
          induction (eq_dec_points A x).
            assert (~(Col x x0 x1)) by (unfold Col; auto).
            treat_equalities; eCol.
          assert (Col A x x0)  by eCol.
          assert (Col A x x1)  by eCol.
          assert (Col A x0 x1) by eCol.
          assert (Col x x0 x1) by eCol.
          contradiction.
        exists x1; assumption.
      exists x0; assumption.
    exists x; assumption.
Qed.

Lemma t2_8 : forall A B C D E : Tpoint,
 Bet A B C -> Bet D B E -> Cong A B D B -> Cong B C B E -> Cong A E C D.
Proof.
    intros.
    induction (eq_dec_points A B); try (treat_equalities; Cong).
    assert (Cong A B D B -> Cong B C B E -> Cong A D D A -> Cong B D B A -> Bet A B C -> Bet D B E -> A <> B -> Cong C D E A).
      apply five_segments.
    apply cong_symmetry.
    apply cong_right_commutativity.
    apply H4; Cong; Between.
Qed.

Lemma col3 : forall X Y A B C,
 X <> Y ->
 Col X Y A -> Col X Y B -> Col X Y C ->
 Col A B C.
Proof.
    intros.
    assert (Col X A B) by (apply col_transitivity_1 with Y; assumption).
    induction(eq_dec_points C X).
      subst X; apply col_permutation_1; assumption.
    apply col_permutation_1.
    apply col_transitivity_1 with X; try assumption.
      apply col_permutation_2.
      apply col_transitivity_1 with Y; assumption.
    apply col_permutation_2.
    apply col_transitivity_1 with Y; assumption.
Qed.

End T6_2.
