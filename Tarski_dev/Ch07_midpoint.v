Require Export GeoCoq.Tarski_dev.Ch06_out_lines.

Ltac not_exist_hyp_comm A B := not_exist_hyp (A<>B);not_exist_hyp (B<>A).

Ltac not_exist_hyp2 A B C D := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D].
Ltac not_exist_hyp3 A B C D E F := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F].

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

      | H:out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps
 end.

Section T7_1.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Definition is_midpoint M A B := Bet A M B /\ Cong A M M B.

Lemma is_midpoint_dec :
 forall I A B, is_midpoint I A B \/ ~ is_midpoint I A B.
Proof.
    intros.
    unfold is_midpoint.
    elim (Bet_dec A I B);intro; elim (Cong_dec A I I B);intro; tauto.
Qed.

Lemma is_midpoint_id : forall A B, is_midpoint A A B -> A = B.
Proof.
    intros.
    unfold is_midpoint in H.
    spliter.
    treat_equalities;reflexivity.
Qed.

Lemma is_midpoint_id_2 : forall A B, is_midpoint A B A -> A=B.
Proof.
    intros.
    unfold is_midpoint in *.
    spliter.
    apply cong_identity in H0.
    auto.
Qed.

Lemma l7_2 : forall M A B, is_midpoint M A B -> is_midpoint M B A.
Proof.
    unfold is_midpoint.
    intuition.
Qed.

Lemma l7_3 : forall M A, is_midpoint M A A -> M=A.
Proof.
    unfold is_midpoint.
    intros;spliter;repeat split;Between;Cong.
Qed.


Lemma l7_3_2 : forall A, is_midpoint A A A.
Proof.
    unfold is_midpoint.
    intros;repeat split;Between;Cong.
Qed.

(** This corresponds to l7_8 in Tarski's book. *)

Lemma symmetric_point_construction : forall A P, exists P', is_midpoint P A P'.
Proof.
    unfold is_midpoint.
    intros.
    prolong A P E A P.
    exists E.
    split;Cong;Between.
Qed.

Lemma symmetric_point_unicity : forall A P P1 P2, is_midpoint P A P1 -> is_midpoint P A P2 -> P1=P2.
Proof.
    unfold is_midpoint.
    intros.
    spliter.
    elim (eq_dec_points A P); intros.
      treat_equalities;auto.
    apply (construction_unicity A P A P);Cong.
Qed.

Lemma l7_9 : forall P Q A X, is_midpoint A P X -> is_midpoint A Q X -> P=Q.
Proof.
    unfold is_midpoint.
    intros.
    spliter.
    induction (eq_dec_points A X).
      treat_equalities;reflexivity.
    apply (construction_unicity X A X A);Cong;Between.
Qed.

Lemma l7_9_bis : forall P Q A X, is_midpoint A P X -> is_midpoint A X Q -> P=Q.
Proof.
intros; apply l7_9 with A X; unfold is_midpoint in *; split; spliter; Cong; Between.
Qed.

Lemma diff_bet : forall A B C, A <> B -> Bet A B C -> A <> C.
Proof.
    intros.
    intro.
    treat_equalities.
    auto.
Qed.

Lemma l7_13 : forall A P Q P' Q',  is_midpoint A P' P -> is_midpoint A Q' Q -> Cong P Q P' Q'.
Proof.
    unfold is_midpoint.
    intros.
    spliter.
    induction (eq_dec_points P A).
      treat_equalities;Cong.
    prolong P' P X Q A.
    prolong X P' X' Q A.
    prolong Q' Q Y P A.
    prolong Y Q' Y' P A.
    assert (Bet Y A Q') by eBetween.
    assert (Bet P' A X) by eBetween.
    assert (Bet A P X) by eBetween.
    assert(Bet Y Q A) by eBetween.
    assert (Bet A Q' Y') by eBetween.
    assert (Bet X' P' A) by eBetween.
    assert(Bet X A X') by eBetween.
    assert(Bet Y A Y') by eBetween.
    assert (Cong A X Y A) by (eapply l2_11;eCong).
    assert (Cong A Y' X' A).
      apply l2_11 with Q' P'; Between.
        apply cong_transitivity with A Q; Cong.
      apply cong_transitivity with A P; Cong.
    assert (Cong A Y A Y').
      apply (l2_11 A Q Y _ Q' Y'); Between; Cong.
      apply cong_transitivity with A P; Cong.
    assert (Cong X A Y' A) by (apply cong_transitivity with A Y; Cong).
    assert (Cong A X' A Y) by (apply cong_transitivity with A Y'; Cong).
    assert (FSC X A X' Y' Y' A Y X).
      unfold FSC;repeat split; Cong.
        apply bet_col;auto.
      eapply (l2_11 X A X' Y' A Y);Between.
    assert (A <> X).
      eapply diff_bet.
        intro.
        apply H3.
        apply sym_equal.
        apply H26.
      assumption.
    assert (Cong X' Y' Y X) by eauto using l4_16.
    assert (Cong A X A X') by (apply cong_transitivity with A Y; Cong).
    assert (IFSC Y Q A X Y' Q' A X') by (unfold IFSC, FSC in *;spliter;repeat split;Between; Cong).
    assert (Cong Q X Q' X') by eauto using l4_2.
    assert (IFSC X P A Q X' P' A Q') by (unfold IFSC;repeat split;Between;Cong).
    eauto using l4_2.
Qed.

Lemma l7_15 : forall P Q R P' Q' R' A,
 is_midpoint A P P' -> is_midpoint A Q Q' -> is_midpoint A R R' -> Bet P Q R -> Bet P' Q' R'.
Proof.
    intros.
    spliter.
    eapply l4_6.
      apply H2.
    unfold Cong_3.
    repeat split.
      eapply l7_13.
        apply l7_2.
        apply H.
      apply l7_2.
      assumption.
      eapply l7_13.
        apply l7_2.
        apply H.
      apply l7_2.
      assumption.
    eapply l7_13.
      apply l7_2.
      apply H0.
    apply l7_2.
    assumption.
Qed.


Lemma l7_16 : forall P Q R S P' Q' R' S' A,
  is_midpoint A P P' -> is_midpoint A Q Q' ->
  is_midpoint A R R' -> is_midpoint A S S' ->
  Cong P Q R S -> Cong P' Q' R' S'.
Proof.
    intros.
    assert (Cong P Q P' Q').
      eapply l7_13.
        apply l7_2.
        apply H.
      apply l7_2.
      apply H0.
    assert (Cong R S R' S').
      eapply l7_13.
        apply l7_2.
        apply H1.
      apply l7_2.
      apply H2.
    apply cong_transitivity with P Q; Cong.
    apply cong_transitivity with R S; Cong.
Qed.


Lemma symmetry_preserves_midpoint :
   forall A B C D E F Z,
 is_midpoint Z A D -> is_midpoint Z B E ->
 is_midpoint Z C F -> is_midpoint B A C -> is_midpoint E D F.
Proof.
    intros.
    unfold is_midpoint.
    unfold is_midpoint in H2.
    spliter.
    split.
      eapply l7_15;eauto.
    eapply l7_16;eauto.
Qed.

End T7_1.

Hint Resolve l7_13 : cong.
Hint Resolve l7_2 l7_3 l7_3_2 symmetric_point_construction symmetry_preserves_midpoint : midpoint.

Ltac Midpoint := auto with midpoint.

Section T7_2.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma Mid_cases :
  forall A B C,
  is_midpoint A B C \/ is_midpoint A C B ->
  is_midpoint A B C.
Proof.
    intros.
    decompose [or] H; Midpoint.
Qed.

Lemma Mid_perm :
  forall A B C,
  is_midpoint A B C ->
  is_midpoint A B C /\ is_midpoint A C B.
Proof.
    unfold is_midpoint.
    intros.
    spliter.
    repeat split; Between; Cong.
Qed.

Lemma l7_17 : forall P P' A B, is_midpoint A P P' -> is_midpoint B P P' -> A=B.
Proof.
    intros.
    assert (Cong P B P' B).
      unfold is_midpoint in *.
      spliter.
      Cong.
    assert (exists B', is_midpoint A B B') by (apply symmetric_point_construction).
    induction H2.
    assert (Cong P' B P x) by eauto with midpoint cong.
    assert (Cong P B P x) by (apply cong_transitivity with P' B; Cong).
    assert (Cong P B P' x) by eauto with midpoint cong.
    assert (Cong P' B P' x) by (apply cong_transitivity with P x; Cong; apply cong_transitivity with P B; Cong).
    assert (Bet P B P') by (unfold is_midpoint in *;spliter;assumption).
    assert (B=x) by (apply (l4_19 P P' B x);Between).
    subst x.
    apply l7_3.
    assumption.
Qed.

Lemma l7_17_bis : forall P P' A B, is_midpoint A P P' -> is_midpoint B P' P -> A=B.
Proof.
    intros.
    apply l7_17 with P P'; Midpoint.
Qed.

Lemma l7_20 : forall M A B,
  Col A M B -> Cong M A M B -> A=B \/ is_midpoint M A B.
Proof.
    unfold Col.
    intros.
    induction H.
      right.
      unfold is_midpoint.
      split.
        assumption.
      Cong.
    induction H.
      assert (Cong A B B B) by (apply (l4_3 A B M B B M);Between;Cong).
      treat_equalities;auto.
    assert (Cong B A A A) by (apply (l4_3 B A M A A M);Cong;Between).
    treat_equalities;auto.
Qed.

Lemma l7_20_bis : forall M A B, A<>B ->
  Col A M B -> Cong M A M B -> is_midpoint M A B.
Proof.
   intros.
   induction (l7_20 M A B H0 H1);intuition.
Qed.

Lemma cong_col_mid : forall A B C,
 A <> C -> Col A B C -> Cong A B B C ->
 is_midpoint B A C.
Proof.
    intros.
    apply l7_20 in H0.
      intuition subst.
    Cong.
Qed.

Lemma l7_21 : forall A B C D P,
  ~ Col A B C -> B<>D ->
  Cong A B C D -> Cong B C D A ->
  Col A P C -> Col B P D ->
  is_midpoint P A C /\ is_midpoint P B D.
Proof.
    intros.
    assert_diffs.
    assert (exists P', Cong_3 B D P D B P').
      eapply l4_14.
        Col.
      Cong.
    induction H9.
    assert (Col D B x) by
      (apply l4_13 with B D P;Col).
    assert (FSC B D P A D B x C).
      unfold FSC.
      unfold Cong_3 in *.
      spliter.
      repeat split; Cong; Col.
    assert (FSC B D P C D B x A).
      unfold FSC.
      unfold Cong_3 in *.
      spliter.
      repeat split; Col; Cong.
    assert (Cong P A x C) by (eauto using l4_16).
    assert (Cong P C x A) by (eauto using l4_16).
    assert (Cong_3 A P C C x A) by (unfold Cong_3;repeat split; Cong).
    assert (Col C x A) by (eauto using l4_13).
    assert (P=x).
      unfold FSC in *.
      spliter.
      apply (l6_21 A C B D); Col.
    subst x.
    unfold Cong_3 in *;spliter.
    split;apply l7_20_bis;Col;Cong.
Qed.

Lemma l7_22_aux : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 ->
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   is_midpoint M1 A1 B1 -> is_midpoint M2 A2 B2 ->
   le C A1 C A2 ->
   Bet M1 C M2.
Proof.
    intros.
    induction (eq_dec_points A2 C).
      subst C.
      apply le_zero in H5.
      subst A2.
      apply cong_reverse_identity in H1.
      subst B1.
      apply cong_reverse_identity in H2.
      subst B2.
      apply l7_3 in H4.
      subst A1.
      apply between_trivial.
    assert (exists A, is_midpoint C A2 A).
      apply symmetric_point_construction.
    induction H7.
    assert (exists B, is_midpoint C B2 B).
      apply symmetric_point_construction.
    induction H8.
    assert (exists M, is_midpoint C M2 M).
      apply symmetric_point_construction.
    induction H9.
    assert(is_midpoint x1 x x0).
      unfold is_midpoint.
      split.
        eapply l7_15.
          apply H7.
          apply H9.
          apply H8.
        unfold is_midpoint in H4.
        spliter.
        assumption.
      eapply l7_16.
        apply H7.
        apply H9.
        apply H9.
        apply H8.
      unfold is_midpoint in H4.
      spliter.
      assumption.
    assert (le C A1 C x).
      eapply l5_6.
      repeat split.
        apply H5.
        apply cong_reflexivity.
      unfold is_midpoint in H7.
      spliter.
      apply cong_left_commutativity.
      assumption.
    assert (Bet C A1 x).
      induction (eq_dec_points A1 C).
        subst A1.
        apply between_trivial2.
      eapply l6_13_1.
        unfold out.
        2:assumption.
      repeat split.
        assumption.
        intro.
        subst x.
        apply le_zero in H11.
        apply H12.
        subst A1.
        reflexivity.
      eapply l5_2.
        apply H6.
        apply between_symmetry.
        assumption; intro.
      unfold is_midpoint in H7.
      spliter.
      assumption.
    (* assert (M1=x).
    eauto with Midpoint.
    *)
    assert (le C B1 C x0).
      eapply l5_6.
        apply H11.
        assumption.
      unfold is_midpoint in *.
      spliter.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H16.
      eapply cong_transitivity.
        2:apply H15.
      apply cong_commutativity.
      assumption.
    assert (Bet C B1 x0).
      induction (eq_dec_points B1 C).
        subst B1.
        apply cong_symmetry in H1.
        apply cong_reverse_identity in H1.
        subst A1.
        apply between_trivial2.
      induction (eq_dec_points x0 C).
        subst x0.
        apply le_zero in H13.
        subst B1.
        apply between_trivial.
      induction (eq_dec_points B2 C).
        subst B2.
        apply cong_symmetry in H2.
        eapply cong_reverse_identity in H2.
        subst A2.
        apply le_zero in H5.
        subst A1.
        apply cong_reverse_identity in H1.
        subst B1.
        apply False_ind.
        apply H14.
        reflexivity.
      eapply l6_13_1.
        unfold out.
        repeat split.
          assumption.
          assumption.
        eapply l5_2.
          2:apply between_symmetry.
          2:apply H0.
          assumption.
        2:assumption.
      unfold is_midpoint in H8.
      spliter.
      assumption.
    assert (exists Q, Bet x1 Q C /\ Bet A1 Q B1).
      eapply l3_17.
        apply between_symmetry.
        apply H12.
        apply between_symmetry.
        apply H14.
      unfold is_midpoint in H10.
      spliter.
      assumption.
    ex_and H15 Q.
    assert (IFSC x A1 C x1 x0 B1 C x1).
      unfold IFSC.
      unfold is_midpoint in *.
      spliter.
      repeat split.
        apply between_symmetry.
        assumption.
        apply between_symmetry.
        assumption.
        eapply cong_transitivity.
          apply cong_commutativity.
          apply cong_symmetry.
          apply H20.
        eapply cong_transitivity.
          apply H2.
        apply cong_commutativity.
        assumption.
        apply cong_commutativity.
        assumption.
        apply cong_right_commutativity.
        assumption.
      apply cong_reflexivity.
    assert (Cong A1 x1 B1 x1).
      eapply l4_2.
      apply H17.
    assert (Cong Q A1 Q B1).
      induction(eq_dec_points C x1).
        subst x1.
        apply between_identity in H15.
        subst Q.
        apply cong_commutativity.
        assumption.
      eapply l4_17.
        apply H19.
        unfold Col.
        right; left.
        assumption.
        assumption.
      apply cong_commutativity.
      assumption.
    assert (is_midpoint Q A1 B1).
      unfold is_midpoint.
      split.
        assumption.
      apply cong_left_commutativity.
      assumption.
    assert (Q=M1).
      eapply l7_17.
        apply H20.
      assumption.
    subst Q.
    eapply between_exchange3.
      apply H15.
    unfold is_midpoint in H9.
    spliter.
    apply between_symmetry.
    assumption.
Qed.

(** This is Krippen lemma , proved by Gupta in its PhD in 1965 as Theorem 3.45 *)

Lemma l7_22 : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 ->
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   is_midpoint M1 A1 B1 -> is_midpoint M2 A2 B2 ->
   Bet M1 C M2.
Proof.
    intros.
    assert (le C A1 C A2 \/ le C A2 C A1).
      eapply le_cases.
    induction H5.
      eapply l7_22_aux.
        apply H.
        apply H0.
        apply H1.
        apply H2.
        assumption.
        assumption.
      assumption.
    apply between_symmetry.
    eapply l7_22_aux.
      7:apply H5.
      apply between_symmetry.
      apply H.
      5:apply H3.
      4:apply H4.
      apply between_symmetry.
      apply H0.
      assumption.
    assumption.
Qed.

Lemma bet_col1 : forall A B C D, Bet A B D -> Bet A C D -> Col A B C.
Proof.
    intros.
    assert(Bet A B C \/ Bet A C B).
      eapply l5_3.
        apply H.
      assumption.
    unfold Col.
    induction H1.
      left.
      assumption.
    right; left.
    apply between_symmetry.
    assumption.
Qed.

(* TODO: Should be remove if we have the right tactics *)
Lemma bet_col2 : forall A B C D,
 A <> B -> Bet A B C -> Bet A B D ->
 Col A C D.
Proof.
    intros.
    assert(Bet A D C \/ Bet A C D).
      eapply l5_1.
        apply H.
        assumption.
      assumption.
    unfold Col.
    induction H2.
      right; left.
      apply between_symmetry.
      assumption.
    left.
    assumption.
Qed.

Lemma l7_25 : forall A B C,
  Cong C A C B ->
  exists X, is_midpoint X A B.
Proof.
    intros.
    induction(Col_dec A B C).
      assert(A = B \/ is_midpoint C A B).
        apply l7_20.
          unfold Col in *.
          intuition.
        assumption.
      induction H1.
        subst B.
        exists A.
        apply l7_3_2.
      exists C.
      assumption.
    assert (exists P, Bet C A P /\ A<>P).
      apply point_construction_different.
    ex_and H1 P.
    prolong C B Q A P.
    assert (exists R, Bet A R Q /\ Bet B R P).
      eapply inner_pasch.
        apply between_symmetry.
        apply H1.
      apply between_symmetry.
      assumption.
    ex_and H5 R.
    assert (exists X, Bet A X B /\ Bet R X C).
      eapply inner_pasch.
        apply H1.
      assumption.
    ex_and H7 X.
    exists X.
    unfold is_midpoint.
    split.
      assumption.
    apply cong_left_commutativity.
    cut(Cong R A R B).
      intros.
      induction(eq_dec_points R C).
        subst R.
        assert (C = X).
          apply between_identity.
          assumption.
        subst X.
        assumption.
      eapply l4_17.
        apply H10.
        unfold Col.
        right; left.
        apply between_symmetry.
        assumption.
        assumption.
      assumption.
    assert (OFSC C A P B C B Q A).
      unfold OFSC.
      repeat split.
        assumption.
        assumption.
        assumption.
        apply cong_symmetry.
        assumption.
        apply cong_symmetry.
        assumption.
      apply cong_pseudo_reflexivity.
    assert (Cong P B Q A).
      eapply five_segment_with_def.
        eapply H9.
      unfold Col in H0.
      intuition.
      apply H0.
      subst A.
      apply between_trivial.
    assert (exists R', Bet A R' Q /\ Cong_3 B R P A R' Q).
      eapply l4_5.
        assumption.
      apply cong_commutativity.
      assumption.
    ex_and H11 R'.
    assert (IFSC B R P A A R' Q B).
      unfold IFSC.
      repeat split.
        assumption.
        assumption.
        apply cong_commutativity.
        assumption.
        unfold Cong_3 in H12.
        spliter.
        assumption.
        apply cong_pseudo_reflexivity.
      apply cong_commutativity.
      apply cong_symmetry.
      assumption.
    assert (IFSC B R P Q A R' Q P).
      unfold IFSC.
      repeat split;try assumption.
        apply cong_commutativity.
        assumption.
        unfold Cong_3 in H12.
        spliter.
        assumption.
      apply cong_pseudo_reflexivity.
    assert (Cong R A R' B).
      eapply l4_2.
      apply H13.
    assert (Cong R Q R' P).
      eapply l4_2.
      apply H14.
    assert (Cong_3 A R Q B R' P).
      unfold Cong_3.
      repeat split.
        apply cong_commutativity.
        assumption.
        apply cong_commutativity.
        apply cong_symmetry.
        assumption.
      assumption.
    assert (Col B R' P).
      eapply l4_13.
        2:apply H17.
      unfold Col.
      left.
      assumption.
    cut(R=R').
      intro.
      subst R'.
      assumption.
    assert (B <> P).
      unfold IFSC, OFSC, Cong_3 in *.
      spliter.
      intro.
      subst P.
      apply between_identity in H14.
      subst R.
      apply cong_reverse_identity in H12.
      subst R'.
      apply cong_reverse_identity in H32.
      subst Q.
      apply between_identity in H5.
      apply H2.
      assumption.
    assert (A <> Q).
      unfold IFSC, OFSC, Cong_3 in *.
      spliter.
      intro.
      subst Q.
      apply cong_reverse_identity in H20.
      subst P.
      apply H19.
      reflexivity.
    assert(B <> Q).
      intro.
      subst Q.
      apply cong_symmetry in H4.
      apply cong_identity in H4.
      subst P.
      apply H2.
      reflexivity.
    assert (B <> R).
      intro.
      unfold Cong_3, IFSC, OFSC in *.
      spliter.
      subst R.
      clean_duplicated_hyps.
      assert (Col B A C).
        eapply bet_col2.
          2:apply between_symmetry.
          2:apply H7.
          2:assumption.
        intro.
        apply cong_symmetry in H12.
        apply cong_identity in H12.
        subst R'.
        subst X.
        clean_duplicated_hyps.
        assert (Bet B A C \/ Bet B C A).
          eapply l5_2.
            2:apply between_symmetry.
            2:apply H5.
            intro.
            apply H21.
            rewrite H9.
            reflexivity.
          apply between_symmetry.
          assumption.
        apply H0.
        unfold Col.
        induction H9.
          right;right.
          apply between_symmetry.
          assumption.
        right; left.
        assumption.
      apply H0.
      apply col_permutation_4.
      assumption.
    eapply (l6_21 A Q B P R R' ).
      intro.
      unfold Col in H23.
      induction H23.
        assert(Bet A B C).
          eapply outer_transitivity_between2.
            apply H23.
            apply between_symmetry.
            assumption.
          intro.
          apply H21.
          rewrite H24.
          reflexivity.
        apply H0.
        unfold Col.
        left.
        assumption.
      induction H23.
        assert(Bet B A C \/ Bet B C A).
          eapply l5_2.
            2:apply H23.
            intro.
            apply H21.
            rewrite H24.
            reflexivity.
          apply between_symmetry.
          assumption.
        apply H0.
        unfold Col.
        induction H24.
          right;right.
          apply between_symmetry.
          assumption.
        right; left.
        assumption.
      assert(Bet A B C).
        eapply between_exchange3.
          apply between_symmetry.
          apply H23.
        apply between_symmetry.
        assumption.
      apply H0.
      unfold Col.
      left.
      assumption.
      assumption.
      unfold Col.
      right; left.
      apply between_symmetry.
      assumption.
      unfold Col.
      right; left.
      apply between_symmetry.
      assumption.
      unfold Col.
      right; left.
      apply between_symmetry.
      assumption.
    unfold Col.
    unfold Col in H18.
    induction H18.
      right; left.
      apply between_symmetry.
      assumption.
    induction H18.
      left.
      apply between_symmetry.
      assumption.
    right;right.
    apply between_symmetry.
    assumption.
Qed.

Lemma midpoint_distinct_1 : forall I A B,
 A<>B ->
 is_midpoint I A B ->
 I<>A /\ I<>B.
Proof.
    intros.
    split.
      intro.
      subst.
      unfold is_midpoint in *.
      decompose [and] H0.
      treat_equalities.
      intuition.
    intro;subst.
    unfold is_midpoint in *.
    decompose [and] H0.
    treat_equalities.
    intuition.
Qed.

Lemma midpoint_distinct_2 : forall I A B,
 I<>A ->
 is_midpoint I A B ->
 A<>B /\ I<>B.
Proof.
    intros.
    assert (A<>B).
      intro.
      unfold is_midpoint in *;spliter.
      treat_equalities.
      intuition.
    split.
      assumption.
    apply midpoint_distinct_1 in H0.
      intuition.
    intuition.
Qed.


Lemma midpoint_distinct_3 : forall I A B,
 I<>B ->
 is_midpoint I A B ->
 A<>B /\ I<>A.
Proof.
    intros.
    assert (A<>B).
      intro.
      unfold is_midpoint in *;spliter.
      treat_equalities.
      intuition.
    split.
      assumption.
    apply midpoint_distinct_1 in H0.
      intuition.
    intuition.
Qed.


Lemma midpoint_def : forall A B C, Bet A B C -> Cong A B B C -> is_midpoint B A C.
Proof.
    intros.
    unfold is_midpoint.
    split;assumption.
Qed.

Lemma midpoint_bet : forall A B C, is_midpoint B A C -> Bet A B C.
Proof.
    unfold is_midpoint.
    intros.
    elim H.
    intros.
    assumption.
Qed.

Lemma midpoint_col : forall A M B, is_midpoint M A B -> Col M A B.
Proof.
    intros.
    unfold Col.
    right;right.
    apply midpoint_bet.
    apply l7_2.
    assumption.
Qed.

Lemma midpoint_cong : forall A B C, is_midpoint B A C -> Cong A B B C.
Proof.
    unfold is_midpoint.
    intros.
    elim H.
    intros.
    assumption.
Qed.

Lemma midpoint_not_midpoint : forall I A B,
  A<>B ->
  is_midpoint I A B ->
~ is_midpoint B A I.
Proof.
    intros.
    assert (I<>B).
      apply midpoint_distinct_1 in H0.
        tauto.
      assumption.
    apply midpoint_bet in H0.
    intro.
    apply midpoint_bet in H2.
    assert (I=B).
      apply between_symmetry in H0.
      apply between_symmetry in H2.
      eapply between_equality.
        apply H2.
      apply H0.
    intuition.
Qed.

Lemma swap_diff : forall (A B : Tpoint), A<>B -> B<>A.
Proof.
    intuition.
Qed.

Lemma cong_cong_half_1 : forall A M B A' M' B',
 is_midpoint M A B -> is_midpoint M' A' B' ->
 Cong A B A' B' -> Cong A M A' M'.
Proof.
    intros.
    unfold is_midpoint in *.
    spliter.
    assert(exists M'', Bet A' M'' B' /\ Cong_3 A M B A' M'' B').
      eapply l4_5.
        assumption.
      assumption.
    ex_and H4 M''.
    assert (is_midpoint M'' A' B').
      unfold is_midpoint.
      split.
        assumption.
      unfold Cong_3 in H5.
      spliter.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H5.
      eapply cong_transitivity.
        apply H3.
      assumption.
    assert(M'=M'').
      eapply l7_17; unfold is_midpoint; split.
        apply H0.
        apply H2.
        apply H4.
      unfold is_midpoint in H6.
      spliter.
      assumption.
    subst M''.
    unfold Cong_3 in H5.
    spliter.
    assumption.
Qed.

Lemma cong_cong_half_2 : forall A M B A' M' B',
 is_midpoint M A B -> is_midpoint M' A' B' ->
 Cong A B A' B' -> Cong B M B' M'.
Proof.
    intros.
    apply cong_cong_half_1 with A A'.
      Midpoint.
      Midpoint.
    Cong.
Qed.

Lemma cong_mid2__cong13 : forall A M B A' M' B',
 is_midpoint M A B -> is_midpoint M' A' B' ->
 Cong A M A' M' -> Cong A B A' B'.
Proof.
    intros A M B A' M' B' HM HM' HCong.
    destruct HM.
    destruct HM'.
    apply (l2_11 _ M _ _ M'); auto.
    apply (cong_transitivity _ _ A' M'); auto.
    apply (cong_transitivity _ _ A M); Cong.
Qed.

Lemma le_mid2__le13 : forall A M B A' M' B',
 is_midpoint M A B -> is_midpoint M' A' B' ->
 le A M A' M' -> le A B A' B'.
Proof.
    intros A M B A' M' B' HM HM' Hle.
    destruct HM.
    destruct HM'.
    apply (bet2_le2__le _ M _ _ M'); auto.
    apply (l5_6 A M A' M'); auto.
Qed.

Lemma le_mid2__le12 : forall A M B A' M' B',
 is_midpoint M A B -> is_midpoint M' A' B' ->
 le A B A' B' -> le A M A' M'.
Proof.
    intros A M B A' M' B' HM HM' Hle.
    elim(le_cases A M A' M'); auto.
    intro.
    assert(le A' B' A B) by (apply (le_mid2__le13 _ M' _ _ M); auto).
    apply cong__le.
    apply (cong_cong_half_1 _ _ B _ _ B'); auto.
    apply le_anti_symmetry; auto.
Qed.

End T7_2.

Hint Resolve midpoint_bet : between.
Hint Resolve midpoint_col : col.
Hint Resolve midpoint_cong : cong.