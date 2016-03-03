Require Export GeoCoq.Axioms.tarski_axioms.

Ltac prolong A B x C D :=
 assert (sg:= segment_construction A B C D);
 ex_and sg x.

Ltac cases_equality A B := elim (eq_dec_points A B);intros.

Section T1_1.

Context `{M:Tarski_neutral_dimensionless}.

Lemma cong_reflexivity : forall A B,
 Cong A B A B.
Proof.
    intros.
    apply (cong_inner_transitivity B A A B); apply cong_pseudo_reflexivity.
Qed.

Lemma cong_symmetry : forall A B C D : Tpoint,
 Cong A B C D -> Cong C D A B.
Proof.
    intros.
    eapply cong_inner_transitivity.
      apply H.
    apply cong_reflexivity.
Qed.

Lemma cong_transitivity : forall A B C D E F : Tpoint,
 Cong A B C D -> Cong C D E F -> Cong A B E F.
Proof.
    intros.
    eapply cong_inner_transitivity; eauto using cong_symmetry.
Qed.

Lemma cong_left_commutativity : forall A B C D,
 Cong A B C D -> Cong B A C D.
Proof.
    intros.
    eapply cong_inner_transitivity.
      apply cong_symmetry.
      apply cong_pseudo_reflexivity.
    assumption.
Qed.

Lemma cong_right_commutativity : forall A B C D,
 Cong A B C D -> Cong A B D C.
Proof.
    intros.
    apply cong_symmetry.
    apply cong_symmetry in H.
    apply cong_left_commutativity.
    assumption.
Qed.

Lemma cong_trivial_identity : forall A B : Tpoint,
 Cong A A B B.
Proof.
    intros.
    prolong A B E A A.
    eapply cong_inner_transitivity.
      apply H0.
    assert(B=E).
      eapply cong_identity.
      apply H0.
    subst.
    apply cong_reflexivity.
Qed.

Lemma cong_reverse_identity : forall A C D,
 Cong A A C D -> C=D.
Proof.
    intros.
    apply cong_symmetry in H.
    eapply cong_identity.
    apply H.
Qed.

Lemma cong_commutativity : forall A B C D,
 Cong A B C D -> Cong B A D C.
Proof.
    intros.
    apply cong_left_commutativity.
    apply cong_right_commutativity.
    assumption.
Qed.

End T1_1.

Hint Resolve cong_commutativity cong_reverse_identity cong_trivial_identity
             cong_left_commutativity cong_right_commutativity
             cong_transitivity cong_symmetry cong_reflexivity cong_identity : cong.

Ltac Cong := auto with cong.
Ltac eCong := eauto with cong.

Section T1_2.

Context `{M:Tarski_neutral_dimensionless}.

Definition OFSC A B C D A' B' C' D' :=
  Bet A B C /\ Bet A' B' C' /\
  Cong A B A' B' /\ Cong B C B' C' /\
  Cong A D A' D' /\ Cong B D B' D'.

Lemma five_segment_with_def : forall A B C D A' B' C' D',
 OFSC A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof.
    unfold OFSC.
    intros;spliter.
    apply (five_segment A A' B B'); assumption.
Qed.

Lemma cong_diff : forall A B C D : Tpoint,
 A <> B -> Cong A B C D -> C <> D.
Proof.
    intros.
    intro.
    subst.
    apply H.
    eauto using cong_identity.
Qed.

Lemma cong_diff_2 : forall A B C D ,
 B <> A -> Cong A B C D -> C <> D.
Proof.
    intros.
    intro;subst.
    apply H.
    symmetry.
    eauto using cong_identity, cong_symmetry.
Qed.

Lemma cong_diff_3 : forall A B C D ,
 C <> D -> Cong A B C D -> A <> B.
Proof.
    intros.
    intro;subst.
    apply H.
    eauto using cong_identity, cong_symmetry.
Qed.

Lemma cong_diff_4 : forall A B C D ,
 D <> C -> Cong A B C D -> A <> B.
Proof.
    intros.
    intro;subst.
    apply H.
    symmetry.
    eauto using cong_identity, cong_symmetry.
Qed.

Definition Cong_3 A B C A' B' C' := Cong A B A' B' /\ Cong A C A' C' /\ Cong B C B' C'.

Lemma cong_3_sym : forall A B C A' B' C',
 Cong_3 A B C A' B' C' -> Cong_3 A' B' C' A B C.
Proof.
    unfold Cong_3.
    intuition.
Qed.

Lemma cong_3_swap : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong_3 B A C B' A' C'.
Proof.
    unfold Cong_3.
    intuition.
Qed.

Lemma cong_3_swap_2 : forall A B C A' B' C',
 Cong_3 A B C A' B' C' -> Cong_3 A C B A' C' B'.
Proof.
    unfold Cong_3.
    intuition.
Qed.

Lemma cong3_transitivity : forall A0 B0 C0 A1 B1 C1 A2 B2 C2,
 Cong_3 A0 B0 C0 A1 B1 C1 -> Cong_3 A1 B1 C1 A2 B2 C2 -> Cong_3 A0 B0 C0 A2 B2 C2.
Proof.
    unfold Cong_3.
    intros.
    spliter.
    repeat split; eCong.
Qed.

End T1_2.

Hint Resolve cong_3_sym : cong.
Hint Resolve cong_3_swap cong_3_swap_2 cong3_transitivity : cong3.
Hint Unfold Cong_3 : cong3.

Section T1_3.

Context `{M:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma l2_11 : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst B.
      assert (A' = B') by (apply (cong_identity A' B' A); Cong).
      subst; Cong.
    apply cong_commutativity; apply (five_segment A A' B B' C C' A A'); Cong.
Qed.

Lemma construction_unicity : forall Q A B C X Y,
 Q <> A -> Bet Q A X -> Cong A X B C -> Bet Q A Y -> Cong A Y B C -> X=Y.
Proof.
    intros.
    assert (Cong A X A Y) by eCong.
    assert (Cong Q X Q Y) by (apply (l2_11 Q A X Q A Y);Cong).
    assert(OFSC Q A X Y Q A X X) by (unfold OFSC;repeat split;Cong).
    apply five_segment_with_def in H6; try assumption.
    apply cong_identity with X; Cong.
Qed.

Lemma Cong_cases :
 forall A B C D,
 Cong A B C D \/ Cong A B D C \/ Cong B A C D \/ Cong B A D C \/
 Cong C D A B \/ Cong C D B A \/ Cong D C A B \/ Cong D C B A ->
 Cong A B C D.
Proof.
    intros.
    decompose [or] H; Cong.
Qed.

Lemma Cong_perm :
 forall A B C D,
 Cong A B C D ->
 Cong A B C D /\ Cong A B D C /\ Cong B A C D /\ Cong B A D C /\
 Cong C D A B /\ Cong C D B A /\ Cong D C A B /\ Cong D C B A.
Proof.
    intros.
    repeat split; Cong.
Qed.

End T1_3.
