Require Export GeoCoq.Main.Tarski_dev.Ch02_cong.

Section T2_1.

Context {Tn : Tarski_neutral_dimensionless}.

Lemma bet_col : forall A B C, Bet A B C -> Col A B C.
Proof. intros; unfold Col; auto. Qed.

Lemma between_trivial : forall A B, Bet A B B.
Proof.
intros A B; prolong A B x B B.
assert (x = B); [|subst; assumption].
apply cong_reverse_identity with B; Cong.
Qed.

Lemma between_symmetry : forall A B C, Bet A B C -> Bet C B A.
Proof.
intros A B C HB1; assert (HB2 : Bet B C C) by (apply between_trivial).
destruct (inner_pasch A B C B C HB1 HB2) as [I [HB3 HB4]].
apply between_identity in HB3; subst; assumption.
Qed.

(** This lemma is used by tactics for trying several permutations. *)
Lemma Bet_cases : forall A B C,
  Bet A B C \/ Bet C B A ->
  Bet A B C.
Proof. intros; decompose [or] H; auto using between_symmetry. Qed.

Lemma Bet_perm : forall A B C,
  Bet A B C ->
  Bet A B C /\ Bet C B A.
Proof. intros; auto using between_symmetry. Qed.

Lemma between_trivial2 : forall A B, Bet A A B.
Proof. intros; apply between_symmetry, between_trivial. Qed.

Lemma between_equality : forall A B C,
  Bet A B C -> Bet B A C ->
  A = B.
Proof.
intros A B C HB1 HB2.
destruct (inner_pasch A B C B A HB1 HB2) as [I [HB3 HB4]].
apply between_identity in HB3, HB4; congruence.
Qed.

Lemma between_equality_2 : forall A B C,
  Bet A B C -> Bet A C B ->
  B = C.
Proof. intros; apply between_equality with A; auto using between_symmetry. Qed.

Lemma between_exchange3 : forall A B C D,
  Bet A B C -> Bet A C D -> Bet B C D.
Proof.
intros A B C D HB1 HB2; apply between_symmetry in HB1, HB2.
destruct (inner_pasch C D A B C HB1 HB2) as [I [HB3 HB4]].
assert (C = I); [|subst; assumption].
apply between_identity; assumption.
Qed.

Lemma bet_neq12__neq : forall A B C,
  Bet A B C -> A <> B ->
  A <> C.
Proof. intros A B C HB HD H; subst; apply HD, between_identity, HB. Qed.

Lemma bet_neq21__neq : forall A B C,
  Bet A B C -> B <> A ->
  A <> C.
Proof. intros; apply (bet_neq12__neq _ B); auto. Qed.

Lemma bet_neq23__neq : forall A B C,
  Bet A B C -> B <> C ->
  A <> C.
Proof. intros A B C HB HD H; subst; apply (bet_neq21__neq C B C); auto. Qed.

Lemma bet_neq32__neq : forall A B C,
  Bet A B C -> C <> B -> A <> C.
Proof. intros; apply (bet_neq23__neq _ B); auto. Qed.

Lemma not_bet_distincts : forall A B C, ~ Bet A B C -> A <> B /\ B <> C.
Proof.
intros A B C HF; split; intro; subst; apply HF;
[apply between_trivial2|apply between_trivial].
Qed.

End T2_1.

(** Some tactics *)

#[global]
Hint Resolve between_symmetry : between.
#[global]
Hint Resolve between_trivial between_trivial2 : between_no_eauto.

Ltac eBetween := eauto with between.
Ltac Between := auto with between between_no_eauto.

Ltac not_exist_hyp_perm_col A B C := not_exist_hyp (Col A B C); not_exist_hyp (Col A C B);
                                 not_exist_hyp (Col B A C); not_exist_hyp (Col B C A);
                                 not_exist_hyp (Col C A B); not_exist_hyp (Col C B A).

Ltac assert_cols :=
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;assert (Col X1 X2 X3) by (apply bet_col;apply H)
 end.

Ltac clean_trivial_hyps :=
  repeat
  match goal with
   | H : Cong ?X1 ?X1 ?X2 ?X2 |- _ => clear H
   | H : Cong ?X1 ?X2 ?X2 ?X1 |- _ => clear H
   | H : Cong ?X1 ?X2 ?X1 ?X2 |- _ => clear H
   | H : Bet ?X1 ?X1 ?X2      |- _ => clear H
   | H : Bet ?X2 ?X1 ?X1      |- _ => clear H
   | H : Col ?X1 ?X1 ?X2      |- _ => clear H
   | H : Col ?X2 ?X1 ?X1      |- _ => clear H
   | H : Col ?X1 ?X2 ?X1      |- _ => clear H
end.

Ltac clean_reap_hyps_step_ch03 :=
  match goal with
   | H : Col ?A ?B ?C,     H2 : Col ?A ?C ?B     |- _ => clear H2
   | H : Col ?A ?B ?C,     H2 : Col ?B ?A ?C     |- _ => clear H2
   | H : Col ?A ?B ?C,     H2 : Col ?B ?C ?A     |- _ => clear H2
   | H : Col ?A ?B ?C,     H2 : Col ?C ?B ?A     |- _ => clear H2
   | H : Col ?A ?B ?C,     H2 : Col ?C ?A ?B     |- _ => clear H2
   | H : Bet ?A ?B ?C,     H2 : Bet ?C ?B ?A     |- _ => clear H2
   | H : Cong ?A ?B ?C ?D, H2 : Cong ?A ?B ?D ?C |- _ => clear H2
   | H : Cong ?A ?B ?C ?D, H2 : Cong ?C ?D ?A ?B |- _ => clear H2
   | H : Cong ?A ?B ?C ?D, H2 : Cong ?C ?D ?B ?A |- _ => clear H2
   | H : Cong ?A ?B ?C ?D, H2 : Cong ?D ?C ?B ?A |- _ => clear H2
   | H : Cong ?A ?B ?C ?D, H2 : Cong ?D ?C ?A ?B |- _ => clear H2
   | H : Cong ?A ?B ?C ?D, H2 : Cong ?B ?A ?C ?D |- _ => clear H2
   | H : Cong ?A ?B ?C ?D, H2 : Cong ?B ?A ?D ?C |- _ => clear H2
   | H : ?A <> ?B,         H2 : ?B <> ?A         |- _ => clear H2
  end.

Ltac clean_reap_hyps := clean_duplicated_hyps; repeat clean_reap_hyps_step_ch03.

Ltac clean := clean_trivial_hyps; clean_reap_hyps.

Ltac smart_subst X := subst X; clean.

Ltac treat_equalities_aux :=
  repeat
  match goal with
   | H:(?X1 = ?X2) |- _ => smart_subst X2
end.

Ltac treat_equalities :=
treat_equalities_aux;
repeat
  match goal with
   | H : Cong ?X3 ?X3 ?X1 ?X2 |- _ =>
      apply cong_symmetry in H; apply cong_identity in H;smart_subst X2
   | H : Cong ?X1 ?X2 ?X3 ?X3 |- _ =>
      apply cong_identity in H;smart_subst X2
   | H : Bet ?X1 ?X2 ?X1 |- _ => apply between_identity in H;smart_subst X2
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in assert (T : A=B) by (apply (between_equality A B C); Between);
                       smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?A ?C ?B |- _ =>
     let T := fresh in assert (T : B=C) by (apply (between_equality_2 A B C); Between);
                       smart_subst B
   | H : Bet ?A ?B ?C, H2 : Bet ?C ?A ?B |- _ =>
     let T := fresh in assert (T : A=B) by (apply (between_equality A B C); Between);
                       smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?C ?A |- _ =>
     let T := fresh in assert (T : B=C) by (apply (between_equality_2 A B C); Between);
                       smart_subst A
end.

Ltac show_distinct X Y := assert (X<>Y);[intro;treat_equalities|idtac].

Section T2_2.

Context {Tn    : Tarski_neutral_dimensionless}
        {TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.

Lemma between_inner_transitivity : forall A B C D,
  Bet A B D -> Bet B C D ->
  Bet A B C.
Proof.
intros A B C D HB1 HB2; destruct (inner_pasch A B D B C HB1 HB2) as [I []].
treat_equalities; Between.
Qed.

Lemma outer_transitivity_between2 : forall A B C D,
  Bet A B C -> Bet B C D -> B <> C ->
  Bet A C D.
Proof.
intros A B C D HB1 HB2 HD; prolong A C x C D.
assert (x = D); [|subst; assumption].
apply (construction_uniqueness B C C D); Cong.
apply (between_exchange3 A B C x); assumption.
Qed.

End T2_2.

#[global]
Hint Resolve outer_transitivity_between2 between_inner_transitivity between_exchange3 : between.

Section T2_3.

Context {Tn    : Tarski_neutral_dimensionless}
        {TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.

Lemma between_exchange2 : forall A B C D,
  Bet A B D -> Bet B C D ->
  Bet A C D.
Proof.
intros A B C D HB1 HB2.
induction (eq_dec_points B C); subst; eBetween.
Qed.

Lemma outer_transitivity_between : forall A B C D,
  Bet A B C -> Bet B C D -> B <> C ->
  Bet A B D.
Proof.
intros A B C D HB1 HB2 HD; apply between_symmetry.
apply (outer_transitivity_between2 _ C); Between.
Qed.

Lemma between_exchange4 : forall A B C D,
  Bet A B C -> Bet A C D ->
  Bet A B D.
Proof.
intros A B C D HB1 HB2.
apply between_symmetry, (between_exchange2 _ C); Between.
Qed.

End T2_3.

#[global]
Hint Resolve between_exchange2 outer_transitivity_between between_exchange4 : between.

Section T2_4.

Context {Tn    : Tarski_neutral_dimensionless}
        {TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.

Lemma l3_9_4 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 -> Bet_4 A4 A3 A2 A1.
Proof. unfold Bet_4; intros;spliter; Between. Qed.

Lemma l3_17 : forall A B C A' B' P,
  Bet A B C -> Bet A' B' C -> Bet A P A' ->
  exists Q, Bet P Q C /\ Bet B Q B'.
Proof.
intros A B C A' B' P HB1 HB2 HB3.
assert (HD : exists Q', Bet B' Q' A /\ Bet P Q' C)
  by (apply (inner_pasch C A A' B' P); Between).
destruct HD as [Q' [HB4 HB5]].
assert (HD : exists Q, Bet B Q B' /\ Bet Q' Q C)
  by (apply (inner_pasch C B' A B Q'); Between).
destruct HD as [Q [HB6 HB7]].
exists Q; eBetween.
Qed.

(** The prove the former version of lower dimension axiom for compatibility. *)

Lemma lower_dim_ex : exists A B C,
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof. exists PA, PB, PC; apply lower_dim. Qed.

Lemma two_distinct_points : exists X, exists Y : Tpoint, X <> Y.
Proof.
destruct lower_dim_ex as [A [B [C HNC]]]; exists A, B.
intro; subst; apply HNC; left; Between.
Qed.

Lemma point_construction_different : forall A B,
  exists C, Bet A B C /\ B <> C.
Proof.
intros A B; destruct two_distinct_points as [X [Y HD]].
prolong A B F X Y; exists F; split; [|intro; treat_equalities]; Between.
Qed.

Lemma another_point : forall A : Tpoint, exists B, A <> B.
Proof.
intro A; destruct (point_construction_different A A) as [B []].
exists B; assumption.
Qed.

Lemma BetSEq : forall A B C,
  BetS A B C <-> Bet A B C /\ A <> B /\ A <> C /\ B <> C.
Proof.
unfold BetS; split; [intros [HB [HAB HBC]]|tauto].
repeat split; auto; intro; treat_equalities; auto.
Qed.

End T2_4.

Section Beeson_1.

(** Another proof of l2_11 without eq_dec_points but using Cong stability
inspired by Micheal Beeson. #<a href="http://www.michaelbeeson.com/research/papers/AxiomatizingConstructiveGeometry.pdf"></a> # *)

Context {Tn : Tarski_neutral_dimensionless}.

Variable Cong_stability : forall A B C D, ~ ~ Cong A B C D -> Cong A B C D.

Lemma l2_11_b : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' ->
 Cong A B A' B' -> Cong B C B' C' ->
 Cong A C A' C'.
Proof.
intros A B C A' B' C' HB1 HB2 HC1 HC2; apply Cong_stability; intro HNC.
assert (HAB : A <> B) by (intro; treat_equalities; Cong).
cut (Cong C A C' A'); [Cong| apply (five_segment _ _ _ _ _ _ _ _ HC1); Cong].
Qed.

Lemma cong_dec_eq_dec_b :
  (forall A B : Tpoint, ~~ A = B -> A = B).
Proof.
intros A B HAB; apply (cong_identity _ _ A), Cong_stability.
intro HNC; apply HAB; intro; subst; apply HNC; Cong.
Qed.

End Beeson_1.

Section Beeson_2.

Context {Tn : Tarski_neutral_dimensionless}.

Variable Bet_stability : forall A B C, ~ ~ Bet A B C -> Bet A B C.

Lemma bet_dec_eq_dec_b :
  (forall A B : Tpoint, ~~ A = B -> A = B).
Proof.
intros A B HAB; apply between_identity, Bet_stability; intro HNB.
apply HAB; intro; subst; apply HNB; Between.
Qed.

End Beeson_2.