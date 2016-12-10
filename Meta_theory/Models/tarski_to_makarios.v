Require Export GeoCoq.Axioms.tarski_axioms.
Require Export GeoCoq.Axioms.makarios_variant_axioms.

(** In this file we formalize the result given in T. J. M. Makarios:
 A further simplification of Tarski's axioms of geometry, June 2013. *)

Section Tarski83_to_Makarios_variant.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_reflexivity : forall A B,
 Cong A B A B.
Proof.
intros.
apply (cong_inner_transitivity B A A B);
apply cong_pseudo_reflexivity.
Qed.

Lemma cong_symmetry : forall A B C D : Tpoint,
 Cong A B C D -> Cong C D A B.
Proof.
intros.
eapply cong_inner_transitivity.
apply H.
apply cong_reflexivity.
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

Lemma five_segment' : forall A A' B B' C C' D D' : Tpoint,
    Cong A B A' B' ->
    Cong B C B' C' ->
    Cong A D A' D' ->
    Cong B D B' D' ->
    Bet A B C -> Bet A' B' C' -> A <> B -> Cong D C C' D'.
Proof.
intros.
apply cong_left_commutativity.
eapply five_segment with A A' B B';auto.
Qed.

Lemma lower_dim_ex : 
 exists A B C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists PA.
exists PB. 
exists PC.
apply lower_dim.
Qed.

Instance Makarios_Variant_follows_from_Tarski : Tarski_neutral_dimensionless_variant.
Proof.
exact (Build_Tarski_neutral_dimensionless_variant
 Tpoint Bet Cong
 point_equality_decidability
 cong_identity
 cong_inner_transitivity
 segment_construction
 five_segment'
 between_identity
 inner_pasch
 PA PB PC
 lower_dim).
Qed.

End Tarski83_to_Makarios_variant.

Section Makarios_variant_to_Tarski83.

Context `{MTn:Tarski_neutral_dimensionless_variant}.

Ltac prolong A B x C D :=
 assert (sg:= Msegment_construction A B C D);
 ex_and sg x.

Lemma Mcong_reflexivity : forall A B,
 CongM A B A B.
Proof.
intros.
prolong B A x A B.
eapply Mcong_inner_transitivity with A x;auto.
Qed.

Lemma Mcong_symmetry : forall A B C D ,
 CongM A B C D -> CongM C D A B.
Proof.
intros.
eapply Mcong_inner_transitivity.
apply H.
apply Mcong_reflexivity.
Qed.


Lemma between_trivial : forall A B : MTpoint, BetM A B B.
Proof.
intros.
prolong A B x B B.
assert (x = B)
 by (apply Mcong_identity in H0;auto).
subst;assumption.
Qed.

Lemma between_symmetry : forall A B C : MTpoint, BetM A B C -> BetM C B A.
Proof.
intros.
assert (BetM B C C).
apply between_trivial.
assert(exists x, BetM B x B /\ BetM C x A)
 by (eapply Minner_pasch;eauto).
ex_and H1 x.
apply Mbetween_identity in H1.
subst;assumption.
Qed.

Lemma cong_pseudo_reflexivity : forall A B : MTpoint, CongM A B B A.
Proof.
intros.
prolong B A x B A.
induction (Mpoint_equality_decidability x A).
subst.
apply Mcong_symmetry in H0.
assert (B=A)
 by (apply Mcong_identity with A;assumption).
subst;auto.

apply between_symmetry in H.
assert (CongM x A x A) by ( apply Mcong_reflexivity;auto).
assert (CongM A B A B) by ( apply Mcong_reflexivity;auto).
assert (CongM A A A A) by ( apply Mcong_reflexivity;auto).
apply Mfive_segment with x x A A;auto.
Qed.

Lemma Mcong_left_commutativity : forall A B C D,
 CongM A B C D -> CongM B A C D.
Proof.
intros.
eapply Mcong_inner_transitivity.
apply Mcong_symmetry.
apply cong_pseudo_reflexivity.
assumption.
Qed.

Lemma five_segment : forall A A' B B' C C' D D' : MTpoint,
    CongM A B A' B' ->
    CongM B C B' C' ->
    CongM A D A' D' ->
    CongM B D B' D' ->
    BetM A B C -> BetM A' B' C' -> A <> B -> CongM C D C' D'.
Proof.
intros.
apply Mcong_left_commutativity.
apply Mfive_segment with A A' B B';auto.
Qed.

Instance Tarski_follows_from_Makarios_Variant : Tarski_neutral_dimensionless.
Proof.
exact (Build_Tarski_neutral_dimensionless
 MTpoint BetM CongM
 cong_pseudo_reflexivity
 Mcong_inner_transitivity
 Mcong_identity
 Msegment_construction
 five_segment
 Mbetween_identity
 Minner_pasch
 MPA MPB MPC
 Mlower_dim).
Defined.

Instance Tarski_follows_from_Makarios_Variant' :
  Tarski_neutral_dimensionless_with_decidable_point_equality Tarski_follows_from_Makarios_Variant.
Proof. split; apply Mpoint_equality_decidability. Defined.

End Makarios_variant_to_Tarski83.
