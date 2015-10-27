(** We describe here a variant of the axiom system proposed by T.J.M. Makarios in June 2013. *)
(** This variant has a slightly different five_segment  axioms and allows to remove the 
    cong_pseudo_reflexivity axiom.
    All axioms have been shown to be independent except cong_identity and inner_pasch. *)

Class Tarski_neutral_dimensionless_variant := {
 MTpoint : Type;
 BetM : MTpoint -> MTpoint -> MTpoint -> Prop;
 CongM : MTpoint -> MTpoint -> MTpoint -> MTpoint -> Prop;
 Mbetween_identity : forall A B : MTpoint, BetM A B A -> A = B;
 Mcong_identity : forall A B C : MTpoint, CongM A B C C -> A = B;
 Mcong_inner_transitivity : forall A B C D E F : MTpoint,
   CongM A B C D -> CongM A B E F -> CongM C D E F;
 Minner_pasch : forall A B C P Q : MTpoint,
      BetM A P C -> BetM B Q C ->
      exists x, BetM P x B /\ BetM Q x A;
 Mfive_segment : forall A A' B B' C C' D D' : MTpoint,
    CongM A B A' B' ->
    CongM B C B' C' ->
    CongM A D A' D' ->
    CongM B D B' D' ->
    BetM A B C -> BetM A' B' C' -> A <> B -> CongM D C C' D';
 Msegment_construction : forall A B C D : MTpoint,
    exists E : MTpoint, BetM A B E /\ CongM B E C D;
 Mlower_dim : exists A, exists B, exists C, ~ (BetM A B C \/ BetM B C A \/ BetM C A B)
 }.