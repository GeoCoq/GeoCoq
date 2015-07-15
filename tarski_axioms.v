Require Export general_tactics.

(** This version of the axioms of Tarski is the one given in 
 Wolfram Schwabhäuser, Wanda Szmielew and Alfred Tarski,
 Metamathematische Methoden in der Geometrie, Springer-Verlag, Berlin, 1983.

This axioms system is the result of a long history of axiom systems for geometry studied by
 Tarski, Schwabhäuser, Szmielew and Gupta.
*)

Class Tarski_neutral_dimensionless := {
 Tpoint : Type;
 Bet : Tpoint -> Tpoint -> Tpoint -> Prop;
 Cong : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop;
 between_identity : forall A B, Bet A B A -> A=B;
 cong_pseudo_reflexivity : forall A B : Tpoint, Cong A B B A;
 cong_identity : forall A B C : Tpoint, Cong A B C C -> A = B;
 cong_inner_transitivity : forall A B C D E F : Tpoint,
   Cong A B C D -> Cong A B E F -> Cong C D E F;
 inner_pasch : forall A B C P Q : Tpoint,
      Bet A P C -> Bet B Q C ->
      exists x, Bet P x B /\ Bet Q x A;
 five_segments : forall A A' B B' C C' D D' : Tpoint,
    Cong A B A' B' ->
    Cong B C B' C' ->
    Cong A D A' D' ->
    Cong B D B' D' ->
    Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D';
 segment_construction : forall A B C D : Tpoint,
    exists E : Tpoint, Bet A B E /\ Cong B E C D;
 lower_dim : exists A, exists B, exists C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B)
}.

Class Tarski_2D `(Tn : Tarski_neutral_dimensionless) := {
  upper_dim : forall A B C P Q : Tpoint,
    P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
    (Bet A B C \/ Bet B C A \/ Bet C A B)
}.

(** We replace Tarski's version of the parallel postulate by the triangle circumscription.
 The proof that these two axioms are classically equivalent can be found in Euclid.v
*)
Class Tarski_2D_euclidean `(T2D : Tarski_2D) := {
  euclid : forall A B C,
    ~ (Bet A B C \/ Bet B C A \/ Bet C A B) -> exists CC, Cong A CC B CC /\ Cong A CC C CC
}.

Class EqDecidability U := {
 eq_dec_points : forall A B : U, A=B \/ ~ A=B
}.
 
(** We describe here a variant of the axiom system proposed by T.J.M. Makarios in June 2013. *)
(** This variant has a slightly different five_segments axioms and allows to remove the 
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
 Mfive_segments : forall A A' B B' C C' D D' : MTpoint,
    CongM A B A' B' ->
    CongM B C B' C' ->
    CongM A D A' D' ->
    CongM B D B' D' ->
    BetM A B C -> BetM A' B' C' -> A <> B -> CongM D C C' D';
 Msegment_construction : forall A B C D : MTpoint,
    exists E : MTpoint, BetM A B E /\ CongM B E C D;
 Mlower_dim : exists A, exists B, exists C, ~ (BetM A B C \/ BetM B C A \/ BetM C A B)
 }.

(** We describe here an intuitionistic version of Tarski's axiom system proposed
by Michael Beeson. *)

Class intuitionistic_Tarski_neutral_dimensionless := {
 ITpoint : Type;
 IBet : ITpoint -> ITpoint -> ITpoint -> Prop;
 ICong : ITpoint -> ITpoint -> ITpoint -> ITpoint -> Prop;
 Cong_stability : forall A B C D, ~ ~ ICong A B C D -> ICong A B C D;
 Bet_stability : forall A B C, ~ ~ IBet A B C -> IBet A B C;
 IT (A B C : ITpoint) := ~ (A<>B /\ B<>C /\ ~ IBet A B C);
 ICol (A B C : ITpoint) :=  ~ (~ IT C A B /\ ~ IT A C B /\ ~ IT A B C);
 Ibetween_identity : forall A B, ~ IBet A B A;
 Icong_identity : forall A B C, ICong A B C C -> A = B;
 Icong_pseudo_reflexivity : forall A B : ITpoint, ICong A B B A;
 Icong_inner_transitivity : forall A B C D E F,
   ICong A B C D -> ICong A B E F -> ICong C D E F;
 Iinner_pasch : forall A B C P Q,
   IBet A P C -> IBet B Q C -> ~ ICol A B C -> 
   exists x, IBet P x B /\ IBet Q x A;
 Ibetween_symmetry : forall A B C, IBet A B C -> IBet C B A;
 Ibetween_inner_transitivity : forall A B C D, IBet A B D -> IBet B C D -> IBet A B C;
 Ifive_segments : forall A A' B B' C C' D D',
    ICong A B A' B' ->
    ICong B C B' C' ->
    ICong A D A' D' ->
    ICong B D B' D' ->
    IT A B C -> IT A' B' C' -> A <> B -> ICong C D C' D';
 Isegment_construction : forall A B C D,
    A<>B -> exists E, IT A B E /\ ICong B E C D;
 Ilower_dim : exists A, exists B, exists C, ~ IT C A B /\ ~ IT A C B /\ ~ IT A B C
}.

