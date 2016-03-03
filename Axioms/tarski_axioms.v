Require Export GeoCoq.Utils.general_tactics.

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
      exists X, Bet P X B /\ Bet Q X A;
 five_segment : forall A A' B B' C C' D D' : Tpoint,
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

Class Tarski_2D_euclidean `(T2D : Tarski_2D) := {
  euclid : forall A B C D T : Tpoint,
    Bet A D T -> Bet B D C -> A<>D ->
    exists X, exists Y,
    Bet A B X /\ Bet A C Y /\ Bet X T Y
}.

Class EqDecidability U := {
 eq_dec_points : forall A B : U, A=B \/ ~ A=B
}.
