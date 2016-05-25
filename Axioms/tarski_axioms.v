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
 cong_pseudo_reflexivity : forall A B, Cong A B B A;
 cong_inner_transitivity : forall A B C D E F,
   Cong A B C D -> Cong A B E F -> Cong C D E F;
 cong_identity : forall A B C, Cong A B C C -> A = B;
 segment_construction : forall A B C D,
   exists E, Bet A B E /\ Cong B E C D;
 five_segment : forall A A' B B' C C' D D',
   Cong A B A' B' ->
   Cong B C B' C' ->
   Cong A D A' D' ->
   Cong B D B' D' ->
   Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D';
 between_identity : forall A B, Bet A B A -> A = B;
 inner_pasch : forall A B C P Q,
   Bet A P C -> Bet B Q C ->
   exists X, Bet P X B /\ Bet Q X A;
 lower_dim : exists A, exists B, exists C,
   ~ (Bet A B C \/ Bet B C A \/ Bet C A B)
}.

Class Tarski_neutral_dimensionless_with_decidable_point_equality
 `(Tn : Tarski_neutral_dimensionless) := {
 point_equality_decidability : forall A B : Tpoint, A = B \/ ~ A = B
}.

Class Tarski_2D
 `(TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality) := {
 upper_dim : forall A B C P Q,
   P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
   (Bet A B C \/ Bet B C A \/ Bet C A B)
}.

Class Tarski_2D_euclidean `(T2D : Tarski_2D) := {
 euclid : forall A B C D T,
   Bet A D T -> Bet B D C -> A<>D ->
   exists X, exists Y,
   Bet A B X /\ Bet A C Y /\ Bet X T Y
}.