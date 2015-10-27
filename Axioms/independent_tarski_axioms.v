Class independent_Tarski_neutral_dimensionless := {
 TpointG : Type;
 BetG : TpointG -> TpointG -> TpointG -> Prop;
 CongG : TpointG -> TpointG -> TpointG -> TpointG -> Prop;
 bet_inner_transitivityG : forall A B C D, BetG A B D -> BetG B C D -> BetG A B C;
 bet_symmetryG : forall A B C, BetG A B C -> BetG C B A;
 cong_pseudo_reflexivityG : forall A B, CongG A B B A;
 cong_identityG : forall A B C, CongG A B C C -> A = B;
 cong_inner_transitivityG : forall A B C D E F,
   CongG A B E F -> CongG C D E F -> CongG A B C D;
 inner_paschG : forall A B C P Q,
   BetG A P C -> BetG B Q C ->
   A <> P -> P <> C -> B <> Q -> Q <> C ->
   ~ (BetG A B C \/ BetG B C A \/ BetG C A B) ->
   exists x, BetG P x B /\ BetG Q x A;
 five_segmentG : forall A A' B B' C C' D D',
   CongG A B A' B' -> CongG B C B' C' -> CongG A D A' D' -> CongG B D B' D' ->
   BetG A B C -> BetG A' B' C' -> A <> B -> CongG C D C' D';
 segment_constructionG : forall A B C D,
   exists E, BetG A B E /\ CongG B E C D;
 lower_dimG : exists A, exists B, exists C, ~ (BetG A B C \/ BetG B C A \/ BetG C A B)
}.

Class independent_Tarski_2D `(TnG : independent_Tarski_neutral_dimensionless) := {
 upper_dimG : forall A B C P Q,
   P <> Q -> A <> B -> A <> C -> B <> C ->
   CongG A P A Q -> CongG B P B Q -> CongG C P C Q ->
   (BetG A B C \/ BetG B C A \/ BetG C A B)
}.

Class independent_Tarski_2D_euclidean `(T2DG : independent_Tarski_2D) := {
 euclidG : forall A B C D T,
   BetG A D T -> BetG B D C ->
   ~ (BetG A B C \/ BetG B C A \/ BetG C A B) ->
   exists x, exists y, BetG A B x /\ BetG A C y /\ BetG x T y
}.