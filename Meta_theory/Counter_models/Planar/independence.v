Section Axioms.

Variable Point : Type.

Variable Bet : Point -> Point -> Point -> Prop.

Variable Cong : Point -> Point -> Point -> Point -> Prop.

Variable PA PB PC : Point.

Definition point_equality_decidability :=
  forall A B : Point, A = B \/ ~ A = B.

(* This axiom was denoted by A2 in Gupta's PhD thesis. *)

Definition bet_inner_transitivityP := forall A B C D,
  Bet A B D -> Bet B C D -> Bet A B C.

(* This axiom was denoted by A4 in Gupta's PhD thesis. *)

Definition cong_pseudo_reflexivityP := forall A B, Cong A B B A.

(* This axiom was denoted by A5 in Gupta's PhD thesis. *)

Definition cong_identityP := forall A B C, Cong A B C C -> A = B.

(* This axiom was denoted by A6 in Gupta's PhD thesis. *)

Definition cong_inner_transitivityP := forall A B C D E F,
  Cong A B E F -> Cong C D E F -> Cong A B C D.

(* This axiom corresponds to part of A7 from Gupta's PhD thesis. This is Pasch's axiom from which the degenerate cases have been removed. *)

Definition inner_paschP := forall A B C P Q,
  Bet A P C -> Bet B Q C ->
  A <> P -> P <> C -> B <> Q -> Q <> C ->
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B) ->
  exists X, Bet P X B /\ Bet Q X A.

(* This axiom corresponds to part of A7 from Gupta's PhD thesis. This is the axiom of symmetry of betweenness which can be derived from a degenerate cases of Pasch's axiom. *)

Definition bet_symmetryP := forall A B C, Bet A B C -> Bet C B A.

Definition Col A B C := Bet A B C \/ Bet B C A \/ Bet C A B.

Definition Coplanar A B C D :=
  exists X, (Col A B X /\ Col C D X) \/
            (Col A C X /\ Col B D X) \/
            (Col A D X /\ Col B C X).

Definition Par_strict A B C D :=
  A <> B /\ C <> D /\ Coplanar A B C D /\ ~ exists X, Col X A B /\ Col X C D.

Definition Par A B C D :=
  Par_strict A B C D \/ (A <> B /\ C <> D /\ Col A C D /\ Col B C D).

(* This axiom is equivalent to the previous one when assuming A0, A2, A4-A7, A9-A11. *)

Definition euclidP := forall A B C D P Q,
  Par A B C D -> Col A B P -> ~ Col A B Q -> Coplanar C D P Q ->
  exists Y, Col P Q Y /\ Col C D Y.

(* This axiom was denoted by A9 in Gupta's PhD thesis. *)

Definition five_segmentP := forall A A' B B' C C' D D',
  Cong A B A' B' -> Cong B C B' C' -> Cong A D A' D' -> Cong B D B' D' ->
  Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D'.

(* This axiom was denoted by A10 in Gupta's PhD thesis. However an hypothesis has been added to only non-null segments to be extended. *)

Definition segment_constructionP := forall A B C D,
  exists E, Bet A B E /\ Cong B E C D.

(* This axiom was denoted by A11 in Gupta's PhD thesis. *)

Definition lower_dimP := ~ Col PA PB PC.

(* This axiom was denoted by A12 in Gupta's PhD thesis. *)

Definition upper_dimP := forall A B C P Q,
  P <> Q -> A <> B -> A <> C -> B <> C ->
  Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  Col A B C.

(* This axiom was denoted by A13 in Gupta's PhD thesis. *)

Definition continuityP := forall (Xi Upsilon : Point -> Prop),
  (exists A, forall X Y, Xi X -> Upsilon Y -> Bet A X Y) ->
  (exists B, forall X Y, Xi X -> Upsilon Y -> B = X \/ B = Y \/ Bet X B Y).

End Axioms.
