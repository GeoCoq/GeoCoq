Require Export GeoCoq.Tarski_dev.Definitions.

Section Continuity_Defs.

Context `{Tn:Tarski_neutral_dimensionless}.

(** In this file, we introduce elementary continuity properties.
These properties are different variant to assert that the intersection
of line, segment and circles exists under some assumptions.
Adding one of these properties as axiom to the Tarski_2D type class gives us
a definition of ruler and compass geometry.
The links between these properties are in file elementary_continuity_props.v
*)


(** If there is a point P inside a circle, and Q outside then there is
    a point Z of the segment PQ which is on the circle. *)

Definition segment_circle := forall A B P Q,
  InCircle P A B ->
  OutCircle Q A B ->
  exists Z, Bet P Z Q /\ OnCircle Z A B.

(** Given a line UV which contains a point inside the circle, there is
   a point of line UV which is on the circle. *)

Definition one_point_line_circle := forall A B U V P,
  Col U V P -> U <> V -> Bet A P B ->
  exists Z, Col U V Z /\ OnCircle Z A B.

(** Given a line UV which contains a point P inside the circle, there are
  two points on line UV which belong to the circle and they are distinct if
 if P is strictly inside the circle. *)

Definition two_points_line_circle := forall A B U V P,
  Col U V P -> U <> V -> Bet A P B ->
  exists Z1 Z2, Col U V Z1 /\ OnCircle Z1 A B /\
                Col U V Z2 /\ OnCircle Z2 A B /\
                Bet Z1 P Z2 /\ (P <> B -> Z1 <> Z2).

(** Given two circles (A,B) and (C,D), if there are two points of (C,D)
 one inside and one outside (A,B) then there is a point of intersection
 of the two circles. *)

Definition circle_circle := forall A B C D P Q,
  OnCircle P C D ->
  OnCircle Q C D ->
  InCircle P A B ->
  OutCircle Q A B ->
  exists Z, OnCircle Z A B /\ OnCircle Z C D.

(** Given two circles (A,B) and (C,D),
   if there is a point of (A,B) which is inside (C,D)
  and vice-versa, then there is a point of intersection of the two circles. *)

Definition circle_circle_bis := forall A B C D P Q,
  OnCircle P C D ->
  InCircle P A B ->
  OnCircle Q A B ->
  InCircle Q C D ->
  exists Z, OnCircle Z A B /\ OnCircle Z C D.

(** Given two circles (A,B) and (C,D), if there are two points of (C,D)
 one inside and one outside (A,B) then there are two points of intersection
 of the two circles.
 They are distinct if the inside and outside properties are strict. *)

Definition circle_circle_two := forall A B C D P Q,
  OnCircle P C D ->
  OnCircle Q C D ->
  InCircle P A B ->
  OutCircle Q A B ->
  exists Z1 Z2,
    OnCircle Z1 A B /\ OnCircle Z1 C D /\
    OnCircle Z2 A B /\ OnCircle Z2 C D /\
    (InCircleS P A B -> OutCircleS Q A B -> Z1<>Z2).

(*
Definition weak_cantor_s_axiom := forall (A B:nat -> Tpoint),
  (forall n, Bet (A n) (A (S n)) (B (S n)) /\ Bet (A (S n)) (B (S n)) (B n) /\ A (S n) <> B (S n)) ->
  exists X, forall n, Bet (A n) X (B n).
*)

(** Nested A B describes the fact that the sequences A and B form the end points of nested non-degenerate segments *)

Definition Nested (A B:nat -> Tpoint -> Prop) :=
  (forall n, exists An, A n An) /\ (forall n, exists Bn, B n Bn) /\
  forall n An Am Bm Bn,
    A n An -> A (S n) Am -> B (S n) Bm -> B n Bn -> Bet An Am Bm /\ Bet Am Bm Bn /\ Am <> Bm.

Definition cantor_s_axiom := forall A B, Nested A B ->
  exists X, forall n An Bn, A n An -> B n Bn -> Bet An X Bn.

Definition dedekind_s_axiom := forall (Xi Upsilon : Tpoint -> Prop),
  (exists A, forall X Y, Xi X -> Upsilon Y -> Bet A X Y) ->
  (exists B, forall X Y, Xi X -> Upsilon Y -> Bet X B Y).

(** First-order formula *)

Inductive FOF : Prop -> Prop :=
| eq_fof : forall A B:Tpoint, FOF (A = B)
| bet_fof : forall A B C, FOF (Bet A B C)
| cong_fof : forall A B C D, FOF (Cong A B C D)
| not_fof : forall P, FOF P -> FOF (~ P)
| and_fof : forall P Q, FOF P -> FOF Q -> FOF (P /\ Q)
| or_fof : forall P Q, FOF P -> FOF Q -> FOF (P \/ Q)
| implies_fof : forall P Q, FOF P -> FOF Q -> FOF (P -> Q)
| forall_fof : forall P, (forall (A:Tpoint), FOF (P A)) -> FOF (forall A, P A)
| exists_fof : forall P, (forall (A:Tpoint), FOF (P A)) -> FOF (exists A, P A).

Definition first_order_dedekind := forall Xi Upsilon,
  (forall X, FOF (Xi X)) -> (forall Y, FOF (Upsilon Y)) ->
  (exists A, forall X Y, Xi X -> Upsilon Y -> Bet A X Y) ->
  (exists B, forall X Y, Xi X -> Upsilon Y -> Bet X B Y).

Definition archimedes_axiom := forall A B C D, A <> B -> Reach A B C D.

Definition aristotle_s_axiom := forall P Q A B C,
  ~ Col A B C -> Acute A B C ->
  exists X, exists Y, Out B A X /\ Out B C Y /\ Per B X Y /\ Lt P Q X Y.

Definition greenberg_s_axiom := forall P Q R A B C,
  ~ Col A B C ->
  Acute A B C -> Q <> R -> Per P Q R ->
  exists S, LtA P S Q A B C /\ Out Q S R.

End Continuity_Defs.