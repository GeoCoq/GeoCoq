Require Export GeoCoq.Tarski_dev.Annexes.circles.

Section Elementary_Continuity_Defs.

Context `{TE:Tarski_2D}.

(** In this file, we introduce elementary continuity properties. 
   These properties are different variant to assert that the intersection
   of line, segment and circles exists under some assumptions.
  Adding one of these properties as axiom to the Tarski_2D type class gives us
  a definition of ruler and compass geometry. 
  The links between these properties is in file elementary_continuity_props.v
*)


(** If there is a point P inside a circle, and Q outside then there is
    a point Z of the segment PQ which is on the circle. *)

Definition segment_circle :=
 forall A B P Q,
 InCircle P A B ->
 OutCircle Q A B ->
 exists Z, Bet P Z Q /\ OnCircle Z A B.

(** Given a line UV which contains a point inside the circle, there is
   a point of line UV which is on the circle. *)

Definition one_point_line_circle :=
 forall A B U V P,
 Col U V P -> U <> V -> Bet A P B ->
 exists Z, Col U V Z /\ OnCircle Z A B.

(** Given a line UV which contains a point P inside the circle, there are
  two points on line UV which belong to the circle and they are distinct if
 if P is strictly inside the circle. *)

Definition two_points_line_circle :=
 forall A B U V P,
 Col U V P -> U <> V -> Bet A P B ->
 exists Z1 Z2, Col U V Z1 /\ OnCircle Z1 A B /\ 
               Col U V Z2 /\ OnCircle Z2 A B /\
              Bet Z1 P Z2 /\ (P <> B -> Z1 <> Z2).

(** Given two circles (A,B) and (C,D), if there are two points of (C,D)
 one inside and one outside (A,B) then there is a point of intersection 
 of the two circles. *) 

Definition circle_circle:=
 forall A B C D P Q,
 OnCircle P C D ->
 OnCircle Q C D ->
 InCircle P A B ->
 OutCircle Q A B ->
 exists Z, OnCircle Z A B /\ OnCircle Z C D.

(** Given two circles (A,B) and (C,D), 
   if there is a point of (A,B) which is inside (C,D)
  and vice-versa, then there is a point of intersection of the two circles. *)

Definition circle_circle_bis:=
 forall A B C D P Q,
 OnCircle P C D ->
 InCircle P A B ->
 OnCircle Q A B ->
 InCircle Q C D ->
 exists Z, OnCircle Z A B /\ OnCircle Z C D.

(** Given two circles (A,B) and (C,D), if there are two points of (C,D)
 one inside and one outside (A,B) then there are two points of intersection 
 of the two circles.
 They are distinct if the inside and outside properties are strict. *) 

Definition circle_circle_two :=
 forall A B C D P Q,
 OnCircle P C D ->
 OnCircle Q C D ->
 InCircle P A B ->
 OutCircle Q A B ->
 exists Z1 Z2,
 OnCircle Z1 A B /\ OnCircle Z1 C D /\
 OnCircle Z2 A B /\ OnCircle Z2 C D /\
 (InCircleS P A B -> OutCircleS Q A B -> Z1<>Z2).

End Elementary_Continuity_Defs.




