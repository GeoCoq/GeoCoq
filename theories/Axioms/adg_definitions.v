Require Export GeoCoq.Axioms.tarski_axioms.

(**
   ADG-compatible predicate names.

   This file defines the ADG vocabulary directly from the primitive Tarski
   notions [Bet] and [Cong].  It intentionally does not import or alias
   GeoCoq.Axioms.Definitions.
*)

Section ADGDefinitions.

Context `{Tn:Tarski_neutral_dimensionless}.

(** Betweenness and incidence *)
(**Bet is a coq predicate for non strict betweeness**)
Definition betweenNonStrict A B C := Bet A B C.
(**verified**)

Definition between A B C :=
  betweenNonStrict A B C /\ A <> B /\ B <> C /\ A <> C.

(**verified**)
Definition collinear A B C :=
  betweenNonStrict A B C \/
  betweenNonStrict B A C \/
  betweenNonStrict A C B.

(**to be checked**)
Definition coplanar A B C D :=
  exists X, (collinear A B X /\ collinear C D X) \/
            (collinear A C X /\ collinear B D X) \/
            (collinear A D X /\ collinear B C X).
(*verified*)
Definition onLine P A B :=
  A <> B /\ collinear P A B.
(*verified*)
Definition onRay O A B :=
  O <> A /\ O <> B /\ (betweenNonStrict O A B \/ betweenNonStrict O B A).

(** Segment congruence and order *)

(**Is Cong a Rocq tactic?**)
Definition congruent A B C D := Cong A B C D.
(**mostly redundant**)
Definition congruentSegments A B C D := Cong A B C D.

Definition congruentCircles O P O' P' := congruentSegments O P O' P'.
(**verified**)
Definition congruentTriangles A B C A' B' C' :=
  congruentSegments A B A' B' /\
  congruentSegments A C A' C' /\
  congruentSegments B C B' C'.
(**verified**)
Definition lessEqual A B C D :=
  exists E, betweenNonStrict C E D /\ congruentSegments A B C E.
(**verified**)
Definition lessThan A B C D :=
  lessEqual A B C D /\ ~ congruentSegments A B C D.
(**verified**)
Definition greaterEqual A B C D := lessEqual C D A B.
(**verified**)
Definition greaterThan A B C D := lessThan C D A B.

(** Midpoints, right angles, perpendicularity, and sides *)
(**Verified**)
Definition midpoint M A B :=
  betweenNonStrict A M B /\ congruentSegments A M B M.

Definition rightAngle A B C :=
  exists C', midpoint B C C' /\ congruentSegments A C A C'.

Definition perpendicularAt P A B C D :=
  A <> B /\ C <> D /\ collinear P A B /\ collinear P C D /\
  forall U V, collinear U A B -> collinear V C D -> rightAngle U P V.

Definition perpendicular A B C D :=
  exists P, perpendicularAt P A B C D.

Definition perpendicular2 A B C D P :=
  exists X Y, collinear P X Y /\
              perpendicular X Y A B /\
              perpendicular X Y C D.

Definition oppositeSides A B P Q :=
  ~ collinear P A B /\ ~ collinear Q A B /\
  exists T, collinear T A B /\ betweenNonStrict P T Q.

Definition sameSide A B X Y :=
  exists Z, oppositeSides A B X Z /\ oppositeSides A B Y Z.

(** Reflections and perpendicular bisectors *)

Definition reflectionStrict P' P A B :=
  (exists X, midpoint X P P' /\ collinear A B X) /\
  (perpendicular A B P P' \/ P = P').

Definition reflection P' P A B :=
  (A <> B /\ reflectionStrict P' P A B) \/
  (A = B /\ midpoint A P P').

Definition symmetric P' P I := midpoint I P P'.

Definition perpendicularBisector P Q A B :=
  reflectionStrict A B P Q /\ A <> B.

Definition onPerpendicularBisector P A B :=
  (exists M, midpoint M A B /\ P <> M) /\ congruentSegments P A P B.

(** Angles *)

Definition congruentAngles A B C D E F :=
  A <> B /\ C <> B /\ D <> E /\ F <> E /\
  exists A', exists C', exists D', exists F',
  betweenNonStrict B A A' /\ congruentSegments A A' E D /\
  betweenNonStrict B C C' /\ congruentSegments C C' E F /\
  betweenNonStrict E D D' /\ congruentSegments D D' B A /\
  betweenNonStrict E F F' /\ congruentSegments F F' B C /\
  congruentSegments A' C' D' F'.

Definition insideAngle P A B C :=
  A <> B /\ C <> B /\ P <> B /\
  exists X, betweenNonStrict A X C /\ (X = B \/ onRay B X P).

Definition lessEqualAngles A B C D E F :=
  exists P, insideAngle P D E F /\ congruentAngles A B C D E P.

Definition lessThanAngles A B C D E F :=
  lessEqualAngles A B C D E F /\ ~ congruentAngles A B C D E F.

Definition greaterEqualAngles A B C D E F :=
  lessEqualAngles D E F A B C.

Definition greaterThanAngles A B C D E F :=
  lessThanAngles D E F A B C.

Definition acute A B C :=
  exists A' B' C',
  rightAngle A' B' C' /\ lessThanAngles A B C A' B' C'.

Definition obtuse A B C :=
  exists A' B' C',
  rightAngle A' B' C' /\ lessThanAngles A' B' C' A B C.

Definition supplementary A B C D E F :=
  A <> B /\ exists A',
  betweenNonStrict A B A' /\ congruentAngles D E F C B A'.

(** Parallelism *)

Definition parallelNonReflexive A B C D :=
  A <> B /\ C <> D /\ coplanar A B C D /\
  ~ exists X, collinear X A B /\ collinear X C D.

Definition parallel A B C D :=
  parallelNonReflexive A B C D \/
  (A <> B /\ C <> D /\ collinear A C D /\ collinear B C D).

Definition parallelNonStrict A B C D :=
  parallel A B C D \/ A = B \/ C = D.

Definition onParallel P B C D :=
  parallel P B C D /\ C <> D.

(** Circles *)

Definition onCircle C O P := congruentSegments O C O P.

Definition insideCircle C O P := lessEqual O C O P.

Definition outsideCircle C O P := lessEqual O P O C.

Definition insideCircleStrict C O P := lessThan O C O P.

Definition outsideCircleStrict C O P := lessThan O P O C.

Definition diameter A B O P :=
  betweenNonStrict A O B /\ onCircle A O P /\ onCircle B O P.

Definition concyclic A B C D :=
  coplanar A B C D /\
  exists O, congruentSegments O A O B /\
            congruentSegments O A O C /\
            congruentSegments O A O D.

(** Clarification needed: does ADG expect [X] and [Y] to be different here? *)
Definition intersectionCircleCircle X Y O P O' P' :=
  onCircle X O P /\ onCircle X O' P' /\
  onCircle Y O P /\ onCircle Y O' P'.

(** Intersections *)

Definition intersectionLineLine X A B C D :=
  onLine X A B /\ onLine X C D.

Definition intersectionLineSegment X A B C D :=
  onLine X A B /\ betweenNonStrict C X D.

Definition intersectionSegmentSegment X A B C D :=
  betweenNonStrict A X B /\ betweenNonStrict C X D.

Definition intersectionLineCircle X Y A B O P :=
  onLine X A B /\ onLine Y A B /\ onCircle X O P /\ onCircle Y O P.

Definition meetLineLine A B C D :=
  exists X, intersectionLineLine X A B C D.

Definition meetLineSegment A B C D :=
  exists X, intersectionSegmentSegment X A B C D.

(** Triangles and quadrilaterals *)

Definition triangleNdg A B C := ~ collinear A B C.

Definition equilateral A B C :=
  congruentSegments A B B C /\ congruentSegments B C C A.

Definition equilateralNdg A B C :=
  equilateral A B C /\ A <> B.

Definition isosceles A B C := congruentSegments A B B C.

Definition isoscelesStrict A B C :=
  congruentSegments A B B C /\ ~ collinear A B C.

Definition isoscelesRight A B C :=
  congruentSegments A B B C /\ rightAngle A B C.

Definition parallelogram A B C D :=
  (A <> C \/ B <> D) /\ exists M, midpoint M A C /\ midpoint M B D.

Definition parallelogramFlat A B C D :=
  collinear A B C /\ collinear A B D /\
  congruentSegments A B C D /\
  congruentSegments A D C B /\
  (A <> C \/ B <> D).

Definition parallelogramNdg A B C D :=
  parallelogram A B C D /\ ~ collinear A B C.

Definition rectangle A B C D :=
  A <> B /\ A <> C /\ A <> D /\
  B <> C /\ B <> D /\ C <> D /\
  parallelogram A B C D /\ congruentSegments A C B D.

Definition rhombus A B C D :=
  parallelogram A B C D /\ congruentSegments A B B C.

Definition square A B C D :=
  rectangle A B C D /\ congruentSegments A B B C.

Definition kite A B C D :=
  congruentSegments B C C D /\ congruentSegments D A A B.

Definition saccheri A B C D :=
  rightAngle B A D /\ rightAngle A D C /\
  congruentSegments A B C D /\ sameSide A D B C.

Definition lambert A B C D :=
  A <> B /\ B <> C /\ C <> D /\ A <> D /\
  rightAngle B A D /\ rightAngle A D C /\ rightAngle A B C.

Definition congruentRectangles A B C D A' B' C' D' :=
  congruentSegments A B A' B' /\
  congruentSegments B C B' C' /\
  rectangle A B C D /\ rectangle A' B' C' D'.

Definition similarTriangles A B C A' B' C' :=
  congruentAngles A B C A' B' C' /\
  congruentAngles B C A B' C' A' /\
  congruentAngles C A B C' A' B'.

Definition verticalAngles A B C D E F :=
  B = E /\ between A B D /\ between C B F.

Definition trapezoid A B C D := parallel A B C D.

Definition trapezoidIsosceles A B C D :=
  trapezoid A B C D /\ congruentSegments B C D A.

Definition acuteTriangle A B C :=
  triangleNdg A B C /\
  acute A B C /\ acute B C A /\ acute C A B.

Definition obtuseTriangle A B C :=
  triangleNdg A B C /\
  (obtuse A B C \/ obtuse B C A \/ obtuse C A B).

Definition onAngleBisector P A O B :=
  P <> O /\ congruentAngles A O P P O B.

(** Segment and angle sums *)

Definition sumSegments A B C D E F :=
  exists P Q R,
  betweenNonStrict P Q R /\
  congruentSegments P Q A B /\
  congruentSegments Q R C D /\
  congruentSegments P R E F.

Definition sumAngles A B C D E F G H I :=
  exists J,
  congruentAngles C B J D E F /\
  ~ sameSide B C A J /\
  coplanar A B C J /\
  congruentAngles A B J G H I.

Definition sumAnglesLessThanStraightAngle A B C D E F :=
  A <> B /\ (onRay E D F \/ ~ betweenNonStrict A B C) /\
  exists J,
  congruentAngles C B J D E F /\
  ~ sameSide B C A J /\
  ~ oppositeSides A B C J /\
  coplanar A B C J.

Definition sumAnglesTriangleCongruent A B C D E F :=
  exists G H I,
  sumAngles A B C B C A G H I /\
  sumAngles G H I C A B D E F.

Definition sumAnglesDefect A B C D E F :=
  exists G H I,
  sumAnglesTriangleCongruent A B C G H I /\
  supplementary G H I D E F.

(**
   The following ADG names are intentionally not defined here yet because the
   intended ADG meaning needs more domain-specific checking:

   centroid, harmonic, incenterNdg, orthocenter, quadrilateral,
   quadrilateralNonCrossed, trapezoidRight.
*)

End ADGDefinitions.
