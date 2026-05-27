.. _chapter_onlypoints:

Only points
============

Predicates
__________


.. csv-table:: 
   :header: "ADGLib"# "LaTeX notation"# "Intuitive meaning"# "Definition"
   :widths: 20, 20, 60, 60
   :delim: #

    "between(A,B,C)"#""#"points :math:`A`, :math:`B` and :math:`C` are collinear and :math:`B` is strictly between :math:`A` and :math:`C`"#
    "betweenNonStrict(A,B,C)"#":math:`\betweenNonStrict{A}{B}{C}`"#"points :math:`A`, :math:`B` and :math:`C` are collinear and :math:`B` is between :math:`A` and :math:`C`, it can be the case the :math:`A=B` or :math:`B=C`."#""
    "centroid(H,A,B,C)"#""#":math:`H` is the centroid of triangle :math:`ABC`"#
    "circumcenter(G,A,B,C)"#""#":math:`G` is the circum-center of the points :math:`ABC`"#
    "collinear(A,B,C)"#":math:`\collinear{A}{B}{C}`"#"points :math:`A`, :math:`B` and :math:`C` are collinear"#":math:`\betweenNonStrict{A}{B}{C} \lor \betweenNonStrict{B}{A}{C} \lor \betweenNonStrict{A}{C}{B}`"
    "concyclic(A,B,C,D)"#""#":math:`A`, :math:`B`, :math:`C` and :math:`D` belong to the same circle (possibly degenerated)"#":math:`Coplanar A B C D \land \exists O\; \congruentSegments{O}{A}{O}{B} \land \congruentSegments{O}{A}{O}{C}  \land \congruentSegments{O}{A}{O}{D}`"
    "congruent(A,B,C,D)"#":math:`\congruentSegments{A}{B}{C}{D}`"#"the segments :math:`AB` and :math:`CD` are congruent (intuitively in the sense that they have same length, but length measure is not assumed to exist)"#
    "congruentAngles(A,B,C,D,E,F)}"#":math:`\congruentAngles{A}{B}{C}{D}{E}{F}`"#"the angles :math:`\angle{ABC}` and :math:`\angle{DEF}` are congruent"#":math:`A \neq B \land C \neq B \land D \neq E \land F \neq E \land \land \exists A', \exists C', \exists D', \exists F',  \betweenNonStrict{B}{A}{A'} \land \congruentSegments {A}{A'}{E}{D} \land \betweenNonStrict {B}{C}{C'} \land \congruentSegments{C}{C'}{E}{F} \land  \betweenNonStrict {E}{D}{D'} \land \congruentSegments{D}{D'}{B}{A} \land \betweenNonStrict {E}{F}{F'} \land \congruentSegments{F}{F'}{B}{C} \land  \congruentSegments{A'}{C'}{D'}{F'}`"
    "congruentCircles(O,P,O',P')"#""#"the two circles (or sphere) are congruent."#:math:`\congruentSegments{O}{P}{O'}{P'}`"
    "congruentTriangles(A,B,C,A',B',C')"#""#":math:`ABC` is congruent to :math:`A'B'C'`"#":math:`\congruentSegments{A}{B}{A'}{B'} \land \congruentSegments{A}{C}{A'}{C'} \land \congruentSegments{B}{C}{B'}{C'}`"
    "congruentRectangles(A,B,C,D,A',B',C',D')"#""#":math:`ABCD`  and :math:`A'B'C'D'` are congruent rectangles"#":math:`\congruentSegments{A}{B}{A'}{B'} \land \congruentSegments{B}{C}{B'}{C'} \land Rectangle(A,B,C,D) \land Rectangle(A',B',C',D')`"
    "diameter(A,B,O,P)"#""#":math:`AB` is a diameter of the circle of center :math:`O` going through :math:`P`"#
    "equilateral(A,B,C)"#""#":math:`ABC` is an equilateral triangle"#":math:`\congruentSegments{A}{B}{B}{C} \land \congruentSegments{B}{C}{C}{A}`"
    "equilateralNdg(A,B,C)"#""#":math:`ABC` is an equilateral triangle and the points are distinct and hence not collinear"#":math:`equilateral A B C \land A \neq B`"
    "harmonic(A,B,C,D)"#""#"Points :math:`A`, :math:`B`, :math:`C`, :math:`D` are on the same line and :math:`AC/CB=DA/DB`"#
    "incenterNdg(G,A,B,C)"#""#":math:`G` is the in-center of triangle :math:`ABC`"#
    "insideCircleStrict(C,O,P)"#""#":math:`C` is strictly inside or on circle (or sphere) of center :math:`O` going through :math:`P`"#
    "insideCircle(C,O,P)"#" "#":math:`C` is inside the circle (or sphere) of center :math:`O` going through :math:`P`"#
    "insideAngle(P,A,B,C)"#":math:`\insideAngle{P}{A}{B}{C}`"#"the point :math:`P` is inside the angle :math:`\angle{ABC}`"#":math:`A \neq B \land C \neq B \land P \neq B \land \exists X, \betweenNonStrict{A}{X}{C} \land (X = B \lor out{B}{X}{P})`"
    "intersectionLineLine(X,A,B,C,D)}"#""#":math:`X` is the intersection of lines :math:`AB` and :math:`CD`"#
    "intersectionLineSegment(X,A,B,C,D)"#""#":math:`X` is the intersection of line :math:`AB` and segment :math:`CD`"#
    "intersectionLineCircle(X,Y,A,B,O,P)"#""#":math:`X` and :math:`Y` are the intersections of line :math:`AB` and circle :math:`OP`"#
    "intersectionSegmentSegment(X,A,B,C,D)"#""#":math:`X` is the intersection of segments :math:`AB` and :math:`CD`"#
    "intersectionCircleCircle(X,Y,O,P,O',P')"#""#":math:`X` and :math:`Y` are the intersections of circles :math:`OP` and :math:`O'P'`."#
    "isosceles(A,B,C)"#""#":math:`ABC` is an isosceles triangle in :math:`B`, points may be equal."#":math:`\congruentSegments{A}{B}{B}{C}`"
    "isoscelesStrict(A,B,C)"#""#":math:`ABC` is an isosceles triangle in :math:`B`, points are not collinear."#":math:`\congruentSegments{A}{B}{B}{C} \land \lnot \collinear{A}{B}{C}`"
    "kite(A,B,C,D)"#""#":math:`ABCD` is a kite"#
    "lambert(A,B,C,D)"#""#":math:`ABCD` is a quadrilateral with three right angles. In hyperbolic geometry the fourth angle is acute, in Euclidean geometry it is a right angle."#":math:`A\neq B \land B \neq C \land C \neq D \land A \neq D \land \rightAngle{B}{A}{D} \land \rightAngle{A}{D}{C} \land \rightAngle{A}{B}{C}`"
    "midpoint(M,A,B)"#""#":math:`M` is the midpoint of segment :math:`AB`"#":math:`\betweenNonStrict{A}{M}{B} \land \congruentSegments{A}{M}{B}{M}`"
    "onAngleBisector(P,A,O,B)"#""#":math:`P` belongs to the bisector of angle :math:`AOB`"#" :math:`P \neq O \land \angle{AOP}` and :math:`\angle{POB}` are congruent"
    "onCircle(C,O,P)}"#""#":math:`C` is on circle (or sphere) of center :math:`O` going through :math:`P`"#
    "onLine(P,A,B)"#""#"points :math:`P` is on line :math:`AB` (:math:`A\neq B`)"#
    "onParallel(P,B,C,D)"#""#":math:`P` is on the parallel to line :math:`CD` through :math:`B`"#":math:`\parallelADG{A}{B}{C}{D} \land C \neq D`"
    "onPerpendicularBisector(P,A,B)"#""#":math:`P` belongs to the perpendicular bisector of segment :math:`AB`"#":math:`P \neq midpoint(A,B)` and :math:`\congruentSegments{P}{A}{P}{B}`"
    "onRay(O,A,B)"#":math:`out{O}{A}{B}`"#":math:`B` belongs to the half line :math:`OA`"#":math:`O \neq A \land O  \neq B \land (\betweenNonStrict{O}{A}{B} \lor \betweenNonStrict{O}{B}{A})`"
    "oppositeSides(A,B,P,Q)"#":math:`tS{A}{B}{P}{Q}`"# :math:`P` and :math:`Q` are on different sides of line :math:`AB` # :math:`\lnot \collinear{P}{A}{B} \land \lnot \collinear{Q}{A}{B} \land \exists T, \collinear{T}{A}{B} \land \betweenNonStrict{P}{T}{Q}`
    "outsideCircle(C,O,P)"#""#":math:`C` is on or outside the circle (or sphere) of center :math:`O` going through :math:`P`"
    "outsideCircleStrict(C,O,P)"#""#":math:`C` is strictly outside the circle (or sphere) of center :math:`O` going through :math:`P`"
    "meetLineLine(A,B,C,D)"#""#"The lines :math:`AB` and :math:`CD` intersect"
    "meetLineSegment(A,B,C,D)"#""#"The segment :math:`AB` and segment :math:`CD` intersect" 
    "orthocenter(H,A,B,C)"#""#":math:`H` is the ortho-center of triangle :math:`ABC`"#
    "perpendicular(A,B,C,D)"#":math:`\perpendicular{A}{B}{C}{D}`"#"line :math:`AB` is perpendicular to line :math:`CD` (:math:`A\neq B` and :math:`C\neq D`)"
    "perpendicularAt(P,A,B,C,D)"#":math:`\perpendicularAt{P}{A}{B}{C}{D}`"#"line :math:`AB` is perpendicular to line :math:`CD` at point :math:`P`"#":math:`\collinear{P}{A}{B} \land \collinear{P}{C}{D} \land (\forall U, V, \collinear{U}{A}{B} \Rightarrow \collinear{V}{C}{D} \Rightarrow \perpendicular{U}{P}{V})`"
    "perpendicular2(A,B,C,D,P)"#":math:`perpTwo{A}{B}{C}{D}{P}`"#"the line :math:`AB` and :math:`CD` have a common perpendicular through :math:`P` "#":math:`\exists X, \exists Y, \collinear{P}{X}{Y} \land \perpendicular{X}{Y}{A}{B} \land \perpendicular{X}{Y}{C}{D}`"
    "parallel(A,B,C,D)"#":math:`\parallelADG{A}{B}{C}{D}`"#"line :math:`AB` is parallel to line :math:`CD` "#" :math:`spara{A}{B}{C}{D} \lor (A \neq B \land C \neq D \land \collinear{A}{C}{D} \land \collinear{B}{C}{D})`"
    "parallelNonStrict(A,B,C,D)"#""#"line :math:`AB` is parallel to line :math:`CD` or :math:`A=B` or :math:`C=D` "#" :math:`\parallelADG{A}{B}{C}{D} \lor (A=B \lor C=D)`"
    "parallelNonReflexive(A,B,C,D)"#""#"line :math:`AB` is parallel to line :math:`CD` and :math:`AB \neq CD`"#" :math:`A \neq B \land C \neq D \land \coplanar{A}{B}{C}{D} \land \lnot \exists X, \collinear{X}{A}{B} \land \collinear{X}{C}{D}`"
    "verticalAngles(A,B,C,D,E,F)"#""#":math:`ABC` and :math:`DEF` are vertical angles"#":math:`B=E \land \betweenStrict{A}{B}{D} \land \betweenStrict{C}{B}{F}`"
    "parallelogram(A,B,C,D)"#""#":math:`ABCD` is a parallelogram, this includes a flat case defined as diagonals intersect in their midpoint" 
    "parallelogramNdg(A,B,C,D)"#""#":math:`ABCD` is a parallelogram. The points are not collinear"#
    "parallelogramFlat(A,B,C,D)"#""#":math:`ABCD` is a flat parallelogram. The four points are on the same line and the diagonals intersect in their midpoints"#":math:`\collinear{A}{B}{A'} \land \collinear{A}{B}{B'} \land \congruentSegments{A}{B}{A'}{B'} \land \congruentSegments{A}{B'}{A'}{B} \land (A \neq A' \lor B \neq B')`" 
    "perpendicularBisector(P,Q,A,B)"#""# :math:`PQ` is the perpendicular bisector of segment :math:`AB` #":math:`ReflectL\,A\,B\,P\,Q \land A \neq B`"
    "quadrilateral(A,B,C,D)"#""# 
    "quadrilateralNonCrossed(A,B,C,D)"#""# 
    "rectangle(A,B,C,D)"#""#":math:`ABCD` is a rectangle (all points are distinct)"#
    "reflectionStrict(P',P,A,B)"#""#":math:`P'` is the image of :math:`P` by reflection on line :math:`AB` "#" :math:`(\exists X\; \midpoint{X}{P}{P'} \land \collinear{A}{B}{X}) \land (\perpendicular{A}{B}{P}{P'} \lor P=P')`"
    "reflection(P',P,A,B)"#""#":math:`P'` is the image of :math:`P` by reflection on line :math:`AB` if :math:`A \neq B` and :math:`P'` is the image of :math:`P` by the reflection on point :math:`A` if :math:`A=B`"#" :math:`(A\neq B \land ReflectL\,P'\,P\,A\, B) \lor (A=B \land \midpoint{A}{P}{P'})`" 
    "rhombus(A,B,C,D)"#""#":math:`ABCD` is a rhombus"# 
    "rightAngle(A,B,C)"#":math:`\rightAngle{A}{B}{C}`"#"the triangle :math:`ABC` is a right triangle in :math:`B`"#" :math:`\exists C', \midpoint{C}{B}{C'} \land \congruentSegments{A}{C}{A}{C'}`"
    "saccheri(A,B,C,D)"#""#":math:`ABCD` is a quadrilateral with two equal sides perpendicular to the base. In Euclidean geometry it is a rectangle"#" :math:`\rightAngle{B}{A}{D} \land \rightAngle{A}{D}{C} \land \congruentSegments{A}{B}{C}{D} \land \sameSide{A}{D}{B}{C}`"
    "sameSide(A,B,X,Y)"#""#":math:`X` and :math:`Y` are on the same side of line :math:`AB`"#" :math:`\exists Z, \oppositeSides{A}{B}{X}{Z} \land \oppositeSides{A}{B}{Y}{Z}`"
    "similarTriangles(A,B,C,A',B',C')"#""#":math:`ABC` is similar to :math:`A'B'C'`"#" :math:`\congruentAngles{A}{B}{C}{A'}{B'}{C'} \land \congruentAngles{B}{C}{A}{B'}{C'}{A'} \land \congruentAngles{C}{A}{B}{C'}{A'}{B'}`"
    "square(A,B,C,D)"#""#":math:`ABCD` is a square (all points are distinct)"
    "symmetric(P',P,I)"#""#":math:`P'` is the symmetric of :math:`P` wrt :math:`I`" 
    "trapezoid(A,B,C,D)"#""#":math:`ABCD` is a trapezoid :math:`AB` is parallel to :math:`CD`"#
    "trapezoidRight(A,B,C,D)"#""#":math:`ABCD` is a trapezium with a right angle in :math:`A`" 
    "trapezoidIsosceles(A,B,C,D)"#""#" :math:`ABCD` is a trapezoid with congruent non-necessary parallel sides :math:`AB` is parallel to :math:`CD` and :math:`\congruentSegments{B}{C}{D}{A}`"
    "triangleNdg(A,B,C)"#""#":math:`A`, :math:`B`, :math:`C` are non-collinear"  
    "lessEqual(A,B,C,D)"#":math:`AB \leq CD`"#"the length :math:`AB` is smaller or equal to length :math:`CD`"#" :math:`\exists E, \betweenNonStrict{C}{Y}{D} \land \congruentSegments{A}{B}{C}{E}`" 
    "lessThan(A,B,C,D)"#":math:`AB < CD`"#"the length :math:`AB` is smaller to length :math:`CD`"#" :math:`AB \leq CD \land \lnot \congruentSegments{A}{B}{C}{D}`"
    "greaterEqual(A,B,C,D)"#":math:`AB \ge CD`"#"the length :math:`AB` is greater or equal to length :math:`CD`"#" :math:`CD \leq AB`"
    "greaterThan(A,B,C,D)"#":math:`AB > CD`"#"the length :math:`AB` is greater than length :math:`CD`"#" :math:`CD < AB`"
    "lessEqualAngles(A,B,C,D,E,F)"#":math:`\lea{A}{B}{C}{D}{E}{F}`"#"the angle :math:`\angle{ABC}` is smaller or equal than angle :math:`\angle{DEF}`"#" :math:`\exists P, \insideAngle{P}{D}{E}{F} \land \congruentAngles{A}{B}{C}{D}{E}{P}`"
    "lessThanAngles(A,B,C,D,E,F)"#":math:`\lta{A}{B}{C}{D}{E}{F}`"#"the angle :math:`\angle{ABC}` is smaller than angle :math:`\angle{DEF}`"#" :math:`\lea{A}{B}{C}{D}{E}{F} \land \lnot \congruentAngles{A}{B}{C}{D}{E}{F}`"
    "greaterThanAngles(A,B,C,D,E,F)"#":math:`\gta{A}{B}{C}{D}{E}{F}`"#"the angle :math:`\angle{ABC}` is greater than angle :math:`\angle{DEF}`"# 
    "greaterEqualAngles(A,B,C,D,E,F)"#":math:`\gea{A}{B}{C}{D}{E}{F}`"#"the angle :math:`\angle{ABC}` is greater than or equal to angle :math:`\angle{DEF}`"#
    "acute(A,B,C)"#""#":math:`\angle{ABC}` is an acute angle (strictly)"#":math:`\exists A', \exists B', \exists C', \rightAngle{A'}{B'}{C'} \land \lta{A}{B}{C}{A'}{B'}{C'}`"
    "obtuse(A,B,C)"#""#":math:`\angle{ABC}` is an obtuse angle (strictly)"#":math:`\exists A', \exists B', \exists C', \rightAngle{A'}{B'}{C'} \land \lta{A'}{B'}{C'}{A}{B}{C}`"
    "acuteTriangle(A,B,C)"#""#":math:`ABC` is a triangle with three acute angles."#
    "obtuseTriangle(A,B,C)"#""#":math:`ABC` is a triangle with one obtuse angle."#
    "supplementary(A,B,C,D,E,F)"#""#":math:`\angle{ABC}` and :math:`\angle{DEF}` are supplementary"#":math:`A \neq B \land \exists A', \betweenNonStrict{A}{B}{A'} \land \congruentAngles{D}{E}{F}{C}{B}{A'}`"
    "sumSegments(A,B,C,D,E,F)"#""#":math:`EF` is congruent to the sum of :math:`AB` and :math:`CD`"#
    "sumAngles(A,B,C,D,E,F,G,H,I)"#":math:`\sumAngles{A}{B}{C}{D}{E}{F}{G}{H}{I}`"#"The sum of angles :math:`\angle{ABC}` and :math:`\angle{DEF}` is congruent to :math:`\angle{GHI}`"#" :math:`\exists\,J\; \congruentAngles{C}{B}{J}{D}{E}{F} \land \lnot \sameSide{B}{C}{A}{J} \land \coplanar{A}{B}{C}{J} \land \congruentAngles{A}{B}{J}{G}{H}{I}`"
    "sumAnglesLessThanStraightAngle(A,B,C,D,E,F)"#""#"The sum of the angles :math:`\angle{ABC}` and :math:`\angle{DEF}` is smaller than the straight angle."#" :math:`A\neq B \land (Out E D F \lor \lnot \betweenNonStrict{A}{B}{C}) \land \exists\,J\; \congruentAngles{C}{B}{J}{D}{E}{F} \land \lnot \sameSide{B}{C}{A}{J} \land \lnot \oppositeSides{A}{B}{C}{J} \land \coplanar{A}{B}{C}{J}`"
    "sumAnglesTriangleCongruent(A,B,C,D,E,F)"#":math:`\sumAnglesTriangleCongruent{A}{B}{C}{D}{E}{F}`"#"The sum of the angles of the triangle :math:`ABC` is congruent to the angle :math:`\angle{D}{E}{F}`"
    "sumAnglesDefect(A,B,C,D,E,F)"#""#"The difference between the sum of angles of :math:`ABC` and a straight angle"
    "isoscelesRight(A,B,C)"#""#":math:`ABC` is a right and isosceles triangle in :math:`B`"#" :math:`\congruentSegments{A}{B}{B}{C} \land \rightAngle{A}{B}{C}`" 

Function symbols
________________

.. csv-table:: 
   :header: "ADGLib"# "LaTeX notation"# "Intuitive meaning"# "Definition"
   :widths: 20, 20, 60, 60
   :delim: #

    "funAnotherPoint(A,B)"#""#"a point on line :math:`AB` different from :math:`A` and :math:`B`"
    "funCentroid(A,B,C)"#""#"the centroid (gravity center) of triangle :math:`ABC`"
    "funCircumcenter(A,B,C)"#""#"the circumcenter of triangle :math:`ABC` "
    "funEquilateralFrom(A,B)"#""#"A point :math:`C` such that :math:`ABC` is an equilateral triangle"
    "funEquilateralFromOnSide(A,B,P)"#""#"A point :math:`C` such that :math:`ABC` is an equilateral triangle, and :math:`C` and :math:`P` are on the same side of line :math:`AB`"
    "funExtend(A,B)"#""#"a point on half-line :math:`AB` such that :math:`B` is between :math:`A` and the new point"
    "funExtendDistance(A,B,P,Q)"#""#"a point :math:`N` on half-line :math:`AB` such that :math:`B` is between :math:`A` and :math:`N` and :math:`BN` is congruent to :math:`PQ`. This corresponds to a compass"
    "funFoot(A,B,P)"#""#the foot of the perpendicular to :math:`AB` through :math:`P` "
    "funIncenter(A,B,C)"#""#the incenter of triangle :math:`ABC` "
    "funIntersectionLineLine(A,B,C,D)"#""#the intersection of lines AB and CD (assuming they do interesect ? )"
    "funIntersectionLineSegment(A,B,C,D)"#""#intersection of line :math:`AB` and segment :math:`CD`"
    "funIntersectionLineCircle(A,B,O,P)"#""#intersection of line :math:`AB` and circle of center :math:`O` going through :math:`P`. "
    "funIntersectionSegmentCircle(A,B,O,P)"#""#intersection of segment :math:`AB` and circle of center :math:`O` going through :math:`P`. "
    "funIntersectionSegmentSegment(A,B,C,D)"#""#intersection of segment :math:`AB` and segment :math:`CD`"
    "funIsoscelesFrom(A,B)"#""#A point :math:`C` such that :math:`ABC` is an isosceles triangle in :math:`C`"
    "funIsoscelesFromOnSide(A,B,P)"#""#"A point :math:`C` such that :math:`ABC` is an isosceles triangle in :math:`C` and :math:`C` is on the same side of line :math:`AB` as :math:`P`"
    "funMidpoint(A,B)"#""#the midpoint of segment :math:`AB`"
    "funOnLine(A,B)"#""#"a point on line :math:`AB`"
    "funOnRay(A,B)"#""#"a point on ray :math:`AB`"
    "funOnSegment(A,B)"#""#"a point segment :math:`AB`"
    "funOrthocenter(A,B,C)"#""#"the orthocenter of triangle :math:`ABC`"
    "funSymmetric(P,O)"#""#"the symmetric of :math:`P` wrt. :math:`O`"
    "funSymmetric(P,A,B)"#""#"the symmetric of :math:`P` wrt. line :math:`AB`"

Non deterministic Function
__________________________


.. csv-table:: 
   :header: "ADGLib"# "LaTeX notation"# "Intuitive meaning"# "Definition"
   :widths: 20, 20, 60, 60
   :delim: #

    "funAnotherPoint(A,B)"#""#"a point on line :math:`AB` different from :math:`A` and :math:`B`"
    "funCentroid(A,B,C)"#""#"the centroid (gravity center) of triangle :math:`ABC` "
    "funCircumcenter(A,B,C)"#""#"the circumcenter of triangle :math:`ABC` "
    "funEquilateralFrom(A,B)"#""#"A point :math:`C` such that :math:`ABC` is an equilateral triangle"
    "funEquilateralFromOnSide(A,B,P)"#""#"A point :math:`C` such that :math:`ABC` is an equilateral triangle, and :math:`C` and :math:`P` are on the same side of line :math:`AB`"
    "funExtend(A,B)"#""#"a point on half-line :math:`AB` such that :math:`B` is between :math:`A` and the new point"
    "funExtendDistance(A,B,P,Q)"#""#"a point :math:`N` on half-line :math:`AB` such that :math:`B` is between :math:`A` and :math:`N` and :math:`BN` is congruent to :math:`PQ`. This corresponds to a compass"
    "funFoot(A,B,P)"#""#"the foot of the perpendicular to :math:`AB` through :math:`P` "
    "funIncenter(A,B,C)"#""#"the incenter of triangle :math:`ABC` "
    "funIntersectionLineLine(A,B,C,D)"#""#"the intersection of lines AB and CD (assuming they do interesect ? ) \jn{undefined if they do not intersect ?}"
    "funIntersectionLineSegment(A,B,C,D)"#""#"intersection of line :math:`AB` and segment :math:`CD`"
    "funIntersectionLineCircle(A,B,O,P)"#""#"intersection of line :math:`AB` and circle of center :math:`O` going through :math:`P`. \jn{what to do when there are two intersections ?} "
    "funIntersectionSegmentCircle(A,B,O,P)"#""#"intersection of segment :math:`AB` and circle of center :math:`O` going through :math:`P`. \jn{what to do when there are two intersections ?} "
    "funIntersectionSegmentSegment(A,B,C,D)"#""#"intersection of segment :math:`AB` and segment :math:`CD`"
    "funIsoscelesFrom(A,B)"#""#"A point :math:`C` such that :math:`ABC` is an isosceles triangle in :math:`C`"
    "funIsoscelesFromOnSide(A,B,P)"#""#"A point :math:`C` such that :math:`ABC` is an isosceles triangle in :math:`C` and :math:`C` is on the same side of line :math:`AB` as :math:`P`"
    "funMidpoint(A,B)"#""#"the midpoint of segment :math:`AB` "
    "funOnLine(A,B)"#""#"a point on line :math:`AB`"
    "funOnRay(A,B)"#""#"a point on ray :math:`AB`"
    "funOnSegment(A,B)"#""#"a point segment :math:`AB`"
    "funOrthocenter(A,B,C)"#""#"the orthocenter of triangle :math:`ABC` "
    "funSymmetric(P,O)"#""#"the symmetric of :math:`P` wrt. :math:`O`"
    "funSymmetric(P,A,B)"#""#"the symmetric of :math:`P` wrt. line :math:`AB`"

Area method
___________

.. csv-table:: 
   :header: "ADGLib"# "LaTeX notation"# "Intuitive meaning"# "Definition"
   :widths: 20, 20, 60, 60
   :delim: #

    "signedAreaTriangle(A,B,C)"#":math:`\signedAreaTriangle{A}{B}{C}`"#"the signed area of triangle :math:`ABC`"
    "signedAreaQuadrilateral(A,B,C,D)"#":math:`\signedAreaQuadrilateral{A}{B}{C}{D}`"#"the sum of the signed areas the triangles :math:`ABC` and :math:`ACD`"
    "signedRatio(A,B,C,D)"#":math:`\signedRatio{A}{B}{C}{D}`"#"the ratio of the signed distance from :math:`A` to :math:`B` and from :math:`C` to :math:`D`. :math:`C` is different from :math:`D`"
    "pythagorasDifference(A,B,C)"#":math:`\pythagorasDifference{A}{B}{C}`"#":math:`AB^2 + BC^2 - AC^2`"
    "pythagorasDifferenceQuadrilateral(A,B,C,D)"#":math:`\pythagorasDifferenceQuadrilateral{A}{B}{C}{D}`"#"The pytharogas difference of :math:`ABD`` minus the pythagoras difference of :math:`CBD`"
    "onLineRatio(Y,A,B,r)"#""#":math:`Y`` is a point on the line :math:`AB` such that :math:`\signedDistance{A}{Y}=r\signedDistance{A}{B}`"
    "onParallelRatio(Y,W,U,V,r)"#""#":math:`Y` is a point on the parallel to line :math:`UV` going through :math:`W` such that :math:`\signedDistance{W}{Y}=r\signedDistance{U}{V}` "
    "onPerpenticularRatio(Y,W,U,V,r)"#""#":math:`Y` is a point on the perpendicular to line :math:`UV` going through :math:`W` such that :math:`4 \signedAreaTriangle{U}{V}{Y}=\pythagorasDifference{U}{V}{U}` "



