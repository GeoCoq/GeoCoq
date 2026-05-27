# GeoCoq to ADG Core Predicate Mapping

This file starts with the basic mappings we are most confident about, then
adds broader ADGLib mappings with explicit confidence labels.

Status legend:

- `exact`: same intended meaning and same argument order.
- `equiv`: definition differs syntactically but should be equivalent by basic geometry lemmas.
- `close`: very likely mapping, but not definitionally identical.

## Primitive And Incidence Predicates

| GeoCoq name | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `Tpoint` | point type | `Point` / point type | point type | exact | In Lean this should probably be a type parameter or class field. |
| `Bet A B C` | endpoints `A C`, middle point `B` | `betweenNonStrict A B C` | endpoints `A C`, middle point `B` | exact | GeoCoq `Bet` is non-strict betweenness. |
| `BetS A B C` | endpoints `A C`, middle point `B` | `between A B C` | endpoints `A C`, middle point `B` | close | Strict betweenness. ADG version may include `A <> C` explicitly. |
| `Col A B C` | points `A B C` | `collinear A B C` | points `A B C` | equiv | GeoCoq and ADG use different disjunct order, but equivalent by betweenness symmetry. |
| `Coplanar A B C D` | points `A B C D` | `coplanar A B C D` | points `A B C D` | exact | Same intended coplanarity predicate. |
| `Out P A B` | origin `P`, ray point `A`, target point `B` | `onRay P A B` | origin `P`, ray point `A`, target point `B` | exact | Means `B` lies on ray `PA`. |

## Segment Congruence And Order

| GeoCoq name | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `Cong A B C D` | segment `AB`, segment `CD` | `congruentSegments A B C D` | segment `AB`, segment `CD` | exact | Segment congruence. |
| `Cong A B C D` | segment `AB`, segment `CD` | `congruent A B C D` | segment `AB`, segment `CD` | exact | ADG also uses `congruent` for segment congruence. |
| `Cong_3 A B C A' B' C'` | triangle `ABC`, triangle `A'B'C'` | `congruentTriangles A B C A' B' C'` | triangle `ABC`, triangle `A'B'C'` | exact | Three side congruences. |
| `Le A B C D` | segment `AB <= CD` | `lessEqual A B C D` | segment `AB <= CD` | exact | Segment order. |
| `Lt A B C D` | segment `AB < CD` | `lessThan A B C D` | segment `AB < CD` | exact | Strict segment order. |
| `Ge A B C D` | segment `AB >= CD` | `greaterEqual A B C D` | segment `AB >= CD` | exact | Reverse of `Le`. |
| `Gt A B C D` | segment `AB > CD` | `greaterThan A B C D` | segment `AB > CD` | exact | Reverse of `Lt`. |

## Midpoint, Perpendicularity, And Sides

| GeoCoq name | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `Midpoint M A B` | midpoint `M`, endpoints `A B` | `midpoint M A B` | midpoint `M`, endpoints `A B` | exact | Same argument order. |
| `Per A B C` | angle `ABC`, right angle at `B` | `rightAngle A B C` | angle `ABC`, right angle at `B` | exact | Vertex is the middle argument. |
| `Perp_at P A B C D` | point `P`, line `AB`, line `CD` | `perpendicularAt P A B C D` | point `P`, line `AB`, line `CD` | exact | Same argument order. |
| `Perp A B C D` | line `AB`, line `CD` | `perpendicular A B C D` | line `AB`, line `CD` | exact | Perpendicularity of two lines. |
| `Perp2 A B C D P` | line `AB`, line `CD`, through point `P` | `perpendicular2 A B C D P` | line `AB`, line `CD`, through point `P` | exact | Common perpendicular through `P`. |
| `TS A B P Q` | line `AB`, points `P Q` | `oppositeSides A B P Q` | line `AB`, points `P Q` | exact | Points on opposite sides of a line. |
| `OS A B P Q` | line `AB`, points `P Q` | `sameSide A B P Q` | line `AB`, points `P Q` | exact | Points on same side of a line. |

## Angles

| GeoCoq name | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `CongA A B C D E F` | angle `ABC`, angle `DEF` | `congruentAngles A B C D E F` | angle `ABC`, angle `DEF` | exact | Vertices are `B` and `E`. |
| `InAngle P A B C` | point `P`, angle `ABC` | `insideAngle P A B C` | point `P`, angle `ABC` | exact | Same argument order. |
| `LeA A B C D E F` | angle `ABC <= DEF` | `lessEqualAngles A B C D E F` | angle `ABC <= DEF` | exact | Angle order. |
| `LtA A B C D E F` | angle `ABC < DEF` | `lessThanAngles A B C D E F` | angle `ABC < DEF` | exact | Strict angle order. |
| `GeA A B C D E F` | angle `ABC >= DEF` | `greaterEqualAngles A B C D E F` | angle `ABC >= DEF` | exact | Reverse of `LeA`. |
| `GtA A B C D E F` | angle `ABC > DEF` | `greaterThanAngles A B C D E F` | angle `ABC > DEF` | exact | Reverse of `LtA`. |
| `Acute A B C` | angle `ABC` | `acute A B C` | angle `ABC` | exact | Same argument order. |
| `Obtuse A B C` | angle `ABC` | `obtuse A B C` | angle `ABC` | exact | Same argument order. |
| `SuppA A B C D E F` | angle `ABC`, angle `DEF` | `supplementary A B C D E F` | angle `ABC`, angle `DEF` | exact | Supplementary angles. |

## Parallelism

| GeoCoq name | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `Par_strict A B C D` | line `AB`, line `CD` | `parallelNonReflexive A B C D` | line `AB`, line `CD` | exact | Proper non-intersecting coplanar lines. |
| `Par A B C D` | line `AB`, line `CD` | `parallel A B C D` | line `AB`, line `CD` | exact | Includes strict parallel and same-line proper case. |

## Circles

| GeoCoq name | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `OnCircle P O R` | point `P`, center `O`, radius point `R` | `onCircle P O R` | point `P`, center `O`, radius point `R` | exact | Same argument order. |
| `InCircle P O R` | point `P`, center `O`, radius point `R` | `insideCircle P O R` | point `P`, center `O`, radius point `R` | exact | Inside or on circle. |
| `OutCircle P O R` | point `P`, center `O`, radius point `R` | `outsideCircle P O R` | point `P`, center `O`, radius point `R` | exact | Outside or on circle. |
| `InCircleS P O R` | point `P`, center `O`, radius point `R` | `insideCircleStrict P O R` | point `P`, center `O`, radius point `R` | exact | Strictly inside by name. |
| `OutCircleS P O R` | point `P`, center `O`, radius point `R` | `outsideCircleStrict P O R` | point `P`, center `O`, radius point `R` | exact | Strictly outside. |
| `Diam A B O P` | diameter endpoints `A B`, center `O`, radius point `P` | `diameter A B O P` | diameter endpoints `A B`, center `O`, radius point `P` | exact | Same argument order. |

## Sums

| GeoCoq name | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `SumS A B C D E F` | `AB + CD = EF` | `sumSegments A B C D E F` | `AB + CD = EF` | exact | Segment sum. |
| `SumA A B C D E F G H I` | angle `ABC + DEF = GHI` | `sumAngles A B C D E F G H I` | angle `ABC + DEF = GHI` | exact | Angle sum. |
| `SAMS A B C D E F` | angle `ABC + DEF` less than straight angle | `sumAnglesLessThanStraightAngle A B C D E F` | angle `ABC + DEF` less than straight angle | exact | Same argument order. |
| `TriSumA A B C D E F` | triangle `ABC` angle sum congruent to angle `DEF` | `sumAnglesTriangleCongruent A B C D E F` | triangle `ABC` angle sum congruent to angle `DEF` | exact | Same argument order. |
| `Defect A B C D E F` | defect of triangle `ABC` as angle `DEF` | `sumAnglesDefect A B C D E F` | defect of triangle `ABC` as angle `DEF` | exact | Same argument order. |

## Requested Additional Mappings

These are useful mappings for the predicates you asked about. Some are marked
`close` because the name maps well, but GeoCoq's historical definition may have
extra or weaker nondegeneracy assumptions than ADG's table wording.

| GeoCoq name | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `is_gravity_center G A B C` | center `G`, triangle `ABC` | `centroid G A B C` | center `G`, triangle `ABC` | close | GeoCoq's highschool name is gravity center; ADG calls this centroid. GeoCoq includes `~ Col A B C`. |
| `is_circumcenter G A B C` | center `G`, triangle/points `ABC` | `circumcenter G A B C` | center `G`, triangle/points `ABC` | close | Same intended object. GeoCoq definition uses equal distances from `G` and coplanarity. |
| `Concyclic A B C D` | points `A B C D` | `concyclic A B C D` | points `A B C D` | exact | In `Main/Highschool/concyclic.v`, the formula matches the ADG table: coplanar plus one center equidistant from all four points. |
| `equilateral A B C` | triangle `ABC` | `equilateral A B C` | triangle `ABC` | exact | Defined as `AB = BC` and `BC = CA`. |
| `isosceles A B C` | triangle `ABC`, apex/vertex at `B` | `isosceles A B C` | triangle `ABC`, apex/vertex at `B` | exact | Means `AB = BC`; the middle point `B` is the special vertex. |
| `Kite A B C D` | quadrilateral `ABCD` | `kite A B C D` | quadrilateral `ABCD` | exact | GeoCoq definition is `BC = CD` and `DA = AB`, matching the ADG kite shape. |
| `Rectangle A B C D` | quadrilateral `ABCD` | `rectangle A B C D` | quadrilateral `ABCD` | close | GeoCoq `Rectangle` is parallelogram plus equal diagonals. ADG wording says all points are distinct, so add distinctness if ADG-exactness is required. |
| `Square A B C D` | quadrilateral `ABCD` | `square A B C D` | quadrilateral `ABCD` | close | GeoCoq `Square` is rectangle plus equal adjacent sides. ADG wording says all points are distinct, so add distinctness if ADG-exactness is required. |
| `ReflectL P' P A B` | image `P'`, source `P`, mirror line `AB` | `reflectionStrict P' P A B` | image `P'`, source `P`, mirror line `AB` | exact | Reflection in line `AB`; requires the line case. |
| `Reflect P' P A B` | image `P'`, source `P`, mirror data `A B` | `reflection P' P A B` | image `P'`, source `P`, mirror data `A B` | exact | GeoCoq already handles the ADG split: line reflection if `A <> B`, point symmetry if `A = B`. |
| `CongA_3 A B C A' B' C'` | triangle `ABC`, triangle `A'B'C'` | `similarTriangles A B C A' B' C'` | triangle `ABC`, triangle `A'B'C'` | exact | GeoCoq defines this using the same three corresponding angle congruences. |
| `Par A B C D` | line `AB`, line `CD` | `trapezoid A B C D` | quadrilateral `ABCD`, with `AB` parallel to `CD` | close | ADG table says trapezoid means `AB` parallel to `CD`. This is a good name mapping, but it does not assert quadrilateral distinctness. |
| `is_orthocenter H A B C` | point `H`, triangle `ABC` | `orthocenter H A B C` | point `H`, triangle `ABC` | close | Same intended object. GeoCoq includes `~ Col A B C` and three perpendicular altitude conditions. |

## Remaining ADGLib Predicate Mappings

These entries cover the remaining important ADGLib names. Some GeoCoq entries
are expressions instead of old predicate names because GeoCoq does not always
provide one exact historical predicate for the ADG concept.

### Triangle Centers And Special Constructions

| GeoCoq name or expression | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `is_incenter I A B C` | incenter `I`, triangle `ABC` | `incenterNdg I A B C` | incenter `I`, triangle `ABC` | close | GeoCoq includes `~ Col A B C` and three angle-bisector angle congruences. Good for the nondegenerate ADG incenter. |
| `CongA A O P P O B /\ P <> O` | point `P`, angle `AOB` | `onAngleBisector P A O B` | point `P`, angle `AOB` | close | GeoCoq has lemmas around angle bisectors, but this is the direct ADG-shaped expression. |
| `Is_on_perp_bisect P A B` | point `P`, segment `AB` | `onPerpendicularBisector P A B` | point `P`, segment `AB` | close | GeoCoq's old `Is_on_perp_bisect` is just equal distances. ADG wording may additionally exclude the midpoint. |
| `Perp_bisect P Q A B` | line `PQ`, segment `AB` | `perpendicularBisector P Q A B` | line `PQ`, segment `AB` | exact | Same argument order: `PQ` is the perpendicular bisector of `AB`. |

### Intersection Predicates

| GeoCoq name or expression | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `Inter A B C D X` | line `AB`, line `CD`, intersection `X` | `intersectionLineLine X A B C D` | intersection `X`, line `AB`, line `CD` | close | GeoCoq `Inter` is stronger: it requires `CD` nondegenerate and a point on `CD` not on `AB`. |
| `Col A B X /\ Bet C X D` | line `AB`, segment `CD`, point `X` | `intersectionLineSegment X A B C D` | intersection `X`, line `AB`, segment `CD` | exact | This is the direct ADG-shaped expression. Add `A <> B` if using ADG `onLine`. |
| `Col A B X /\ Col A B Y /\ OnCircle X O P /\ OnCircle Y O P` | line `AB`, circle center/radius `O P`, points `X Y` | `intersectionLineCircle X Y A B O P` | points `X Y`, line `AB`, circle `OP` | close | Does not force `X <> Y`; add distinctness if the theorem expects two different intersections. |
| `Bet A X B /\ Bet C X D` | segment `AB`, segment `CD`, point `X` | `intersectionSegmentSegment X A B C D` | intersection `X`, segment `AB`, segment `CD` | exact | Uses non-strict betweenness, so endpoints count. |
| `InterCCAt O P O' P' X Y` | circle `OP`, circle `O'P'`, points `X Y` | `intersectionCircleCircle X Y O P O' P'` | points `X Y`, circle `OP`, circle `O'P'` | close | GeoCoq `InterCCAt` is stronger: it requires two distinct intersections and non-identical circles. |
| `exists X, Inter A B C D X` | line `AB`, line `CD` | `meetLineLine A B C D` | line `AB`, line `CD` | close | GeoCoq version inherits the stronger `Inter` side conditions. |
| `exists X, Bet A X B /\ Bet C X D` | segment `AB`, segment `CD` | `meetLineSegment A B C D` | segment `AB`, segment `CD` | exact | ADG table says the two segments intersect. |

### Quadrilateral Families

| GeoCoq name or expression | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `Plg A B C D` | quadrilateral `ABCD` | `parallelogram A B C D` | quadrilateral `ABCD` | exact | GeoCoq `Plg` is the midpoint-of-diagonals characterization, matching the ADG note about flat cases. |
| `Plg A B C D /\ ~ Col A B C` | quadrilateral `ABCD` | `parallelogramNdg A B C D` | quadrilateral `ABCD` | close | Good ADG-shaped nondegenerate parallelogram; verify if ADG wants a stronger nondegeneracy convention. |
| `Parallelogram_flat A B C D` | quadrilateral `ABCD` | `parallelogramFlat A B C D` | quadrilateral `ABCD` | exact | GeoCoq already has the flat parallelogram predicate. |
| no stable core GeoCoq predicate | quadrilateral `ABCD` | `quadrilateral A B C D` | quadrilateral `ABCD` | needs definition | Define from ADG requirements before mapping. Do not guess this one silently. |
| no stable core GeoCoq predicate | quadrilateral `ABCD` | `quadrilateralNonCrossed A B C D` | quadrilateral `ABCD` | needs definition | Needs the exact ADG convention for non-crossing sides. |
| `Rhombus A B C D` | quadrilateral `ABCD` | `rhombus A B C D` | quadrilateral `ABCD` | exact | GeoCoq: parallelogram plus adjacent side congruence. |
| `Saccheri A B C D` | quadrilateral `ABCD` | `saccheri A B C D` | quadrilateral `ABCD` | exact | Same right-angle, equal-side, same-side definition as ADG. |
| `Lambert A B C D` | quadrilateral `ABCD` | `lambert A B C D` | quadrilateral `ABCD` | exact | GeoCoq also includes coplanarity; ADG table gives the same intended quadrilateral. |
| `Par A B C D` | line `AB`, line `CD` | `trapezoid A B C D` | quadrilateral `ABCD`, with `AB` parallel to `CD` | close | Already listed above. No quadrilateral distinctness is included by this mapping. |
| `Par A B C D /\ Per D A B` | quadrilateral `ABCD`, right angle at `A` | `trapezoidRight A B C D` | quadrilateral `ABCD`, right angle at `A` | tentative | ADG says trapezoid with a right angle in `A`; confirm whether the intended angle is `DAB` or `BAD`. |
| `Par A B C D /\ Cong B C D A` | quadrilateral `ABCD` | `trapezoidIsosceles A B C D` | quadrilateral `ABCD` | exact | Matches ADG wording: `AB` parallel to `CD` and non-parallel sides `BC` and `DA` congruent. |

### Reflection And Symmetry

| GeoCoq name or expression | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `Midpoint I P P'` | center `I`, points `P P'` | `symmetric P' P I` | image `P'`, source `P`, center `I` | exact | ADG argument order puts the symmetry center last. |

### Triangle-Type Predicates

| GeoCoq name or expression | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `equilateral_strict A B C` | triangle `ABC` | `equilateralNdg A B C` | triangle `ABC` | close | GeoCoq highschool name exists and is equivalent to `equilateral A B C /\ A <> B`. ADG says non-collinear; this usually follows but may require a lemma. |
| `isosceles A B C /\ ~ Col A B C` | triangle `ABC`, apex/vertex at `B` | `isoscelesStrict A B C` | triangle `ABC`, apex/vertex at `B` | exact | ADG strict isosceles means equal sides plus non-collinearity. |
| `Acute A B C /\ Acute B C A /\ Acute C A B /\ ~ Col A B C` | triangle `ABC` | `acuteTriangle A B C` | triangle `ABC` | exact | Direct ADG-shaped expression. |
| `(Obtuse A B C \/ Obtuse B C A \/ Obtuse C A B) /\ ~ Col A B C` | triangle `ABC` | `obtuseTriangle A B C` | triangle `ABC` | exact | Direct ADG-shaped expression. |
| `isosceles A B C /\ Per A B C` | triangle `ABC`, right angle at `B` | `isoscelesRight A B C` | triangle `ABC`, right angle at `B` | exact | Equal sides `AB = BC` and right angle at `B`. |
| `~ Col A B C` | points `A B C` | `triangleNdg A B C` | points `A B C` | exact | Nondegenerate triangle condition. |

### Circle And Line Auxiliary Predicates

| GeoCoq name or expression | GeoCoq argument order | ADG name | ADG argument order | Status | Notes |
|---|---|---|---|---|---|
| `A <> B /\ Col P A B` | point `P`, line `AB` | `onLine P A B` | point `P`, line `AB` | exact | ADG `onLine` explicitly requires the line to be nondegenerate. |
| `exists Q, Par B Q C D /\ Col P B Q` | point `P`, through point `B`, line `CD` | `onParallel P B C D` | point `P`, through point `B`, line `CD` | close | Safer than `Par P B C D`: it allows `P = B` while still using a genuine parallel line through `B`. |

## Deliberately Omitted From This Core Mapping

The following names are useful, but they are not included in this "most sure" mapping because they are ambiguous, higher-level, or require more checking:

```text
verticalAngles
harmonic
```

## Argument-Order Warnings

| Predicate | Warning |
|---|---|
| `Bet A B C` / `betweenNonStrict A B C` | `B` is the middle point. |
| `Out P A B` / `onRay P A B` | First argument is the ray origin. It means `B` lies on ray `PA`. |
| `Per A B C` / `rightAngle A B C` | The right angle is at the middle point `B`. |
| `CongA A B C D E F` / `congruentAngles A B C D E F` | Angles are `ABC` and `DEF`; vertices are `B` and `E`. |
| `Le A B C D` / `lessEqual A B C D` | Means segment `AB <= CD`, not point order. |
| `Perp_at P A B C D` / `perpendicularAt P A B C D` | First argument is the intersection/perpendicular point. |
| `OnCircle P O R` / `onCircle P O R` | Order is point-on-circle, center, radius point. |
| `Diam A B O P` / `diameter A B O P` | `A B` are diameter endpoints, `O` is center, `P` is radius point. |
