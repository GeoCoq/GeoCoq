(* The code below defines a class of geometric axioms inspired by Gelertner's paper 
 REALIZATION OF A GEOMETRY THEOREM PROVING MACHINE. 
   It includes properties and relations for points, lines, angles, and triangles, 
   along with axioms for congruence and parallelism. The class is checked for correctness. *)

Class Gelertner_inspired_neutral_2D := {
 Gpoint : Type;
 cong : Gpoint -> Gpoint -> Gpoint -> Gpoint -> Prop;
 collinear : Gpoint -> Gpoint -> Gpoint -> Prop;
 between_strict : Gpoint -> Gpoint -> Gpoint -> Prop;
 congruent_angles : Gpoint -> Gpoint -> Gpoint -> Gpoint -> Gpoint -> Gpoint -> Prop;
 right_angle : Gpoint -> Gpoint -> Gpoint -> Prop;
 perpendicular : Gpoint -> Gpoint -> Gpoint -> Gpoint -> Prop;
 opposite_sides : Gpoint -> Gpoint -> Gpoint -> Gpoint -> Prop;
 same_side : Gpoint -> Gpoint -> Gpoint -> Gpoint -> Prop;
 parallel : Gpoint -> Gpoint -> Gpoint -> Gpoint -> Prop;
 parallelogram : Gpoint -> Gpoint -> Gpoint -> Gpoint -> Prop; 
 midpoint : Gpoint -> Gpoint -> Gpoint -> Prop;
 congruent_triangles : Gpoint -> Gpoint -> Gpoint -> Gpoint -> Gpoint -> Gpoint -> Prop;

 (* Collinearity permutation. *)
 ax_col1 : forall A B C, collinear A B C -> collinear A C B;
 (* Collinearity circular permutation. *)
 ax_col2 : forall A B C, collinear A B C -> collinear B C A;
 (* Non collinearity permutation. *)
 ax_col3 : forall A B C, ~collinear A B C -> ~collinear A C B;
  (* Non collinearity circular permutation. *)
 ax_col4 : forall A B C, ~collinear A B C -> ~collinear B C A;
  (* Non collinearity implies distinct points. *)
 ax_col5 : forall A B C, ~collinear A B C -> A <> B;
 ax_col6 : forall A B C D, ~collinear A B C -> collinear A B D -> A <> D -> ~collinear A D C;
 ax_col7 : forall A B C D, ~collinear A B C -> between_strict C D B -> ~collinear A B D;
  (* Betweenness implies collinearity. *)
 ax_bet1 : forall A B C, between_strict A B C -> collinear A B C;
  (*  Betweenness is strict. *)
 ax_bet_distinct_1: forall A B C, between_strict A B C -> A <> B;
 ax_bet_distinct_2: forall A B C, between_strict A B C -> B <> C;
 ax_bet_distinct_3: forall A B C, between_strict A B C -> A <> C;
  (* Betweenness is transitive. *)
  (* Betweenness is symetric.*)
 ax_bet2 : forall A B C, between_strict A B C -> between_strict C B A;
  (* Pseudo transitivity properties of betweenness. *)
 ax_bet3 : forall A B C D, between_strict A B C -> between_strict B C D -> between_strict A B D;
 ax_bet4 : forall A B C D, between_strict A B C -> between_strict B C D -> between_strict A C D;
  (* Definition of opposite sides. *)
 ax_sides1 : forall A B C X, between_strict A X B -> ~ collinear A X C -> ~ collinear B X C -> opposite_sides X C A B;
 ax_sides2 : forall A B C D X, between_strict A X B -> collinear C X D -> ~ collinear A C D -> ~ collinear B C D -> opposite_sides C D A B;
 (* Straight angles are congruent. *)
 ax_sides5 : forall A B C D X, between_strict A X B -> between_strict C X D -> congruent_angles A X C B X D;
 (* Same side symetries. *)
 ax_sides6 : forall A B C D, same_side B C D A -> same_side B C A D;
 ax_sides7 : forall A B C D, same_side B C D A -> same_side C B A D;
 (* Opposite sides symetries. *)
 ax_sides9 : forall A B C D, opposite_sides A C B D -> opposite_sides C A B D;
 ax_sides10 : forall A B C D, opposite_sides A C B D -> opposite_sides A C D B;

(* Perpendicularity is only between proper lines. *)
 ax_perp_distinct1 : forall X Y Z U, perpendicular X Y Z U -> X <> Y;
 ax_perp_distinct2 : forall X Y Z U, perpendicular X Y Z U -> Z <> U;

(* Segment are symetric in perpendicular. *)
 ax_perp3 : forall X Y Z U, perpendicular X Y Z U -> perpendicular Y X Z U;
 (* Perpendicularity is a symetric relation. *)
 ax_perp4 : forall X Y Z U, perpendicular X Y Z U -> perpendicular Z U X Y;
 ax_perp_right_angle : forall X Y Z, perpendicular X Y Y Z -> right_angle X Y Z;
 ax_right_angle_perp : forall X Y Z, X<>Y -> Y<>Z -> right_angle X Y Z -> perpendicular X Y Y Z;
 ax_perp6 : forall X Y Z U, perpendicular X Y Z U -> collinear Y Z U -> right_angle X Y Z;
 (* This axioms forces the space to be planar. 
 ax_perp_perp_par : forall A B C D E F, perpendicular A B C D -> perpendicular E F C D -> parallel A B E F; *)
 (* Segment are symetric in parallelism. *)
 ax_para1 : forall X Y Z U, parallel X Y Z U -> parallel Y X Z U;
 (* Parallelism is a symetric relation. *)
 ax_para2 : forall X Y Z U, parallel X Y Z U -> parallel Z U X Y;
 (* Same line preserve parallelism. *)
 ax_par_col : forall A B C D B', A<>B' -> parallel A B C D -> collinear A B B' -> parallel A B' C D;
(* Equal lines are parallel. *)
 ax_angle1 : forall A B C, collinear A B C -> A <> B -> A <> C -> parallel A B A C;
 ax_angle2 : forall A B C, collinear A B C -> A <> B -> B <> C -> parallel A B B C;
 (* Segment congruence is reflexive. *)
 ax_cong1 : forall X Y, cong X Y X Y;
 (* Segment congruence is symetric. *)
 ax_cong2 : forall X Y Z U, cong X Y Z U -> cong Z U X Y;
 (* Segments are symetric. *)
 ax_cong3 : forall X Y Z U, cong X Y Z U -> cong Y X Z U;
 (* Angle congruence is reflexive. *)
 ax_congruent_angle_refl : forall A B C, A<>B -> B<>C -> congruent_angles A B C A B C;
 (* Angle congruence is symetric. *)
 ax_congruent_angle_sym : forall A B C D E F, congruent_angles A B C D E F -> congruent_angles D E F A B C;
 (* Angles are symetric. *)
 ax_congruent_angle_syma : forall A B C D E F, congruent_angles A B C D E F -> congruent_angles C B A D E F;
 (* Angle change of half-line *)
 ax_congruent_angle_same_half_line : forall A B C D, between_strict A B C -> C<>D -> congruent_angles A C D B C D;
 (* The supplementary of a right angle is a right angle. *)
 ax_supp_right_right : forall A B C D, between_strict A B C -> right_angle D B C -> right_angle D B A;
 (* An angle congruent to a right angle is a right angle. *)
 ax_congruent_right_right : forall A B C X Y Z, right_angle A B C -> congruent_angles A B C X Y Z -> right_angle X Y Z;
 (* Right angles are congruent. *)
 ax_right_angles_congruent : forall A B C X Y Z, right_angle A B C -> right_angle X Y Z -> A<>B -> B<>C -> X<>Y -> Y<>Z -> congruent_angles A B C X Y Z; (* NDG added*)
 (* Angle congruence is transitive. *)
 ax_congruent_angle_trans: forall A B C D E F G H I, congruent_angles A B C D E F -> congruent_angles D E F G H I -> congruent_angles A B C G H I;
 (* Right angle symmetry. *)
 ax_right_angle_sym : forall A B C, right_angle A B C -> right_angle C B A;
 (* The midpoint is equidistant from extremities. *)
 ax_midpoint1 : forall A B M, midpoint M A B -> cong A M M B;
 (* The midpoint is strictly between the extremitites of the segment. *)
 ax_midpoint2 : forall A B M, midpoint M A B -> A<>B -> between_strict A M B; (* add ndg or define midpoint as strict ? *)
 (* Definition of midpoint. *)
 ax_midpoint3 : forall A B M, between_strict A M B -> cong A M M B -> midpoint M A B;
 (* Segments in midpoint are symetric. *)
 ax_midpoint4 : forall A B C, midpoint C A B -> midpoint C B A;
 (* Congruence of triangles is a reflexive relation. *)
 ax_triangle1 : forall A B C, ~collinear A B C -> congruent_triangles A B C A B C;
  (* Congruence of triangles is a symetric relation. *)
 ax_triangle2 : forall A B C D E F, congruent_triangles A B C D E F -> congruent_triangles D E F A B C;
  (* Congruence of triangles is a transitive relation. *)
 ax_triangle3 : forall A B C D E F X Y Z, congruent_triangles A B C D E F -> congruent_triangles D E F X Y Z -> congruent_triangles A B C X Y Z;
  (* Side-angle-side *)
 ax_sas : forall A B C D E F, ~collinear A B C -> cong A B D E -> congruent_angles A B C D E F -> cong B C E F -> congruent_triangles A B C D E F;
  (* Side-side-side *)
 ax_sss : forall A B C D E F, ~collinear A B C -> cong A B D E -> cong B C E F -> cong F D C A -> congruent_triangles A B C D E F;
  (* Angle-side-angle *)
 ax_asa : forall A B C D E F, ~collinear A B C -> congruent_angles C A B F D E -> cong A B D E -> congruent_angles A B C D E F -> congruent_triangles A B C D E F;
  (* Side-angle-angle *)
 ax_saa : forall A B C D E F, ~collinear A B C -> congruent_angles B C A E F D -> congruent_angles A B C D E F -> cong A B D E -> congruent_triangles A B C D E F;
  (* Congruent triangles provide segment congruence. *)
 ax_tc : forall A B C D E F, congruent_triangles A B C D E F -> cong A B D E;
  (* Congruent triangles circular permutation. *)
 ax_tt : forall X Y Z U V W, congruent_triangles X Y Z U V W -> congruent_triangles Z X Y W U V
}.

(* We seperate the axioms that needs euclidean geometry. *)

Class Gelertner_inspired_euclidean `(G : Gelertner_inspired_neutral_2D) := {
  (* Definition of parallelogram. *)
  ax_parallelogram1 : forall A B C D, ~collinear A B C -> parallel A B C D -> parallel A D B C -> parallelogram A B C D;
  (* Transitivity of parallelism. *)
  ax_par_trans : forall A B C D E F, parallel A B C D -> parallel C D E F -> parallel A B E F;
  (* Midpoint theorem *)
  ax_midpoint_th : forall A B C D E, B<>C -> midpoint D A B -> midpoint E A C -> parallel B C D E; 
  (* Converse of midpoint theorem *)
  ax_midpoint_th_converse : forall A B C D E, ~ collinear C A B -> midpoint D A B -> parallel B C D E -> collinear A C E -> midpoint E A C; (* added NDG *)
  (* Alternate angles formed by parallel lines are congruent angles. *)
  ax_angle9 : forall A B C D, opposite_sides D B A C -> parallel A D B C -> congruent_angles A D B C B D; 
  (* If the alternate angles are congruent the lines are parallel. *)
  ax_angle10 : forall A B C D, opposite_sides A C B D -> congruent_angles B A C D C A -> parallel A B C D; (* changed *)
 (* not needed  ax_aaa : forall A B C D E F, ~collinear A B C -> congruent_angles A B C D E F -> congruent_angles B C A E F D -> congruent_angles C A B F D E; (* added NDG ? *) *)
}.