Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.gelertner_inspired_axioms.
Require Import GeoCoq.Main.Tarski_dev.Ch12_parallel_inter_dec.
Require Import GeoCoq.Main.Annexes.quadrilaterals_inter_dec.
Require Import GeoCoq.Main.Annexes.midpoint_theorems.

Section Tarski_neutral_to_Gelertner_neutral.

 Context `{TnEQD:Tarski_2D}.

 Definition Between_strict := fun A B C =>
  Bet A B C /\ A <> B /\ B <> C /\ A <> C.

Instance Gelertner_neutral_2D_follows_from_Tarski_neutral_2D : Gelertner_inspired_neutral_2D.
  Proof.
    eapply (Build_Gelertner_inspired_neutral_2D Tpoint Cong Col Between_strict CongA Per Perp TS OS Par Parallelogram_strict Midpoint Cong_3).
    - finish.
    - finish.
    - finish.
    - finish.
    - intros;intro;subst;finish.  
    - intros. intro. apply H. ColR. 
    - intros. intro. apply H. 
      unfold Between_strict in H0;spliter. 
      assert (Col B C D); finish.
      ColR.
    - intros. unfold Between_strict in H. 
      spliter;finish.
    - intros. unfold Between_strict in H; spliter;finish.
    - intros. unfold Between_strict in H; spliter;finish.
    - intros. unfold Between_strict in H; spliter;finish.
    - intros. unfold Between_strict in *.
      spliter;split;finish.
    - intros. 
      unfold Between_strict in *; spliter. 
      assert (A<>D) by (intro; treat_equalities; intuition).
      repeat split;finish; eBetween.
    - intros. unfold Between_strict in *;spliter.
      assert (A<>D) by 
       (intro; treat_equalities;intuition).
      spliter;repeat split;finish; eBetween.
    - intros. 
      unfold Between_strict in *;spliter.
      unfold TS.
      repeat split.
      assumption.
      assumption.
      exists X.
      split;finish.
    - intros.
      unfold Between_strict in *;spliter.
      unfold TS in *.
      repeat split;finish.
      exists X;finish.
    - intros. unfold Between_strict in *;spliter.
      apply (l11_14 A X C B D );finish.
    - finish.
    - finish.
    - finish.
    - finish.
    - intros; assert_diffs; finish.
    - intros; assert_diffs; finish.
    - finish.
    - finish.
    - finish.
    - intros. apply per_perp;finish.
    - intros. 
      apply l8_16_1 with Z U;finish.
   (*  - intros. apply l12_9_2D with C D; finish. *)
    - finish.
    - finish.
    - intros. eapply par_col_par_2 with B;finish.
    - finish.
    - finish.
    - finish.
    - finish.
    - finish.
    - intros; apply conga_refl;auto.
    - CongA.
    - CongA.
    - intros. unfold Between_strict in *;spliter.
      eapply out2__conga;finish. 
    - intros. 
      unfold Between_strict in *;spliter.
      apply per_col with C;finish. 
    - intros.
      apply l11_17 with A B C;finish.
    - intros. apply l11_16; finish.
    - intros. eauto using conga_trans.
    - finish.
       
    - finish.
    - intros. unfold Between_strict in *;spliter.
      assert_diffs.
      repeat split;finish.
    - intros. unfold Between_strict in *;spliter.
      assert_diffs.
      repeat split;finish.
    - finish.

    - intros. unfold Cong_3 in *.
      repeat split;finish.
    - intros. eauto using cong3_symmetry. 
    - intros. eauto using cong3_transitivity.
    - intros. 
      assert (T:=cong2_conga_cong A B C D E F H1 H0 H2).
      unfold Cong_3;repeat split;finish.
    - intros. unfold Cong_3 in *.
      repeat split;finish.
    - intros. 
      assert (Cong A C D F /\ Cong B C E F /\ CongA A C B D F E) by (
      apply (l11_50_1 A B C D E F);finish);spliter. 
      unfold Cong_3 in *;repeat split;finish.
    - intros.
      assert (Cong A C D F /\ Cong B C E F /\ CongA C A B F D E) by (
      apply (l11_50_2 A B C D E F);finish);spliter. 
      unfold Cong_3 in *;repeat split;finish.
    - intros. unfold Cong_3 in *;spliter.
      repeat split;finish.
    - intros.
       apply cong_3_swap.
       apply cong_3_swap_2.
       assumption.
Defined.

End Tarski_neutral_to_Gelertner_neutral.

Section Tarski_euclidean_to_Gelertner_euclidean.
 
 Context `{Tneunodim:Tarski_neutral_dimensionless}.
 Context `{Tneudeqdec: @Tarski_neutral_dimensionless_with_decidable_point_equality Tneunodim}.
 Context `{Teuc:@Tarski_euclidean Tneunodim Tneudeqdec}.
 Context `{T2D:@Tarski_2D Tneunodim Tneudeqdec}.

Instance Gelertner_euclidean_follows_from_Tarski_euclidean : Gelertner_inspired_euclidean Gelertner_neutral_2D_follows_from_Tarski_neutral_2D.
  Proof.
    constructor.
  - intros. apply parallel_2_plg;auto.
  - intros. 
      unfold parallel in *.
      apply par_trans with C D.
      assumption.
      assumption.
  - intros. 
      apply(triangle_mid_par B C A E D);finish.
  - intros.
     assert (T:=triangle_par_mid C B A D E).
     apply ax_midpoint4.
     apply T;finish.
   - intros.
      apply (l12_21_a D A B C);finish.
   - intros. 
    apply l12_21_b;finish.
Qed.

End Tarski_euclidean_to_Gelertner_euclidean.


Section Gelertner_examples.

Context `{Gelertner_inspired_euclidean}.

Hint Resolve ax_col1 ax_col2 ax_col3 ax_col4 ax_col5 ax_col6 ax_col7
             ax_bet1 ax_bet2 ax_bet3 ax_bet4
             ax_bet_distinct_1 ax_bet_distinct_2 ax_bet_distinct_3
             ax_sides1 ax_sides2 ax_sides5 ax_sides6 ax_sides7 ax_sides9 ax_sides10
             ax_perp_distinct1 ax_perp_distinct2
             ax_perp3 ax_perp4  ax_perp6
             ax_perp_right_angle ax_right_angle_perp
            (*  ax_perp_perp_par *)
             ax_para1 ax_para2
             ax_par_col
             ax_cong1 ax_cong2 ax_cong3
             ax_right_angle_sym
             ax_congruent_angle_trans
             ax_congruent_angle_refl ax_congruent_angle_sym ax_congruent_angle_syma
             ax_congruent_angle_same_half_line ax_supp_right_right ax_congruent_right_right
             ax_right_angles_congruent
             ax_angle1 ax_angle2 
             ax_midpoint1 ax_midpoint2 ax_midpoint3 ax_midpoint4 
             ax_triangle1 ax_triangle2 ax_triangle3 
             ax_sas ax_sss ax_asa ax_saa
             ax_tc ax_tt
             ax_midpoint_th
             ax_midpoint_th_converse
             ax_par_trans
             ax_angle9 ax_angle10
              : Gelertner_all.

Ltac Gel := eauto with Gelertner_all.

(* Theorems from the appendix of Gelertner's paper: 
   REALIZATION OF A GEOMETRY THEOREM PROVING MACHINE. *)

Example thm_appendix_a :
  forall A B C D,
    ~ collinear B A D ->
    ~ collinear B C D ->
    congruent_angles A B D D B C ->
    right_angle B A D ->
    right_angle B C D ->
    cong A D C D.
Proof.
  intros.
  assert (congruent_angles B A D B C D) 
    by (apply ax_right_angles_congruent;Gel).
  assert (congruent_triangles D B C D B A)
    by (apply ax_saa;Gel). 
  Gel.
Qed.

Example thm_appendix_b :
  forall A B C D,
    ~collinear A B D ->
    ~collinear C D B ->
    parallel B C A D ->
    cong B C A D ->
    opposite_sides D B A C ->
    cong A B C D.
Proof.
 intros.
 assert (congruent_angles A D B C B D)
  by (apply ax_angle9;Gel).
 assert (congruent_triangles B D A D B C)
  by (apply ax_sas;Gel).
 Gel.
Qed.


Example thm_appendix_c_with_heuristics :
  forall A B C D M E,
    ~ collinear C E M ->
    ~ collinear B D M -> 
    between_strict B M C ->
    cong B M M C ->
    between_strict A D M ->
    between_strict D M E ->
    perpendicular B D A M ->
    perpendicular C E M E ->
    cong B D E C.
Proof.
  intros.
  assert (congruent_angles D M B E M C ) by Gel.
  assert (right_angle B D A) by Gel. 
  assert (right_angle B D M) by Gel.
  assert (right_angle M E C) by Gel. 
  assert (congruent_angles B D M C E M)
    by (apply ax_right_angles_congruent;Gel).
  assert (congruent_triangles B M D C M E)
    by (eapply ax_saa;Gel).
  Gel.
Qed. 

(* Those two examples a taken from Gelertner's paper :
   EMPIRICAL EXPLORATIONS OF THE GEOMETRY-THEOREM PROVING MACHINE. *)

Example empirical_appendix_1 :
  forall A B C D E F GG HH,
    midpoint E A B ->
    midpoint F A C ->
    midpoint GG C D ->
    midpoint HH B D ->
    ~collinear E F GG ->
    A<>D ->
    B<>C ->
    parallelogram E F GG HH.
Proof.
  intros.
  assert (parallel A D F GG) by Gel.
  assert (parallel A D  E HH) by Gel.
  assert (parallel F GG E HH) by Gel.
  assert (parallel B C E F) by Gel.
  assert (parallel B C GG HH) by Gel.
  assert (parallel E F GG HH) by Gel.
  apply ax_parallelogram1; Gel.
Qed.

Example empirical_appendix_2 :
  forall A B C D E F M K,
    ~collinear F B C ->     
    ~collinear A B D ->
    ~collinear F D K ->
    A <> K -> 
    A <> D ->  
    K <> D -> 
    E <> F ->
    C <> A ->
    D <> B -> 
    F <> M ->
    parallel A D B C ->
    midpoint E A C ->
    midpoint F B D ->
    between_strict M E F ->
    between_strict A M B ->
    between_strict C F K ->
    collinear A K D ->
    opposite_sides D B K C  ->
    cong M B M A.
Proof.
  intros.
  assert (parallel K D B C) by Gel.
  assert (congruent_angles K D B C B D) by Gel.
  assert (between_strict D F B) by Gel.
  assert (cong D F F B) by Gel.
  assert (congruent_angles K F D C F B) by Gel.
  assert (congruent_angles B D K F D K) by Gel.
  assert (congruent_angles B D K K D F) by Gel.
  assert (congruent_angles D B C F B C) by Gel.
  assert (congruent_angles C B D C B F) by Gel.
  assert (congruent_angles K D F C B F) by Gel.
  assert (congruent_triangles F D K  F B C)
    by (apply (ax_asa F D K  F B C);Gel).
  assert (cong K F C F) by Gel.
  assert (cong C E E A) by Gel.
  assert (between_strict C E A) by Gel.
  assert (midpoint F K C) by Gel.
  assert (parallel A K E F) by (eapply ax_midpoint_th; Gel).
  assert (parallel E F K D) by Gel.
  assert (parallel F E B C) by Gel.
  assert (collinear M E F) by Gel.
  assert (parallel F M B C) by Gel. 
  assert (parallel F M D A) by Gel.
  assert (collinear A M B) by Gel.
  assert (midpoint M B A) by (eapply ax_midpoint_th_converse; Gel).
  Gel.
Qed.

End Gelertner_examples.