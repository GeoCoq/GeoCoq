(** * Euclid's Elements

  Book I
*)

(**
  We present in this file the formalization of the propositions
  from the first book of Euclid Elements.
  Our formal proofs are not formalizations of
  Euclid’s proof, the proof can be very different
  because we do not use the axiom system of Euclid.
  The proofs are performed in the context of Tarski's axioms.
  But we have proven the bi-interpretability with
  the corresponding Hilbert's axioms,
  hence the use can choose his favorite axiom system.

  The english version of the propositions is imported from the
  xml version version of Euclid's Elements provided by the Perseus project:
  http://www.perseus.tufts.edu/hopper/text?doc=Perseus:text:1999.01.0086
  The GeoGebra figures have been created by Gianluigi Trivia.

  Hence, this file is licenced under
  https://creativecommons.org/licenses/by-sa/3.0/us/
  in addition to LGPL 3.0.
*)

(** #
<script type="text/javascript" src="https://www.geogebra.org/scripts/deployggb.js"></script>
<script type="text/javascript">
    var applet1 = new GGBApplet({material_id: "r4D6cEeh"}, true);
    var applet2 = new GGBApplet({material_id: "ERFPd6Gx"}, true);
    var applet3 = new GGBApplet({material_id: "rXcJrHZh"}, true);
    var applet4 = new GGBApplet({material_id: "uEgvYkrc"}, true);
    var applet5 = new GGBApplet({material_id: "tn33uzyD"}, true);
    var applet6 = new GGBApplet({material_id: "VCsxJRRH"}, true);
    var applet7 = new GGBApplet({material_id: "d5dMrQXs"}, true);
    var applet8 = new GGBApplet({material_id: "aQqPfsMd"}, true);
    var applet9 = new GGBApplet({material_id: "RjFXAa9f"}, true);
    var applet10 = new GGBApplet({material_id: "mmRErFqd"}, true);
    var applet11 = new GGBApplet({material_id: "pMdtFxq6"}, true);
    var applet12 = new GGBApplet({material_id: "z5AkXe6N"}, true);
    var applet13 = new GGBApplet({material_id: "ZAHjwcyc"}, true);
    var applet14 = new GGBApplet({material_id: "UKg84dFT"}, true);
    var applet15 = new GGBApplet({material_id: "bnjUjQ9X"}, true);
    var applet16 = new GGBApplet({material_id: "Gg6rHEs3"}, true);
    var applet17 = new GGBApplet({material_id: "npxkCJpC"}, true);
    var applet18 = new GGBApplet({material_id: "VFYgBjGh"}, true);
    var applet19 = new GGBApplet({material_id: "AfKPEzb7"}, true);
    var applet20 = new GGBApplet({material_id: "fH6japew"}, true);
    var applet21 = new GGBApplet({material_id: "rXrbmX4t"}, true);
    var applet22 = new GGBApplet({material_id: "vc4qEQeN"}, true);
    var applet23 = new GGBApplet({material_id: "bThxPU7Q"}, true);
    var applet24 = new GGBApplet({material_id: "Tuz27uFN"}, true);
    var applet25 = new GGBApplet({material_id: "WwqvjYpu"}, true);
    var applet26 = new GGBApplet({material_id: "JUMQJ7pm"}, true);
    var applet27 = new GGBApplet({material_id: "bVZjmJwk"}, true);
    var applet28 = new GGBApplet({material_id: "zsQmywaj"}, true);
    var applet29 = new GGBApplet({material_id: "DhjHHgP5"}, true);
    var applet30 = new GGBApplet({material_id: "bKxnmXBq"}, true);
    var applet31 = new GGBApplet({material_id: "FfT7t9Cu"}, true);
    var applet32 = new GGBApplet({material_id: "mcBCaz8R"}, true);
    var applet33 = new GGBApplet({material_id: "k48aN5wj"}, true);
    var applet34 = new GGBApplet({material_id: "KgPuPTfy"}, true);
    var applet35 = new GGBApplet({material_id: "C7YJBaaB"}, true);
    var applet36 = new GGBApplet({material_id: "gdesjdZD"}, true);
    var applet37 = new GGBApplet({material_id: "TNp5dZa6"}, true);
    var applet38 = new GGBApplet({material_id: "B4FWM9g7"}, true);
    var applet39 = new GGBApplet({material_id: "jHyHD9q7"}, true);
    var applet40 = new GGBApplet({material_id: "W5SANQJp"}, true);
    var applet41 = new GGBApplet({material_id: "ZQtgFvAM"}, true);
    var applet42 = new GGBApplet({material_id: "UQYRQX7w"}, true);
    var applet43 = new GGBApplet({material_id: "anfyFSKf"}, true);
    var applet44 = new GGBApplet({material_id: "y6tFXckE"}, true);
    var applet45 = new GGBApplet({material_id: "vJQkwr7r"}, true);
    var applet46 = new GGBApplet({material_id: "GnrYvWx3"}, true);
    var applet47 = new GGBApplet({material_id: "tdxHWEBA"}, true);
    var applet48 = new GGBApplet({material_id: "T4HcNAgy"}, true);

    window.onload = function() {
        applet1.inject('applet_container1', 'preferHTML5');
        applet2.inject('applet_container2', 'preferHTML5');
        applet3.inject('applet_container3', 'preferHTML5');
        applet4.inject('applet_container4', 'preferHTML5');
        applet5.inject('applet_container5', 'preferHTML5');
        applet6.inject('applet_container6', 'preferHTML5');
        applet7.inject('applet_container7', 'preferHTML5');
        applet8.inject('applet_container8', 'preferHTML5');
        applet9.inject('applet_container9', 'preferHTML5');
        applet10.inject('applet_container10', 'preferHTML5');
        applet11.inject('applet_container11', 'preferHTML5');
        applet12.inject('applet_container12', 'preferHTML5');
        applet13.inject('applet_container13', 'preferHTML5');
        applet14.inject('applet_container14', 'preferHTML5');
        applet15.inject('applet_container15', 'preferHTML5');
        applet16.inject('applet_container16', 'preferHTML5');
        applet17.inject('applet_container17', 'preferHTML5');
        applet18.inject('applet_container18', 'preferHTML5');
        applet19.inject('applet_container19', 'preferHTML5');
        applet20.inject('applet_container20', 'preferHTML5');
        applet21.inject('applet_container21', 'preferHTML5');
        applet22.inject('applet_container22', 'preferHTML5');
        applet23.inject('applet_container23', 'preferHTML5');
        applet24.inject('applet_container24', 'preferHTML5');
        applet25.inject('applet_container25', 'preferHTML5');
        applet26.inject('applet_container26', 'preferHTML5');
        applet27.inject('applet_container27', 'preferHTML5');
        applet28.inject('applet_container28', 'preferHTML5');
        applet29.inject('applet_container29', 'preferHTML5');
        applet30.inject('applet_container30', 'preferHTML5');
        applet31.inject('applet_container31', 'preferHTML5');
        applet32.inject('applet_container32', 'preferHTML5');
        applet33.inject('applet_container33', 'preferHTML5');
        applet34.inject('applet_container34', 'preferHTML5');
        applet35.inject('applet_container35', 'preferHTML5');
        applet36.inject('applet_container36', 'preferHTML5');
        applet37.inject('applet_container37', 'preferHTML5');
        applet38.inject('applet_container38', 'preferHTML5');
        applet39.inject('applet_container39', 'preferHTML5');
        applet40.inject('applet_container40', 'preferHTML5');
        applet41.inject('applet_container41', 'preferHTML5');
        applet42.inject('applet_container42', 'preferHTML5');
        applet43.inject('applet_container43', 'preferHTML5');
        applet44.inject('applet_container44', 'preferHTML5');
        applet45.inject('applet_container45', 'preferHTML5');
        applet46.inject('applet_container46', 'preferHTML5');
        applet47.inject('applet_container47', 'preferHTML5');
        applet48.inject('applet_container48', 'preferHTML5');
    } </script>
# **)

Require Export GeoCoq.Axioms.continuity_axioms.
Require Export GeoCoq.Tarski_dev.Annexes.sums.
Require Export GeoCoq.Tarski_dev.Annexes.circles.
Require Export GeoCoq.Tarski_dev.Ch16_coordinates_with_functions.

(** * Proposition 1
       On a given finite straight line to construct an equilateral triangle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container1"></div> # **)


(** We proved this proposition in the context of euclidean geometry without any continuity axiom.
    It can also be proven more easily assuming a circle-circle intersection axiom,
    as Euclid implicitly did.
    Victor Pambuccian has shown that these hypotheses are minimal.
*)


Section Book_1_prop_1_euclidean.

Context `{TE:Tarski_2D_euclidean}.

Lemma prop_1_euclidean :
 forall A B,
  exists C, Cong A B A C /\ Cong A B B C.
Proof.
 destruct exists_grid_spec as [SS [U1 [U2  Hgrid]]].
  apply (exists_equilateral_triangle SS U1 U2 Hgrid).
Qed.

End Book_1_prop_1_euclidean.

Section Book_1_prop_1_circle_circle.

Context `{TE:Tarski_2D}.

Lemma prop_1_circle_circle :
circle_circle_bis ->
 forall A B,
  exists C, Cong A B A C /\ Cong A B B C.
Proof.
intros.
unfold circle_circle_bis in H.
destruct (H A B B A A B) as [C [HC1 HC2]];Circle.
exists C.
unfold OnCircle in *.
split;Cong.
Qed.

End Book_1_prop_1_circle_circle.


Section Book_1_part_2.

  (** For the next 27 proposition, we do not need the 5th axiom of Euclid,
      nor any continuity axioms, except for Proposition 22, which needs Circle/Circle intersection axiom
  *)

Context `{TE:Tarski_2D}.
	    (** * Proposition 2
       To place at a given point (as an extremity) a straight line equal to a given straight line.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container2"></div> # **)


Lemma prop_2 : forall A B C D, exists E : Tpoint, Bet A B E /\ Cong B E C D.
Proof.
  apply segment_construction.
Qed.


	    (** * Proposition 3
       Given two unequal straight lines, to cut off from the greater a straight line equal to the less. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container3"></div> # **)

Lemma prop_3 : forall A B C D, Le A B C D -> exists E : Tpoint, Bet C E D /\ Cong A B C E.
Proof.
  auto.
Qed.


	    (** * Proposition 4
       If two triangles have the two sides equal to two sides respectively, and have the angles contained by the equal straight lines equal, they will also have the base equal to the base, the triangle will be equal to the triangle, and the remaining angles will be equal to the remaining angles respectively, namely those which the equal sides subtend.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container4"></div> # **)

Lemma prop_4 : forall A B C A' B' C', CongA A B C A' B' C' -> Cong B A B' A' -> Cong B C B' C' ->
  Cong A C A' C' /\ (A <> C -> CongA B A C B' A' C' /\ CongA B C A B' C' A').
Proof.
  apply l11_49.
Qed.


	    (** * Proposition 5
       In isosceles triangles the angles at the base are equal to one another, and, if the equal straight lines be produced further, the angles under the base will be equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container5"></div> # **)

Lemma prop_5_1 : forall A B C, ~ Col A B C -> Cong B A B C -> CongA B A C B C A.
Proof.
  apply l11_44_1_a.
Qed.

Lemma prop_5_2 : forall A B C A' C', ~ Col A B C -> Cong B A B C ->
  Bet B A A' -> A <> A' -> Bet B C C' -> C <> C' ->
  CongA A' A C C' C A.
Proof.
  intros A B C A' C'.
  intros.
  apply l11_13 with B B; auto.
  apply l11_44_1_a; assumption.
Qed.


	    (** * Proposition 6
       If in a triangle two angles be equal to one another, the sides which subtend the equal angles will also be equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container6"></div> # **)

Lemma prop_6 : forall A B C, ~ Col A B C -> CongA B A C B C A -> Cong B A B C.
Proof.
  apply l11_44_1_b.
Qed.


	    (** * Proposition 7
       Given two straight lines constructed on a straight line (from its extremities) and meeting in a point, there cannot be constructed on the same straight line (from its extremities), and on the same side of it, two other straight lines meeting in another point and equal to the former two respectively, namely each to that which has the same extremity with it.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container7"></div> # **)

Lemma prop_7 : forall A B C C', Cong A C A C' -> Cong B C B C' -> OS A B C C' -> C = C'.
Proof.
  intros A B C C' HCongA HCongB HOS.
  assert (HNCol := one_side_not_col123 A B C C' HOS).
  assert_diffs.
  destruct (l11_51 A B C A B C') as [HCongAA [HCongAB HCongAC]]; Cong.
  apply l9_9_bis in HOS.
  destruct (conga__or_out_ts B A C C' HCongAA) as [HOutA|Habs]; [|exfalso; apply HOS; Side].
  destruct (conga__or_out_ts A B C C' HCongAB) as [HOutB|Habs].
    apply (l6_21 A C B C); Col.
  exfalso; apply HOS, Habs.
Qed.


	    (** * Proposition 8
       If two triangles have the two sides equal to two sides respectively, and have also the base equal to the base, they will also have the angles equal which are contained by the equal straight lines. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container8"></div> # **)

Lemma prop_8 : forall A B C A' B' C', A <> B -> A <> C -> B <> C ->
       Cong A B A' B' -> Cong A C A' C' -> Cong B C B' C' ->
       CongA B A C B' A' C' /\ CongA A B C A' B' C' /\ CongA B C A B' C' A'.
Proof.
  apply l11_51.
Qed.


	    (** * Proposition 9
       To bisect a given rectilineal angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container9"></div> # **)

Lemma prop_9 : forall A B C, A <> B -> C <> B ->
  exists P : Tpoint, InAngle P A B C /\ CongA P B A P B C.
Proof.
  apply angle_bisector.
Qed.


	    (** * Proposition 10
       To bisect a given finite straight line.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container10"></div> # **)

Lemma prop_10 : forall A B, exists X : Tpoint, Midpoint X A B.
Proof.
  apply midpoint_existence.
Qed.


	    (** * Proposition 11
       To draw a straight line at right angles to a given straight line from a given point on it.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container11"></div> # **)

Lemma prop_11 : forall A B C, A <> B -> Col A B C -> exists X, Perp A B X C.
Proof.
  intros A B C HAB HCol.
  destruct (not_col_exists A B HAB) as [P HNCol].
  destruct (l10_15 A B C P HCol HNCol) as [X [HPerp HOS]].
  exists X; assumption.
Qed.


	    (** * Proposition 12
       To a given infinite straight line, from a given point which is not on it, to draw a perpendicular straight line.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container12"></div> # **)

Lemma prop_12 : forall A B C, ~ Col A B C ->
  exists X : Tpoint, Col A B X /\ Perp A B C X.
Proof.
  apply l8_18_existence.
Qed.


	    (** * Proposition 13
       If a straight line set up on a straight line make angles, it will make either two right angles or angles equal to two right angles.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container13"></div> # **)

Lemma prop_13 : forall A B C D P Q R, A <> B -> B <> C -> B <> D -> Bet A B C ->
  P <> Q -> Q <> R -> Per P Q R ->
  SumA A B D D B C A B C /\ SumA P Q R P Q R A B C.
Proof.
  intros A B C D P Q R HAB HBC HBD HBet HPQ HQR HPer.
  split.
    apply bet__suma; auto.
  destruct (ex_suma P Q R P Q R) as [S [T [U HSuma]]]; auto.
  apply conga3_suma__suma with P Q R P Q R S T U; try (apply conga_refl); auto.
  assert_diffs.
  apply conga_line; auto.
  apply (per2_suma__bet P Q R P Q R); assumption.
Qed.


	    (** * Proposition 14
       If with any straight line, and at a point on it, two straight lines not lying on the same side make the adjacent angles equal to two right angles, the two straight lines will be in a straight line with one another. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container14"></div> # **)

Lemma prop_14 : forall A B C D, TS A B C D -> Per A B C -> Per A B D -> Bet C B D.
Proof.
  intros A B C D HTS HPer1 HPer2.
  apply (per2_suma__bet A B C A B D); trivial.
  apply suma_left_comm.
  exists D.
  assert_diffs.
  split; CongA.
  split; CongA; Side.
Qed.


	    (** * Proposition 15
       If two straight lines cut one another, they make the vertical angles equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container15"></div> # **)

Lemma prop_15 : forall A B C A' C', Bet A B A' ->  A <> B -> A' <> B ->
  Bet C B C' -> B <> C -> B <> C' ->
  CongA A B C A' B C'.
Proof.
  apply l11_14.
Qed.


	    (** * Proposition 16
       In any triangle, if one of the sides is produced, the exterior angle is greater than either of the interior and opposite angles.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container16"></div> # **)

Lemma prop_16 : forall A B C D, ~ Col A B C -> Bet B A D -> A <> D ->
  LtA A C B C A D /\ LtA A B C C A D.
Proof.
  apply l11_41.
Qed.


	    (** * Proposition 17
       In any triangle two angles taken together in any manner are less than two right angles.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container17"></div> # **)

Lemma prop_17 : forall A B C D E F, ~ Col A B C -> SumA A B C B C A D E F -> 
  SAMS A B C B C A /\ ~ Col D E F.
Proof.
  intros A B C HNCol HSumA.
  split.
  - assert_diffs.
    apply sams123231; auto.
  - apply (ncol_suma__ncol A B C); assumption.
Qed.


	    (** * Proposition 18
       In any triangle the greater side subtends the greater angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container18"></div> # **)

Lemma prop_18 : forall A B C, ~ Col A B C -> Lt B A B C -> Lt C A C B ->
  LtA B C A B A C /\ LtA A B C B A C.
Proof.
  intros.
  split.
  - apply l11_44_2_a; assumption.
  - apply lta_comm, l11_44_2_a; Col.
Qed.


	    (** * Proposition 19
       In any triangle the greater angle is subtended by the greater side.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container19"></div> # **)

Lemma prop_19 : forall A B C, ~ Col A B C -> LtA B A C B C A -> LtA B A C A B C ->
  Lt B C B A /\ Lt C B C A.
Proof.
  intros.
  split.
  - apply l11_44_2_b; assumption.
  - apply l11_44_2_b; Col.
    apply lta_comm; assumption.
Qed.


	    (** * Proposition 20
       In any triangle two sides taken together in any manner are greater than the remaining one.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container20"></div> # **)

Lemma prop_20 : forall A B C D E, ~ Bet A B C -> SumS A B B C D E -> Lt A C D E.
Proof.
  intros A B C D E HNBet HSum.
  destruct (segment_construction A B B C) as [D' [HBet HCong]].
  apply (cong2_lt__lt A C A D'); Cong.
    apply triangle_strict_inequality with B; Cong.
  apply (sums2__cong56 A B B C); trivial.
  exists A, B, D'; repeat split; Cong.
Qed.


	    (** * Proposition 21
       If on one of the sides of a triangle, from its extremities, there be constructed two straight lines meeting within the triangle, the straight lines so constructed will be less than the remaining two sides of the triangle, but will contain a greater angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container21"></div> # **)

Lemma prop_21_1 : forall A B C D, OS A B C D -> OS B C A D -> OS A C B D -> LtA B A C B D C.
Proof.
  apply os3__lta.
Qed.

Lemma prop_21_2 : forall A B C D A1 A2 D1 D2, OS A B C D -> OS B C A D -> OS A C B D ->
  SumS A B A C A1 A2 -> SumS D B D C D1 D2 -> Lt D1 D2 A1 A2.
Proof.
  intros A B C D A1 A2 D1 D2; intros.
  assert (HNCol : ~ Col A B C) by (apply one_side_not_col123 with D; assumption).
  destruct (os2__inangle A B C D) as [HAB [HCB [HDB [E [HBet [Heq|HOut]]]]]]; Side.
    subst; exfalso; apply HNCol; ColR.
  assert_diffs.
  assert (A <> E) by (intro; subst E; apply (one_side_not_col124 A B C D); Col).
  assert (C <> E) by (intro; subst E; apply (one_side_not_col124 B C A D); Col).
  assert (D <> E) by (intro; subst E; apply (one_side_not_col124 A C B D); Col).
  assert (Bet B D E).
    apply out2__bet; [apply l6_6, HOut|].
    apply col_one_side_out with A; Col.
    apply invert_one_side, col_one_side with C; Col.
  destruct (ex_sums E B E C) as [P [Q]].
  apply lt_transitivity with P Q.
  - destruct (ex_sums E C E D) as [R [S]].
    apply le_lt34_sums2__lt with D B D C D B R S; Le.
      apply prop_20 with E; Sums.
      intro; apply HNCol; ColR.
    apply sums_assoc_1 with E D E C E B; Sums.
  - destruct (ex_sums A B A E) as [R [S]].
    apply le_lt12_sums2__lt with E B E C R S E C; Le.
      apply prop_20 with A; Sums.
      intro; apply HNCol; ColR.
    apply sums_assoc_2 with A B A E A C; Sums.
Qed.


	    (** * Proposition 22
       Out of three straight lines, which are equal to three given straight lines, to construct a triangle: thus it is necessary that two of the straight lines taken together in any manner should be greater than the remaining one (cf. [I. 20]).
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container22"></div> # **)

      (** This needs Circle/Circle intersection axiom *)

Lemma prop_22_aux : forall A B C D E F A' B' E' F' C1 C2 E1,
  SumS A B C D E' F' -> SumS C D E F A' B' -> Le E F E' F' -> Le A B A' B' ->
  Out A B C1 -> Cong A C1 C D -> Bet B A C2 -> Cong A C2 C D ->
  Out B A E1 -> Cong B E1 E F ->
  Bet C1 E1 C2.
Proof.
  intros A B C D E F A' B' E' F'; intros.
  assert (Bet C1 A C2) by (assert_diffs; apply l6_2 with B; auto).
  apply not_out_bet.
    ColR.
  intro HOut; destruct HOut as [HC1E1 [HC2E1 [HBet|HBet]]].
  - assert (Bet A C1 E1) by eBetween.
    assert (Bet A E1 B).
      apply out2__bet; trivial.
      apply l6_7 with C1; apply l6_6; trivial.
      assert_diffs; apply bet_out; trivial.
    apply (le__nlt A B A' B'); trivial.
    apply le_lt12_sums2__lt with C D E F A E1 E1 B; Sums; Le.
    split.
      exists C1; split; Cong.
    intro HCong.
    apply HC1E1, between_cong with A; trivial.
    apply cong_transitivity with C D; trivial.
  - assert (Bet A C2 E1) by eBetween.
    assert (Bet B C2 E1) by (assert_diffs; apply l6_2 with A; auto; apply bet_out; Between).
    apply (le__nlt E F E' F'); trivial.
    apply (cong2_lt__lt B C2 B E1); Cong.
      split; [exists C2; Cong|].
      intro HCong.
      apply HC2E1, between_cong with B; trivial.
    apply (sums2__cong56 A B C D); trivial; exists B, A, C2; repeat split; Cong.
Qed.

Lemma prop_22 : circle_circle_bis -> forall A B C D E F A' B' C' D' E' F',
  SumS A B C D E' F' -> SumS A B E F C' D' -> SumS C D E F A' B' ->
  Le E F E' F' -> Le C D C' D' -> Le A B A' B' ->
  exists P Q R, Cong P Q A B /\ Cong P R C D /\ Cong Q R E F.
Proof.
  intros Hcc A B C D E F A' B' C' D' E' F' HSum1 HSum2 HSum3 HLe1 HLe2 HLe3.
  exists A, B.
  destruct (eq_dec_points A B); [|destruct (eq_dec_points C D)]; [| |destruct (eq_dec_points E F)].
  - destruct (segment_construction_0 C D A) as [P HCong].
    exists P; repeat split; Cong.
    subst B.
    apply cong_transitivity with C D; trivial.
    apply le_anti_symmetry.
      apply (l5_6 C D C' D'); Cong; apply (sums2__cong56 A A E F); Sums.
      apply (l5_6 E F E' F'); Cong; apply (sums2__cong56 A A C D); Sums.
  - exists A; treat_equalities; repeat split; Cong.
    apply le_anti_symmetry.
      apply (l5_6 A B A' B'); Cong; apply (sums2__cong56 C C E F); Sums.
      apply (l5_6 E F E' F'); Cong; apply (sums2__cong56 A B C C); Sums.
  - exists B; treat_equalities; repeat split; Cong.
    apply le_anti_symmetry.
      apply (l5_6 A B A' B'); Cong; apply (sums2__cong56 C D E E); Sums.
      apply (l5_6 C D C' D'); Cong; apply (sums2__cong56 A B E E); Sums.
  - destruct (segment_construction_3 A B C D) as [C1 [HC1 HC1']]; auto.
    destruct (segment_construction_3 B A E F) as [E1 [HE1 HE1']]; auto.
    destruct (segment_construction B A C D) as [C2 [HC2 HC2']].
    destruct (segment_construction A B E F) as [E2 [HE2 HE2']].
    assert (Bet C1 E1 C2) by (apply (prop_22_aux A B C D E F A' B' E' F'); trivial).
    assert (Bet E1 C1 E2) by (apply (prop_22_aux B A E F C D B' A' C' D'); Sums; Le).
    destruct (Hcc A C1 B E1 E1 C1) as [Z [HZ1 HZ2]]; Circle.
      apply bet_inc2__inc with C1 C2; Circle; apply onc__inc, cong_transitivity with C D; Cong.
      apply bet_inc2__inc with E1 E2; Circle; apply onc__inc, cong_transitivity with E F; Cong.
    exists Z; repeat split; Cong.
      apply cong_transitivity with A C1; Cong.
      apply cong_transitivity with B E1; Cong.
Qed.


	    (** * Proposition 23
       On a given straight line and at a point on it to construct a rectilineal angle equal to a given rectilineal angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container23"></div> # **)

Lemma prop_23 : forall A B C A' B', A <> B -> A <> C -> B <> C -> A' <> B' ->
  exists C', CongA A B C A' B' C'.
Proof.
  intros A B C A' B'.
  intros.
  destruct (not_col_exists A' B') as [P HNCol]; trivial.
  destruct (angle_construction_2 A B C A' B' P) as [C' [HCongA]]; auto.
  exists C'; assumption.
Qed.

	    (** * Proposition 24
       If two triangles have the two sides equal to two sides respectively, but have the one of the angles contained by the equal straight lines greater than the other, they will also have the base greater than the base. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container24"></div> # **)

Lemma prop_24 : forall A B C D E F, Cong A B D E -> Cong A C D F -> LtA F D E C A B ->
  Lt E F B C.
Proof.
  apply t18_18.
Qed.


	    (** * Proposition 25
       If two triangles have the two sides equal to two sides respectively, but have the base greater than the base, they will also have the one of the angles contained by the equal straight lines greater than the other.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container25"></div> # **)

Lemma prop_25 : forall A B C D E F, A <> B -> A <> C ->
  Cong A B D E -> Cong A C D F -> Lt E F B C ->
  LtA F D E C A B.
Proof.
  apply t18_19.
Qed.


	    (** * Proposition 26
       If two triangles have the two angles equal to two angles respectively, and one side equal to one side, namely, either the side adjoining the equal angles, or that subtending one of the equal angles, they will also have the remaining sides equal to the remaining sides and the remaining angle to the remaining angle. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container26"></div> # **)

Lemma prop_26_1 : forall A B C A' B' C', ~ Col A B C ->
       CongA B A C B' A' C' -> CongA A B C A' B' C' -> Cong A B A' B' ->
       Cong A C A' C' /\ Cong B C B' C' /\ CongA A C B A' C' B'.
Proof.
  apply l11_50_1.
Qed.

Lemma prop_26_2 : forall A B C A' B' C', ~ Col A B C ->
       CongA B C A B' C' A' -> CongA A B C A' B' C' -> Cong A B A' B' ->
       Cong A C A' C' /\ Cong B C B' C' /\ CongA C A B C' A' B'.
Proof.
  apply l11_50_2.
Qed.


	    (** * Proposition 27
       If a straight line falling on two straight lines make the alternate angles equal to one another, the straight lines will be parallel to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container27"></div> # **)

Lemma prop_27 : forall A B C D, TS A C B D -> CongA B A C D C A -> Par A B C D.
Proof.
  apply l12_21_b.
Qed.


	    (** * Proposition 28
       If a straight line falling on two straight lines make the exterior angle equal to the interior and opposite angle on the same side, or the interior angles on the same side equal to two right angles, the straight lines will be parallel to one another. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container28"></div> # **)

Lemma prop_28_1 : forall A B C D P, Out P A C -> OS P A B D -> CongA B A P D C P ->
  Par A B C D.
Proof.
  apply l12_22_b.
Qed.

Lemma prop_28_2 : forall A B C D P Q R, OS B C A D -> SumA A B C B C D P Q R -> Bet P Q R ->
  Par A B C D.
Proof.
  intros A B C D P Q R HOS HSumA HBet.
  destruct (segment_construction D C D C) as [D' [HBet' HCong]].
  apply par_left_comm.
  assert_diffs.
  apply par_col_par with D'; Col.
  apply l12_21_b.
  - apply l9_8_2 with D; Side.
    assert (HNCol := one_side_not_col124 B C A D HOS).
    repeat split; Col.
      intro; apply HNCol; ColR.
    exists C; Col.
  - apply between_symmetry in HBet'.
    assert (HCongA : CongA D' C D P Q R) by (apply conga_line; auto).
    assert (HSumA' : SumA D' C B B C D P Q R).
      apply conga3_suma__suma with D' C B B C D D' C D; CongA; SumA.
    apply sams2_suma2__conga123 with B C D P Q R; trivial;
      apply bet_suma__sams with P Q R; assumption.
Qed.

End Book_1_part_2.

(** The following propositions are valid only in Euclidean geometry, except for Proposition 31, which is valid in neutral geometry. *)

Section Book_1_part_3.


Context `{TE:Tarski_2D_euclidean}.

	    (** * Proposition 29
       A straight line falling on parallel straight lines makes the alternate angles equal to one another, the exterior angle equal to the interior and opposite angle, and the interior angles on the same side equal to two right angles. 
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container29"></div> # **)

Lemma prop_29_1 : forall A B C D, TS A C B D -> Par A B C D -> CongA B A C D C A.
Proof.
  apply l12_21_a.
Qed.

Lemma prop_29_2 : forall A B C D P, Out P A C -> OS P A B D -> Par A B C D ->
  CongA B A P D C P.
Proof.
  apply l12_22_a.
Qed.

Lemma prop_29_3 : forall A B C D P Q R, OS B C A D -> Par A B C D -> SumA A B C B C D P Q R ->
  Bet P Q R.
Proof.
  apply alternate_interior__consecutive_interior.
  unfold alternate_interior_angles_postulate.
  apply l12_21_a.
Qed.


	    (** * Proposition 30
       Straight lines parallel to the same straight line are also parallel to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container30"></div> # **)

Lemma prop_30 : forall A1 A2 B1 B2 C1 C2, Par A1 A2 B1 B2 -> Par B1 B2 C1 C2 ->
   Par A1 A2 C1 C2.
Proof.
  apply par_trans.
Qed.

End Book_1_part_3.


Section Book_1_part_4.
	    (** * Proposition 31
       Through a given point to draw a straight line parallel to a given straight line.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container31"></div> # **)

Context `{TE:Tarski_2D}.

Lemma prop_31 : forall A B P, A <> B -> exists Q, Par A B P Q.
Proof.
  apply parallel_existence1.
Qed.

End Book_1_part_4.

Section Book_1_part_5.

Context `{TE:Tarski_2D_euclidean}.
	    (** * Proposition 32
       In any triangle, if one of the sides be produced, the exterior angle is equal to the two interior and opposite angles, and the three interior angles of the triangle are equal to two right angles.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container32"></div> # **)

Lemma prop_32_1 : forall A B C D E F, TriSumA A B C D E F -> Bet D E F.
Proof.
  apply alternate_interior__triangle.
  unfold alternate_interior_angles_postulate.
  apply l12_21_a.
Qed.

Lemma prop_32_2 : forall A B C D, A <> B -> B <> C -> A <> C -> Bet B A D -> A <> D ->
  SumA A B C B C A C A D.
Proof.
  intros A B C D HAB HBC HAC HBet HAD.
  destruct (ex_trisuma A B C HAB HBC HAC) as [P [Q [R HTri]]].
  assert (Bet P Q R) by (apply (prop_32_1 A B C), HTri).
  destruct HTri as [S [T [U [HSuma1 HSumA2]]]].
  apply conga3_suma__suma with A B C B C A S T U; try (apply conga_refl); auto.
  assert_diffs.
  assert (HCongA : CongA B A D P Q R) by (apply conga_line; auto).
  assert (HSumA' : SumA C A D C A B P Q R).
    apply conga3_suma__suma with C A D C A B B A D; CongA; SumA.
  apply sams2_suma2__conga123 with C A B P Q R; trivial;
    apply bet_suma__sams with P Q R; assumption.
Qed.


	    (** * Proposition 33
       The straight lines joining equal and parallel straight lines (at the extremities which are) in the same directions (respectively) are themselves also equal and parallel.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container33"></div> # **)

Lemma prop_33 : forall A B C D,
 TS A C B D -> Par A B C D -> Cong A B C D ->
 Cong A B C D /\ Cong A D B C /\ Par A D B C.
Proof.
  intros A B C D HTS HPAR HC.
  assert (HPara:Parallelogram A B C D) by (unfold Parallelogram;left;unfold Parallelogram_strict;auto).
  assert (T:=plg_cong A B C D HPara).
  assert_diffs.
  assert (HBC:B<>C) by auto.
  assert (HPar:=plg_par A B C D H2 HBC HPara).
  spliter;repeat split; finish.
Qed.

	    (** * Proposition 34
       In parallelogrammic areas the opposite sides and angles are equal to one another, and the diameter bisects the areas.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container34"></div> # **)

Lemma prop_34_1 : forall A B C D : Tpoint,
  A <> B /\ A <> C /\ B <> C ->
  Parallelogram A B C D -> (CongA A B C C D A /\ CongA B C D D A B) /\ (Cong A B C D /\ Cong A D B C).
Proof.
  intros;split. 
  apply plg_conga;auto.
  apply plg_cong;auto.
Qed.

	    (** * Proposition 35
       Parallelograms which are on the same base and in the same parallels are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container35"></div> # **)
	  
	    (** * Proposition 36
       Parallelograms which are on equal bases and in the same parallels are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container36"></div> # **)
	  
	    (** * Proposition 37
       Triangles which are on the same base and in the same parallels are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container37"></div> # **)
	  
	    (** * Proposition 38
       Triangles which are on equal bases and in the same parallels are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container38"></div> # **)
	  
	    (** * Proposition 39
       Equal triangles which are on the same base and on the same side are also in the same parallels.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container39"></div> # **)
	  
	    (** * Proposition 40
       Equal triangles which are on equal bases and on the same side are also in the same parallels.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container40"></div> # **)
	  
	    (** * Proposition 41
       If a parallelogram have the same base with a triangle and be in the same parallels, the parallelogram is double of the triangle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container41"></div> # **)
	  
	    (** * Proposition 42
       To construct, in a given rectilineal angle, a parallelogram equal to a given triangle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container42"></div> # **)
	  
	    (** * Proposition 43
       In any parallelogram the complements of the parallelograms about the diameter are equal to one another.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container43"></div> # **)
	  
	    (** * Proposition 44
       To a given straight line to apply, in a given rectilineal angle, a parallelogram equal to a given triangle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container44"></div> # **)
	  
	    (** * Proposition 45
       To construct, in a given rectilineal angle, a parallelogram equal to a given rectilineal figure.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container45"></div> # **)
	  
	    (** * Proposition 46
       On a given straight line to describe a square.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container46"></div> # **)



Lemma prop_46 : forall A B, A<>B -> exists C D,  Square A B C D.
Proof.
  exact exists_square.
Qed.


	    (** * Proposition 47
       In right-angled triangles the square on the side subtending the right angle is equal to the squares on the sides containing the right angle.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container47"></div> # **)

      (** This is the Pythagoras theorem.
          Pythagoras is tied to the parallel postulate, in the sense
          that we need the parallel postulate to express it.
          Here, we have a statement based on the geometric definition
          of addition and multiplication as predicates. 
      *)

Lemma prop_47 :
     forall O E E' A B C AC BC AB AC2 BC2 AB2 : Tpoint,
       O <> E ->
       Per A C B ->
       Length O E E' A B AB ->
       Length O E E' A C AC ->
       Length O E E' B C BC ->
       Prod O E E' AC AC AC2 ->
       Prod O E E' BC BC BC2 ->
       Prod O E E' AB AB AB2 ->
       Sum O E E' AC2 BC2 AB2.
Proof.
exact pythagoras.
Qed.

	    (** * Proposition 48
       If in a triangle the square on one of the sides be equal to the squares on the remaining two sides of the triangle, the angle contained by the remaining two sides of the triangle is right.
       *)
	    (** # <div style="width:748px;height:397px;display:block" id="applet_container48"></div> # **)


End Book_1_part_5.