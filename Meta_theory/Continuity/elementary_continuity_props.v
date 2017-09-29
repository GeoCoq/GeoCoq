Require Export GeoCoq.Axioms.continuity_axioms.
Require Export GeoCoq.Tarski_dev.Annexes.circles.

Section Elementary_Continuity_Props.

Context `{TE:Tarski_2D}.

(**    All these properties are known to be equivalent in an arbitrary Hilbert plane
  (Tarski_2D) as shown by Strommer,
  but we don't have formalized the proof yet.

  We have the following proofs:
  - three equivalent variants of the circle-circle continuity axiom;
  - three equivalent variants of the line-circle continuity axiom;
  - the implication from the circle-circle continuity axiom to the line-circle continuity axiom.

  Since we have proved the circle-circle continuity axiom to follow from Tarski's axiom of continuity, all these properties do.
*)

Lemma segment_circle__one_point_line_circle : segment_circle <-> one_point_line_circle.
Proof.
  unfold segment_circle, one_point_line_circle.
  split.
  - intros Hsc A B U V P HCol HUV HBet.
    destruct (eq_dec_points A B).
      unfold InCircle, OnCircle in *.
      treat_equalities.
      exists A; Cong.
    assert (HPIn : InCircle P A B) by (apply bet__le1213; assumption).
    destruct (diff_col_ex3 U V P) as [W [HUW [HVW [HPW HCol2]]]]; trivial.
    destruct (eq_dec_points A P).
    { subst P.
      destruct (segment_construction W A A B) as [Q [HQ1 HQ2]].
      destruct (Hsc A B A Q) as [Z [HZ1 HZ2]]; trivial.
        apply cong__le; Cong.
      exists Z; split; trivial.
      ColR.
    }
    destruct (segment_construction W P P A) as [Q0 [HQ01 HQ02]].
    destruct (segment_construction P Q0 A B) as [Q [HQ1 HQ2]].
    destruct (Hsc A B P Q) as [Z [HZ1 HZ2]]; trivial.
      apply (l5_6 Q Q0 Q A); Cong.
      apply (triangle_reverse_inequality P); Cong.
      assert_diffs.
      apply l6_6, bet_out; auto.
    exists Z; split; trivial.
    ColR.

  - intros Hoplc A B P Q HPIn HQOut.
    destruct (eq_dec_points A B).
      unfold InCircle in HPIn; treat_equalities.
      exists A; split; Between; Circle.
    destruct (eq_dec_points P Q).
      subst Q; exists P; split; Between; Circle.
    destruct (Cong_dec A B A Q) as [HCong|HNCong].
      exists Q; split; Between; Circle.
    assert (HB' : exists B', Cong A B A B' /\ Bet A P B').
    { destruct (eq_dec_points A P).
        subst; exists B; split; Cong; Between.
      destruct (l6_11_existence A A B P) as [B' [HOut HCong]]; auto.
      exists B'; split; Cong.
      apply l6_13_1.
        apply l6_6, HOut.
      apply (l5_6 A P A B); Cong.
    }
    destruct HB' as [B' [HCong HBet]].
    destruct (Hoplc A B' P Q P) as [Z1 [HCol1 HZ1]]; Col.
    assert (HZ1On: OnCircle Z1 A B) by (apply cong_transitivity with A B'; Cong).
    clear dependent B'.
    destruct (or_bet_out P Z1 Q) as [HBet|[HOut|HNCol]];
      [exists Z1; auto| |exfalso; apply HNCol; Col].
    destruct (chord_completion A B Z1 P) as [Z2 [HZ2On HBet]]; trivial.
    exists Z2; split; trivial.
    assert_diffs.
    assert (HBet2 : Bet Z1 Z2 Q).
    { apply out2__bet.
        apply l6_7 with P; trivial.
        apply l6_6, bet_out; auto.
      apply (col_inc2_outcs__out A B); Circle.
        ColR.
      split; trivial.
    }
    eBetween.
Qed.

Lemma one_point_line_circle__two_points_line_circle :
  one_point_line_circle <-> two_points_line_circle.
Proof.
  unfold one_point_line_circle, two_points_line_circle.
  split.
  - intros Hoplc A B U V P HCol HUV HBet.
    destruct (eq_dec_points P B) as [Heq|HPB].
      subst P; exists B, B; repeat split; Circle; Between.
    destruct (Hoplc A B U V P HCol HUV HBet) as [Z1 [HZ1Col HZ1On]].
    exists Z1.
    assert (HPIn : InCircle P A B) by (apply bet__le1213, HBet).
    destruct (chord_completion A B Z1 P) as [Z2 [HZ2On HPBet]]; trivial.
    assert (Z1 <> P).
      intro; treat_equalities; apply HPB, between_cong with A; trivial.
    assert_diffs.
    exists Z2; repeat (split; trivial); ColR.

  - intros Htplc A B U V P HCol HUV HBet.
    destruct (Htplc A B U V P HCol HUV HBet) as [Z [_ [HZ1 [HZ2 _]]]].
    exists Z; auto.
Qed.

Lemma circle_circle__circle_circle_bis : circle_circle -> circle_circle_bis.
Proof.
  intros Hcc A B C D P Q HPOn HPIn HQOn HQIn.
  destruct (eq_dec_points P Q).
    subst Q; exists P; split; assumption.
  destruct (chord_completion C D P Q) as [P' [HP'On HBetQ]]; trivial.
  destruct (chord_completion A B Q P) as [Q' [HQ'On HBetP]]; trivial.
  apply (Hcc A B C D P P'); trivial.
  destruct (le_cases A P' A B); trivial.
  assert (P' = Q).
  { apply between_equality with Q'.
      eBetween.
    assert_diffs.
    apply (col_inc_onc2__bet A B); trivial; ColR.
  }
  subst.
  apply cong__le; Cong.
Qed.

Lemma circle_circle_bis__one_point_line_circle :
  circle_circle_bis -> one_point_line_circle.
Proof.
  unfold circle_circle_bis, one_point_line_circle.
  intros Hcc A B U V P HCol HUV HBet.
  destruct (Col_dec U V B) as [|HNCol].
    exists B; split; Circle.
  destruct (eq_dec_points A P).
    subst P.
    destruct (diff_col_ex3 U V A) as [W [HUW [HVW [HPW HCol2]]]]; trivial.
    destruct (segment_construction W A A B) as [Z [HZ1 HZ2]].
    exists Z; split; trivial; ColR.
  destruct (l10_6_existence U V A) as [C HC].
  destruct (l10_6_existence U V B) as [D HD].
  assert (HBet' : Bet C P D).
    apply image_gen_preserves_bet with A P B U V; trivial.
    left; split; trivial.
    apply image_col, HCol.
  assert (HCong : Cong B P D P) by (apply (is_image_col_cong U V); assumption).
  assert (HDIn : InCircle D A B).
    apply triangle_inequality with P; Cong.
  assert (HBIn : InCircle B C D).
    apply triangle_inequality with P; Cong.
  destruct (Hcc A B C D D B) as [Z [HZ1 HZ2]]; Circle.
  exists Z; split; trivial.
  apply image_cong_col with A C; trivial.
    intro; treat_equalities.
    assert (Col A U V) by (apply l10_8, HC).
    apply HNCol; ColR.
  apply cong_transitivity with A B; trivial.
  apply cong_transitivity with C D; Cong.
  apply cong_symmetry, l10_10 with U V; assumption.
Qed.

Lemma circle_circle__circle_circle_two :
 circle_circle <-> circle_circle_two.
Proof.
  unfold circle_circle, circle_circle_two.
  split.
  { intros Hcc A B C D P Q.
    intros.
    destruct (eq_dec_points A C).
    subst C.
      exists P; exists P.
      assert (Cong A B A D).
        apply le_anti_symmetry.
        apply (l5_6 A B A Q); Cong.
        apply (l5_6 A P A B); Cong.
      assert (Cong A P A B) by (apply cong_transitivity with A D; Cong).
      repeat split; trivial.
      intro Habs.
      destruct Habs.
      contradiction.
    destruct (Hcc A B C D P Q) as [Z1 [HZ1A HZ1B]]; trivial.
    exists Z1.
    destruct (l10_6_existence A C Z1) as [Z2 HZ2].
    exists Z2.
    assert (Cong Z1 C Z2 C) by (apply (is_image_col_cong A C Z1 Z2 C); Col).
    assert (Cong Z1 A Z2 A) by (apply (is_image_col_cong A C Z1 Z2 A); Col).
    repeat split; trivial.
      unfold OnCircle in *; eCong.
      unfold OnCircle in *; eCong.
    intros.
    intro; subst Z2.
    clean.
    destruct (or_bet_out A C Z1) as [HBet|[HOut|HNCol]].
    - apply (lt__nle A B A Q); trivial.
      apply l5_6 with A Q A Z1; Cong.
      apply triangle_inequality with C; trivial.
      apply cong_transitivity with C D; Cong.
    - apply (lt__nle A P A B); trivial.
      apply l5_6 with A Z1 A P; Cong.
      apply triangle_reverse_inequality with C; trivial.
      apply cong_transitivity with C D; Cong.
    - assert (HCol := l10_8 A C Z1 HZ2); Col.
  }
  intros Hcct A B C D P Q.
  intros.
  destruct (Hcct A B C D P Q) as [Z1 [Z2 [HZ1On [HZ1On' _]]]]; trivial.
  exists Z1; auto.
Qed.


Lemma circle_circle_bis__circle_circle :
 circle_circle_bis -> circle_circle.
Proof.
intros.
unfold circle_circle.
intros.
assert (SC:segment_circle).
 {
 assert (T:= circle_circle_bis__one_point_line_circle).
 assert (U:= segment_circle__one_point_line_circle).
 tauto.
 }
unfold segment_circle in *.
destruct (SC  A B P Q H2 H3) as [X [HX1 HX2]].
assert (InCircle X C D) by (apply (bet_inc2__inc C D P Q X);auto using onc__inc).
unfold circle_circle_bis in *.
apply (H A B C D P X);try assumption.
Qed.

Lemma equilateral_triangle_bis :
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

End Elementary_Continuity_Props.
