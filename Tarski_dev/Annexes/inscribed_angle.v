Require Export GeoCoq.Tarski_dev.Annexes.tangency.
Require Export GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Require Export GeoCoq.Tarski_dev.Annexes.half_angles.



Section Inscribed_angle.

Context `{TE:Tarski_2D_euclidean}.

Lemma sum_two_angles_aux1 : forall A B C B', ~ Col A B C -> B <> B'-> Bet A B B' ->
 exists P, InAngle P B' B C /\ CongA B C A C B P /\ CongA B A C B' B P.
Proof.
intros.
assert_diffs.
assert(HPS:exists P, Par_strict A C B P /\ OS A B P C).
{
  assert(HH := parallel_existence1 A C B H7).
  ex_and HH P.
  assert(Par_strict A C B P).
  {
    unfold Par in H3.
    induction H3.
    assumption.
    spliter.
    apply False_ind.
    apply H.
    ColR.
  }
  assert(TS A B C P \/ OS A B C P).
  {
    apply(one_or_two_sides A B C P).
    Col.
    intro.
    apply H6.
    exists A.
    split; Col.
  }
  induction H8.
  assert(HH:=segment_construction P B B P).
  ex_and HH Q.
  exists Q.
  assert(B <> Q).
  {
    intro.
    treat_equalities.
    unfold Par_strict in H6; tauto.
  }
  assert(Par_strict A C B Q).
  {
    apply(par_strict_col2_par_strict A C B P B Q); Col.
  }
  split; auto.
  assert(TS A B Q P).
  {
    unfold TS.
    repeat split.
    intro.
    apply H12.
    exists A.
    split; Col.
    intro.
    apply H6.
    exists A.
    split; Col.
    exists B.
    split; Col.
    Between.
  }
  apply (l9_8_1 A B Q C P); auto.
  exists P.
  split.
  assumption.
  apply one_side_symmetry; auto.
}
ex_and HPS P.

assert(TS B P A B').
{
  unfold TS.
  repeat split.
  intro.
  apply H3.
  exists A.
  split; Col.
  intro.
  apply H3.
  exists A.
  split; ColR.
  exists B.
  split; Col.
}

assert(TS B P C B').
{
  apply (l9_8_2 B P A); auto.
  apply l12_6.
  Par.
}
unfold TS in H9.
spliter.
ex_and H11 T.
exists T.
split.
unfold InAngle.
repeat split; auto.
intro.
treat_equalities.
apply H; ColR.
exists T.
split.
Between.
right.
apply out_trivial.
intro.
treat_equalities.
apply H; ColR.

assert(B <> T).
{
  intro.
  treat_equalities.
  assert(B <> B').
  {
    intro.
    treat_equalities.
    apply H10; Col.
  }
  apply H.
  ColR.
}
split.
apply conga_comm.
apply(l12_21_a C A B T).
assert(OS C B B' T).
{
  apply out_one_side.
  right.
  intro.
  apply H9.
  ColR.
  unfold Out.
  repeat split.
  intro.
  treat_equalities.
  contradiction.
  intro.
  treat_equalities.
  contradiction.
  right; auto.
}
assert(TS C B B' A).
{
  unfold TS.
  repeat split.
  Col.
  intro.
  apply H.
  ColR.
  Col.
  exists B.
  split; Col.
  Between.
}
apply l9_2.
apply(l9_8_2 C B B' T A); auto.

left.
apply par_strict_left_comm.
apply(par_strict_col_par_strict A C B P T); Col.

assert(CongA T B B' C A B').
{
  apply(l12_22_a B T A C B').
  apply bet_out; Between.
  apply(out_one_side B' B T C).
  right.
  intro.
  apply H.
  ColR.
  unfold Out.
  repeat split.
  intro.
  treat_equalities.
  contradiction.
  intro.
  treat_equalities.
  contradiction.
  left; Between.
  apply par_symmetry.
  apply (par_col_par A C B P T); Col.
  left; auto.
}
apply conga_sym.
apply conga_comm.
apply(l11_10 T B B' C A B' T B' C B); (try (apply out_trivial));auto.
unfold Out.
repeat split; auto.
Qed.


Lemma sum_two_angles_aux2 : forall A B C B', 
  Col A B C -> A <> B -> A <> C -> C <> B -> B <> B'-> Bet A B B' ->
  exists P, InAngle P B' B C /\ CongA B C A C B P /\ CongA B A C B' B P.
Proof.
intros.
induction H.
exists C.
split.
apply l11_24.
apply inangle1123; auto.
split.
apply(out_conga A C A C B C B A C C); try(apply out_trivial; auto).
apply conga_trivial_1; auto.
unfold Out.
repeat split; auto.
right; Between.
apply(out_conga C A C C B C B C B' C); try(apply out_trivial; auto).
apply conga_trivial_1; auto.
unfold Out.
repeat split; auto.
unfold Out.
repeat split; auto.
apply(l5_2 A); auto.

induction H.
exists B'.
split.
apply inangle1123; auto.
split.
apply(conga_line); eBetween.
apply(out_conga C A C B' B B' B C B' B'); try(apply out_trivial; auto).
apply conga_trivial_1; auto.
apply bet_out; Between.

exists C.
split.
apply l11_24.
apply inangle1123; auto.
split.
apply(out_conga B C B C B C B A C C); try(apply out_trivial; auto).
apply conga_trivial_1; auto.
unfold Out.
repeat split; auto.
apply conga_line; eBetween.
Qed.


Lemma sum_two_angles : forall A B C B', A <> B -> A <> C -> C <> B -> B <> B'-> Bet A B B' ->
 exists P, InAngle P B' B C /\ CongA B C A C B P /\ CongA B A C B' B P.
Proof.
intros.
induction(Col_dec A B C).
apply sum_two_angles_aux2; auto.
apply sum_two_angles_aux1; auto.
Qed.


Lemma chord_par_diam : forall O P A B C C' A' U,
 O <> P -> ~Col A B C' -> Diam C C' O P -> Midpoint A' A C' -> OnCircle A O P -> OnCircle B O P ->
 Col A B U -> Perp O U A B -> Par A C' O U -> B = C.
Proof.
intros.
assert_diffs.
assert(Midpoint U A B).
{
  apply(col_onc2_perp__mid O P A B U); Col.
}
assert(O <> A').
intro.
treat_equalities.
induction H7.
apply H7.
exists O.
split; Col.
spliter.
assert(Perp A U  O U).
{
  apply perp_sym in H6.
  apply (perp_col A B O U U); Col.
  intro.
  treat_equalities.
  apply perp_distinct in H6.
  tauto.
}
apply perp_left_comm in H18.
apply perp_not_col in H18.
apply H18; Col.
unfold Diam in H1.
spliter.
assert(HH:=mid_onc2__perp O P A C' A' H15 H13 H3 H17 H2).
assert(Perp O U O A').
{
  apply(par_perp_perp A C' O U O A' H7); Perp.
}

assert(Par O A' A B).
{
  apply (l12_9 _ _ _ _ O U); Perp.
}
assert(HM:=midpoint_existence B C').
ex_and HM O'.
assert(HP:= triangle_mid_par A B C' O' A' H11 H20 H2).
assert(Par O A' A' O').
{
  apply (par_trans _ _ A B); Par.
}
assert(Col O O' A').
{
  induction H21.
  apply False_ind.
  apply H21.
  exists A'.
  split; Col.
  spliter.
  Col.
}

induction(eq_dec_points O O').
treat_equalities.
eapply(symmetric_point_uniqueness C' O); Midpoint.
split; eCong.
Between.

assert(HQ:= mid_onc2__perp O P B C' O' H23  H10 H4 H17 H20).
apply(perp_col O A' A C' O') in HH; Col.
assert(Par A C' B C').
{
  apply(l12_9 A C' B C' O O'); Perp.
}
apply False_ind.
induction H24.
apply H24.
exists C'.
split;Col.
spliter.
apply H0.
Col.
Qed.





Lemma cong_mid2__conga3 : forall O A A' C C',
  O <> C -> A <> C -> Cong O A O C -> Midpoint O C C' -> Midpoint A' A C' ->
   CongA O A C O C A /\ CongA O A C A O A' /\ CongA O C A C' O A'.
Proof.
intros.

assert(A' <> O).
{
  intro.
  treat_equalities; tauto.
}
induction(Col_dec A O C).
assert(HH:= l7_20 O A C H5 H1).
induction HH.
treat_equalities; tauto.
assert(A = C').
{
  apply(symmetric_point_uniqueness C O A C'); Midpoint.
}
subst C'.
assert(A' = A).
apply l7_3;auto.
subst A'.
split.
unfold Midpoint in H2.
apply(l11_21_b).
spliter.
repeat split; auto.
left; Between.
repeat split; auto.
left; Between.
split.
apply (conga_trans _ _ _ O A O).
apply (out_conga O A C O A C O C O O); try(apply out_trivial; auto).
apply conga_refl; auto.
repeat split; auto.
unfold Midpoint in H2.
spliter.
Between.
apply(conga_trivial_1); auto.

apply (conga_trans _ _ _ O C O).
apply (out_conga O C O O C O O A O O); try(apply out_trivial; auto).
apply conga_refl; auto.
repeat split; auto.
unfold Midpoint in H2.
spliter.
Between.
apply(conga_trivial_1); auto.


(********** general case ************)

assert(CongA O A C O C A ).
{
  apply(l11_44_1_a); auto.
}
split; auto.

assert(exists P : Tpoint,
         InAngle P C' O A /\ CongA O A C A O P /\ CongA O C A C' O P).
{
  assert_diffs.
  apply(sum_two_angles C O A C'); Between.
}
ex_and H7 AA.

assert(CongA A' O A A' O C').
{
  assert_diffs.
  apply(cong3_conga A' O A A' O C'); auto.
  repeat split; Cong.
  unfold Midpoint in *.
  spliter.
  eCong.
}

assert(CongA AA O A AA O C').
{
  apply (conga_trans _ _ _ O A C);
  CongA.
  apply (conga_trans _ _ _ O C A);
  CongA.
}


assert(Col O A' AA).
{
  apply(conga2__col A O C' A' AA); CongA.
  intro.
  apply out_col in H12.
  unfold Midpoint in *.
  spliter.
  assert(A = C' \/ Midpoint O A C').
  apply l7_20; eCong; Col.
  induction H15.  
  treat_equalities.
  apply H5; Col.
  assert(A = C).
  apply(symmetric_point_uniqueness C' O); Midpoint.
  split; Between; Cong.
  assert_diffs.
  treat_equalities; tauto.
}

assert(Out O AA A').
{
  assert_diffs.
  apply(col_inangle2__out C' O A AA A');Col.
  intro.
  assert(Midpoint O A C').
  {
    unfold Midpoint in *.
    spliter.
    split; eCong.
    Between.
  }
  assert(A = C).
  apply(symmetric_point_uniqueness C' O); Midpoint.
  treat_equalities; tauto.
  unfold InAngle.
  repeat split; auto.
  exists A'.
  split; Between.
  right.
  apply out_trivial; auto.
}

split.
assert_diffs.
apply(l11_10 O A C A O AA O C A A'); try (apply out_trivial; auto).
auto.
apply l6_6; auto.
assert_diffs.
apply(l11_10 O C A C' O AA O A C' A'); try (apply out_trivial; auto).
auto.
apply l6_6; auto.
Qed.


Lemma inscribed_angle_ts : forall  O P A B C,
   O <> P -> TS O C A B -> OS A B O C ->
   OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
   exists T, InAngle T A O B /\ CongA A O T A C B /\ CongA B O T A C B.
Proof.
intros.
unfold OnCircle in *.
assert(H5: ~Col O A B).
{
  unfold OS in H1.
  ex_and H1 R.
  unfold TS in H1.
  tauto.
}

assert(HH:=symmetric_point_construction C O).
ex_and HH C'.
assert(HH:=midpoint_existence C' A).
ex_and HH A'.
assert(HH:=midpoint_existence C' B).
ex_and HH B'.

assert(~Col A B C').
{
  apply (onc3__ncol O P); Circle.
  intro.
  treat_equalities.
  apply H5; Col.
  intro.
  treat_equalities.
  unfold TS in H0.
  spliter.
  apply H0.
  Col.
  intro.
  treat_equalities.
  unfold TS in H0.
  spliter.
  apply H8.
  Col.
  unfold Midpoint in H6.
  spliter.
  unfold OnCircle.
  eCong.
}

assert(A <> A' /\ B <> B').
{
  split;
  intro;
  treat_equalities;
  apply H9;Col.
}

assert(A <> B /\ A' <> B').
{
  split;
  intro;
  treat_equalities;
  apply H9;Col.
}
spliter.

assert(Par A B A' B').
{
  apply(triangle_mid_par A B C' B' A'); Midpoint.
}
assert(HPS:Par_strict A B A' B').
{
  induction H14.
  assumption.
  spliter.
  unfold Midpoint in *.
  spliter.
  apply False_ind.
  apply H9.
  assert_diffs.
  ColR.
}

assert(HH:=midpoint_existence A B).
ex_and HH U.
assert(Perp O U A B).
{
  apply(mid_onc2__perp O P A B U); Circle.
  intro.
  treat_equalities.
  unfold Midpoint in H15.
  spliter.
  apply H5.
  Col.
}

assert(Perp A' B' O U).
{
  apply(par_perp_perp A B A' B' O U); Perp.
}

assert(HH:= perp_inter_perp_in A' B' O U H17).
ex_and HH T.
exists T.



assert(OnCircle C' O P).
{
  unfold Midpoint in H6; spliter.
  unfold OnCircle; eCong.
}

assert(Per C' A' O).
{
  apply l8_2.
  apply(mid_onc2__per O P C' A A'); Circle.
}
assert(Per C' B' O).
{
  apply l8_2.
  apply(mid_onc2__per O P C' B B'); Circle.
}

assert(O <> T).
{
  intro.
  treat_equalities.
  assert(Par C' A C' B).
  {
    apply(chords_midpoints_col_par O P C' A' A C' B' B H); Circle.
    Col.
    intro.
    assert(A = C' \/ Midpoint O A C').
    apply l7_20; Col.
    eCong.
    induction H24.
    treat_equalities.
    apply H9; Col.
    assert(A = C).
    {
      apply(symmetric_point_uniqueness C' O A C); Midpoint.
    }
    treat_equalities.
    unfold TS in H0.
    spliter.
    apply H0; Col.
    intro.
    assert(B = C' \/ Midpoint O B C').
    apply l7_20; Col.
    eCong.
    induction H24.
    treat_equalities; tauto.
    assert(B' = O).
    {
      apply (l7_17 B C'); Midpoint.
    }
    apply sym_equal in H25.
    treat_equalities.
    unfold TS in H0.
    spliter.
    apply H4; Col.
  }
  unfold Par in H19.
  induction H19.
  apply H19.
  exists C'.
  repeat split; Col.
  spliter.
  apply H9; Col.
}

assert(Perp O T A' B').
{
  apply (perp_col O U A' B' T); Col.
  apply perp_in_perp in H20.
  Perp.
}

assert(TS O C' A B).
{
  assert_diffs.
  eapply(col_preserves_two_sides O C); Col.
}

assert(TS O C' A' B').
{
  apply(l9_8_2 _ _ A).
  apply l9_2.
  apply(l9_8_2 _ _ B).
  apply l9_2.
  assumption.
  apply one_side_symmetry.
  apply invert_one_side.
  apply(out_one_side C' O B' B).
  apply l9_2 in H26.
  assert(HH:= two_sides_not_col O C' B A H26).
  right; Col.
  unfold Midpoint in H8.
  spliter.
  assert_diffs.
  repeat split; auto.
  apply one_side_symmetry.
  apply invert_one_side.
  apply(out_one_side C' O A' A).
  assert(HH:= two_sides_not_col O C' A B H26).
  right; Col.
  unfold Midpoint in H7.
  spliter.
  assert_diffs.
  repeat split; auto.
}

assert(HL:=l13_2 O C' A' B' T H27 H22 H23 H18 H25); spliter.
assert(CongA O A C O C A /\ CongA O A C A O A' /\ CongA O C A C' O A').
{
  assert_diffs.
  apply(cong_mid2__conga3 O A A' C C'); auto.
  eCong.
  Midpoint.
}

assert(CongA O B C O C B /\ CongA O B C B O B' /\ CongA O C B C' O B').
{
  assert_diffs.
  apply(cong_mid2__conga3 O B B' C C'); auto.
  eCong.
  Midpoint.
}

spliter.
assert(OS A B A' T).
{
  apply (l12_6).
  apply(par_strict_col_par_strict A B A' B'); Par.
  intro.
  treat_equalities.
  apply conga_sym in H29.
  apply eq_conga_out in H29.
  apply out_col in H29.
  assert(C' = B' \/ O = B').
  apply(l8_9 C' B' O H23); Col.
  induction H18.
  treat_equalities; tauto.
  assert_diffs.
  treat_equalities; tauto.
}
assert(OS A B A' C').
{
  apply out_one_side.
  right.
  assert_diffs.
  apply (onc3__ncol O P); auto.
  apply bet_out; Between.
}
assert(OS A B C' T).
{
  apply(one_side_transitivity _ _ _ A'); auto.
  apply one_side_symmetry; auto.
}
assert(TS A B O C').
{
  apply(ray_cut_chord O P C C' A B H); Circle.
  unfold Diam.
  repeat split; Circle.
  Between.
  apply(col_preserves_two_sides C' O C C' A B); Col.
  assert_diffs; auto.
  apply invert_two_sides; auto.
  apply one_side_symmetry; auto.
}
assert(TS A B O T).
{
  apply l9_2.
  apply(l9_8_2 A B C' T O);auto.
  apply l9_2;auto.
}

assert(Hout:Out O U T).
{
  induction H19.
  assert_diffs.
  apply bet_out; auto.
  induction H19.
  apply l6_6.
  assert_diffs.
  apply bet_out; Between.
  apply False_ind.

  assert(OS U A O T).
  {
    apply out_one_side.
    left.
    apply perp_sym in H16.
    apply(perp_col A B O U U) in H16.
    apply perp_left_comm in H16.
    apply perp_not_col in H16.
    Col.
    assert_diffs; auto.
    Col.
    apply bet_out; auto.
    assert_diffs; auto.
    Between.
  }
  apply invert_one_side in H42.
  apply (col_one_side A U B O T) in H42; Col.
  apply l9_9 in H41.
  contradiction.
}

split.
unfold InAngle.
assert_diffs.
repeat split; auto.
exists U.
split.
Between.
right.
auto.

assert(HalfA A' A O C').
{
  assert_diffs.
  apply(halfa_chara2 ).
  exists C'.
  exists A'.
  split; eCong.
  split.
  apply out_trivial; auto.
  split.
  Midpoint.
  apply out_trivial; auto.
}

assert(HalfA T A O B).
{
  assert_diffs.
  apply(halfa_chara2 ).
  exists B.
  exists U.
  split; eCong.
  split.
  apply out_trivial; auto.
  split.
  Midpoint.
  auto.
}

assert(LtA A O C' A O B).
{
  unfold LtA.
  split.
  apply(inangle__lea).
  apply(ts2__inangle A O B C'); auto.
  intro.
  assert(Out O C' B \/ TS A O C' B) by (apply (conga__or_out_ts);auto).
  induction H45.
  unfold TS in H26.
  spliter.
  apply H46; Col.
  assert(OS A O C' B).
  {
    apply(in_angle_one_side A O B C').
    Col.
    intro.
    assert(A = C' \/ Midpoint O A C').
    apply l7_20; Col.
    eCong.
    induction H47.
    treat_equalities.
    apply H9; Col.
    assert(C = A).
    apply (symmetric_point_uniqueness C' O); Midpoint.
    treat_equalities.
    unfold TS in H27.
    spliter.
    intuition Col.
    apply(ts2__inangle A O B C'); auto.
  }
  apply l9_9 in H45.
  contradiction.
}

assert(HalfA B' B O C').
{
  assert_diffs.
  apply(halfa_chara2 ).
  exists C'.
  exists B'.
  split; eCong.
  split.
  apply out_trivial; auto.
  split.
  Midpoint.
  apply out_trivial; auto.
}

assert(HalfA T B O A).
{
  assert_diffs.
  apply(halfa_chara2 ).
  exists A.
  exists U.
  split; eCong.
  split.
  apply out_trivial; auto.
  split.
  Midpoint.
  auto.
}

assert(LtA B O C' B O A).
{
  unfold LtA.
  split.
  apply(inangle__lea).
  apply(ts2__inangle B O A C'); auto.
  apply invert_two_sides; auto.
  apply l9_2; auto.
  intro.
  assert(Out O C' A \/ TS B O C' A).
  {
    apply(conga__or_out_ts B O C' A); auto.
  }
  induction H48.
  unfold TS in H26.
  spliter.
  apply H26; Col.
  assert(OS B O C' A).
  {
    apply(in_angle_one_side B O A C').
    Col.
    intro.
    assert(B = C' \/ Midpoint O B C').
    apply l7_20; Col.
    eCong.
    induction H50.
    treat_equalities.
    apply H9; Col.
    assert(C = B).
    apply (symmetric_point_uniqueness C' O); Midpoint.
    treat_equalities.
    unfold TS in H27.
    spliter.
    intuition Col.
    apply(ts2__inangle B O A C').
    apply invert_two_sides; auto.
    apply l9_2.
    apply(col_preserves_two_sides O C O C' A B); Col.
    intro.
    treat_equalities; tauto.
  }
  apply l9_9 in H48.
  contradiction.
}

assert(LtA A O A' A O T).
{
  apply(galfa_preseves_lta A O C' A O B A O A' A O T); auto;
  unfold gHalfA.
  exists A'.
  split; CongA.
  apply conga_refl;
  intro;
  treat_equalities.
  tauto.
  unfold HalfA in H39.
  spliter.
  assert_diffs; tauto.
  exists T.
  split; CongA.
  apply conga_refl; auto.
  intro;
  treat_equalities;
  tauto.
}

assert(LtA B O B' B O T).
{
  apply(galfa_preseves_lta B O C' B O A B O B' B O T); auto;
  unfold gHalfA.
  exists B'.
  split; CongA.
  apply conga_refl;
  intro;
  treat_equalities.
  tauto.
  unfold HalfA in H45.
  spliter.
  assert_diffs; tauto.
  exists T.
  split; CongA.
  apply conga_refl; auto.
  intro;
  treat_equalities;
  tauto.
}


assert(InAngle C' A O B).
{
  apply(ts2__inangle A O B C'); auto.
}
assert(InAngle A' A O B).
{
  apply (in_angle_trans _ _ _ C'); auto.
  unfold InAngle.
  assert_diffs.
  unfold Midpoint in H7.
  spliter.
  repeat split; auto.
  exists A'.
  split; Between.
  right.
  apply out_trivial; auto.
}
assert(InAngle T A O B).
{
  assert_diffs.
  repeat split;auto.
  exists U.
  unfold Midpoint in H15; spliter.
  split; auto.
}

assert(OS A O A' T).
{
  apply(inangle_one_side _ _ B); Col.
  intro.
  unfold Midpoint in *.
  spliter.
  unfold TS in H0.
  spliter.
  apply H0.
  ColR.
  intro.
  apply perp_sym in H16.
  apply (perp_col _ _ _ _ U) in H16.
  apply perp_left_comm in H16.
  apply perp_not_col in H16.
  assert(Col A O U)by ColR.
  apply H16; Col.
  intro.
  treat_equalities; tauto.
  Col.
}

apply invert_one_side in H53.
apply one_side_symmetry in H53.

assert(TS O A' A T).
{
  apply(lta_os__ts A O T A'); auto.
  apply(halfa_not_null _ _ _ C'); auto.
  unfold TS in H0.
  spliter.
  intro.
  apply H0.
  ColR.
}

assert(CongA A O T A C B).
{
  apply(l11_22a A O T A' A C B O).
  split; auto.
  split.
  apply invert_two_sides; auto.
  split.
  apply(conga_trans _ _ _ O A C); CongA.
  apply(conga_trans _ _ _ C' O B'); CongA.
}

split; auto.
unfold HalfA in H43.
spliter.
apply(conga_trans _ _ _ A O T); CongA.
Qed.



Lemma inscribed_angle_os : forall  O P A B C, O <> P ->
 TS O B A C -> OS O C A B -> OS A B O C -> OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
 exists T, InAngle T A O B /\ CongA A O T A C B /\ CongA B O T A C B.
Proof.
intros O P A B C H h.
intros.
unfold OnCircle in *.
assert(H5: ~Col O A B).
{
  unfold OS in H1.
  ex_and H1 R.
  unfold TS in H1.
  tauto.
}

assert(HH:=symmetric_point_construction C O).
ex_and HH C'.
assert(HH:=midpoint_existence C' A).
ex_and HH A'.
assert(HH:=midpoint_existence C' B).
ex_and HH B'.

assert(~Col A B C').
{
  unfold OS in H0.
  ex_and H0 R.
  unfold TS in H0.
  spliter.
  apply (onc3__ncol O P); Circle.
  intro.
  treat_equalities.
  apply H5; Col.
  intro.
  treat_equalities.
  apply H0.
  Col.
  intro.
  treat_equalities.
  unfold TS in H9.
  spliter. 
  apply H8.
  Col.
  unfold Midpoint in H6.
  spliter.
  unfold OnCircle.
  eCong.
}

assert(A <> A' /\ B <> B').
{
  split;
  intro;
  treat_equalities;
  apply H9;Col.
}

assert(A <> B /\ A' <> B').
{
  split;
  intro;
  treat_equalities;
  apply H9;Col.
}
spliter.

assert(HH:=midpoint_existence A B).
ex_and HH U.

assert(Par C' B A' U).
{
  apply(triangle_mid_par C' B A U A'); Midpoint.
  intro.
  treat_equalities; tauto.
}

assert(HPS:Par_strict C' B A' U).
{
  induction H15.
  assumption.
  spliter.
  unfold Midpoint in *.
  spliter.
  apply False_ind.
  apply H9.
  assert_diffs.
  ColR.
}


assert(OnCircle C' O P).
{
  unfold Midpoint in H6; spliter.
  unfold OnCircle; eCong.
}

assert(Perp O B' C' B).
{
  assert_diffs.
  apply(mid_onc2__perp O P C' B B'); Circle.
  intro.
  treat_equalities; tauto.
}

assert(Perp A' U O B').
{
  apply(par_perp_perp C' B A' U O B'); Perp.
}

assert(HH:= perp_inter_perp_in A' U O B' H18).
ex_and HH T.
exists U.

assert(Per A A' O).
{
  apply l8_2.
  apply(mid_onc2__per O P A C' A'); Circle.
  Midpoint.
}


assert(Per A U O).
{
  apply l8_2.
  apply(mid_onc2__per O P A B U); Circle.
}
assert(O <> T).
{
  intro.
  treat_equalities.
  assert(Par A C' A B).
  {
    apply l7_2 in H7.
    apply(chords_midpoints_col_par O P A A' C' A U B H); Circle.
    Col.
    intro.
    assert(A = C' \/ Midpoint O A C').
    apply l7_20; Col.
    eCong.
    induction H24.
    treat_equalities.
    apply H9; Col.
    assert(A = C).
    {
      apply(symmetric_point_uniqueness C' O A C); Midpoint.
    }
    treat_equalities.
    unfold OS in H0.
    ex_and H0 R.

    unfold TS in H0.
    spliter.
    apply H0; Col.
  }
  unfold Par in H20.
  induction H20.
  apply H20.
  exists A.
  repeat split; Col.
  spliter.
  apply H9; Col.
}

assert(Perp O T A' U).
{
  apply (perp_col O B' A' U T); Col.
  apply perp_in_perp in H21.
  Perp.
}

assert(OS A O U B).
{
  apply out_one_side;Col.
  repeat split; auto.
  intro.
  treat_equalities.
  unfold Midpoint in H14.
  spliter.
  apply H5; Col.
  left.
  unfold Midpoint in H14.
  tauto.
}

assert(OS A O A' C').
{
  apply out_one_side;Col.
  left.
  assert(Diam A C' O P \/ ~ Col O A A' /\ ~ Col O C' A').
  apply(mid_chord__diam_or_ncol O P A C' A'); Circle.
  intro.
  treat_equalities; auto.
  apply l7_2; auto;
  repeat split; auto.
  induction H27.
  apply diam__midpoint in H27.
  assert(A' = O).
  {
    apply(l7_17 A C');
    Midpoint.
  }
  treat_equalities.
  assert(hh:= not_two_sides_id A A' B).
  contradiction.
  spliter.
  Col.
  repeat split; auto.
  intro.
  treat_equalities; tauto.
  unfold Midpoint in H7.
  spliter.
  left; Between.
}



assert(OS O A B C).
{
  apply one_side_symmetry.
  apply(os_ts1324__os O C B A).
  apply one_side_symmetry; auto.
  apply l9_2; auto.
}

assert(HN1:~Col O A C).
{
  intro.
  assert(Diam C A O P).
  {
    apply(center_col__diam O P C A); Circle.
    intro.
    treat_equalities.
    assert(hh:= not_two_sides_id C A' B).
    contradiction.
    Col.
  }
  assert(Diam C C' O P).
  {
    repeat split; Circle.
    unfold Midpoint in H6.
    spliter; Between.
  }
  assert(HH:= diam_end_uniqueness O P C A C' H30 H31).
  treat_equalities; tauto.
}

assert(HN2:~Col O A C').
{
  intro.
  assert(Diam C' A O P).
  {
    apply(center_col__diam O P C' A); Circle.
    intro.
    treat_equalities; tauto.
    Col.
  }
  assert(Diam C' C O P).
  {
    repeat split; Circle.
    unfold Midpoint in H6.
    spliter; Between.
  }
  assert(HH:= diam_end_uniqueness O P C' A C H30 H31).
  treat_equalities.
  assert(hh:= not_two_sides_id A A' B) || 
  assert(hh:= not_two_sides_id A O B). 
  contradiction.
}

assert(HN3:~Col O B C).
{
  intro.
  assert(Diam C B O P).
  {
    apply(center_col__diam O P C B); Circle.
    intro.
    treat_equalities.
    apply perp_distinct in H18.
    tauto.
    assert(hh:= not_two_sides_id C A' C).
    Col.
  }
  assert(Diam C C' O P).
  {
    repeat split; Circle.
    unfold Midpoint in H6.
    spliter; Between.
  }
  assert(HH:= diam_end_uniqueness O P C B C' H30 H31).
  treat_equalities; tauto.
}

assert(TS O A B C').
{
  apply (l9_8_2 _ _ C).
  unfold TS.
  repeat split; Col.
  exists O.
  split; Col.
  unfold Midpoint in H6.
  spliter.
  Between.
  apply one_side_symmetry; auto.
}


assert(TS O A A' U).
{
  apply(l9_8_2 _ _ C').
  apply l9_2.
  eapply (l9_8_2 _ _ B);auto.
  apply one_side_symmetry; auto.
  apply invert_one_side; auto.
  apply invert_one_side.
  apply one_side_symmetry; auto.
}

assert(HT:=l13_2 O A A' U T H30 H22 H23 H19 H25).
spliter.


assert(U <> O).
{
  intro.
  treat_equalities.
  unfold TS in H30.
  spliter.
  apply H34; Col.
}

assert(Perp A B O U).
{
  apply perp_sym.
  apply(mid_onc2__perp O P A B U);auto.
}


split.

repeat split; auto.
intro.
treat_equalities; tauto.
intro.
treat_equalities; tauto.
exists U.
split.
Between.
right.
apply out_trivial; auto.

assert(CongA A O U B O U).
{
  apply(cong_perp_conga); auto.
  eCong.
}

assert(CongA O A C O C A /\ CongA O A C A O A' /\ CongA O C A C' O A').
{
  assert_diffs.
  apply(cong_mid2__conga3 O A A' C C'); auto.
  eCong.
  Midpoint.
}

assert(CongA O B C O C B /\ CongA O B C B O B' /\ CongA O C B C' O B').
{
  assert_diffs.
  apply(cong_mid2__conga3 O B B' C C'); auto.
  eCong.
  Midpoint.
}

spliter.
assert(InAngle A C' O B).
{
  unfold InAngle.
  assert_diffs.
  repeat split; auto.
  unfold TS in H29.
  spliter.
  ex_and H66 X.
  exists X.

  assert(OS O C X B).
  {
    apply(col_one_side O C' C X B);
    Col.
    apply invert_one_side.
    apply out_one_side.
    right.
    intro.
    apply HN3.
    ColR.
    repeat split; auto.
    intro.
    treat_equalities.
    apply HN2.
    Col.
    left; Between.
  }
  split.
  Between.
  right.

  apply (col_one_side_out O C X A).
  Col.
  apply (one_side_transitivity _ _ _ B); auto.
  apply one_side_symmetry; auto.
}

assert(~Col C' O B).
{
  intro.
  unfold Midpoint in H6.
  spliter.
  apply HN3.
  assert_diffs.
  ColR.
}

assert(OS C' O A' A).
{
  apply out_one_side.
  right; Col.
  unfold Midpoint in H7.
  spliter.
  unfold Out.
  repeat split; auto.
  intro.
  treat_equalities.
  apply H9; Col.
  intro.
  treat_equalities.
  apply H9; Col.
}

assert(OS C' O B' B).
{
  apply out_one_side.
  right; Col.
  unfold Midpoint in H8.
  spliter.
  unfold Out.
  repeat split; auto.
  intro.
  treat_equalities.
  apply H9; Col.
  intro.
  treat_equalities.
  apply H9; Col.
}

assert(OS C' O A U).
{
  apply (l9_17 _ _ B).
  apply invert_one_side.
  eapply (col_one_side _ C); Col.
  intro.
  treat_equalities.
  intuition Col.
  unfold Midpoint in H14.
  tauto.
}

assert(OS C' O A' B').
{
  apply (one_side_transitivity _ _ _ A); auto.
  apply (one_side_transitivity _ _ _ B); auto.
  apply invert_one_side.
  eapply (col_one_side _ C); Col.
  intro; treat_equalities.
  intuition Col.
  apply one_side_symmetry.
  auto.
}

assert(OS C' O A' U).
{
  apply (one_side_transitivity _ _ _ A); auto.
}
assert(OS C' O A' T).
{
  apply (l9_17 _ _ U); auto.
}
assert(OS C' O B' T).
{
  apply (one_side_transitivity _ _ _ B); auto.
  apply (one_side_transitivity _ _ _ A); auto.
  apply invert_one_side.
  eapply (col_one_side _ C); Col.
  intro; treat_equalities.
  intuition Col.
  apply one_side_symmetry.
  auto.
  apply (one_side_transitivity _ _ _ A'); auto.
  apply one_side_symmetry.
  auto.
}

assert(Out O B' T).
{
  assert(HH:= l9_19 C' O B' T O).
  destruct HH; Col.
  intro; treat_equalities.
  intuition Col.
  apply H52 in H51.
  tauto.
}


assert(InAngle U T O B).
{
  apply(inangle_halfa_inangle O C' B A T U); auto.
  unfold HalfA.
  split.
  intro.
  apply H44; Col.
  split.
  unfold InAngle.
  assert_diffs.
  repeat split; auto.
  exists B'.
  unfold Midpoint in H8.
  spliter.
  split; auto.
  apply (out_conga C' O B' B O B' C' T B T);
  try(apply out_trivial; auto); auto.
  apply (conga_trans _ _ _ O B C); CongA.
  apply (conga_trans _ _ _ O C B); CongA.
  intro; treat_equalities; tauto.
  intro; treat_equalities; tauto.
  apply halfa_chara2.
  exists B.
  exists U.
  split; eCong.
  split.
  apply out_trivial; auto.
  intro; treat_equalities.
  tauto.
  split; auto.
  apply out_trivial; auto.
}

assert(Perp T O A' T).
{
  apply perp_left_comm.
  apply (perp_col _ B'); auto.
  apply perp_sym.
  apply (perp_col _ U); auto.
  intro.
  apply sym_equal in H54.
  treat_equalities.
  
  apply conga_sym in H32.
  apply(eq_conga_out) in H32.
  assert(Col O U A) by Col.
  apply per_not_col in H23; auto.
  apply H23; Col.
  intro.
  treat_equalities.
  apply perp_distinct in H35.
  tauto.
}

assert(T <> U).
{
  intro.
  treat_equalities.
  apply conga_sym in H31.
  apply(eq_conga_out) in H31.
  unfold OS in H27.
  ex_and H27 R.
  unfold TS in H30.
  spliter.
  apply H30; Col.
}
assert(~Col O T U).
{
  apply per_not_col ; auto.
  apply perp_sym in H54.
  apply perp_comm in H54.
  apply (perp_col _ _ _ _ U) in H54; auto.
  apply perp_perp_in in H54.
  apply perp_in_comm in H54.
  apply perp_in_per in H54.
  apply l8_2; auto.
  Col.
}


assert(CongA B O U A C B).
{
  apply conga_left_comm.
  apply (l11_22b U O B T A C B O).
  split.
  apply invert_one_side.
  apply in_angle_one_side; auto.
  intro.
  assert(Col B O B').
  ColR.
  apply H44; ColR.
  split.
  apply invert_one_side; auto.
  split.
  apply(conga_trans _ _ _ A O A'); CongA.
  apply(conga_trans _ _ _ O A C); CongA.

  apply conga_sym.
  apply(conga_trans _ _ _ B' O B); CongA.
  apply(conga_trans _ _ _ O B C); CongA.
  assert_diffs.
  apply (out_conga B' O B B' O B B' B T B);auto;
  try(apply out_trivial; auto). 
  apply conga_refl; auto.
}
split.
apply(conga_trans A O U B O U); CongA.
auto.
Qed.

Lemma inscribed_angle_col : forall  O P A B C,
 Col A O C -> O <> P -> OS A B O C -> OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
 exists T, InAngle T A O B /\ CongA A O T A C B /\ CongA B O T A C B.
Proof.
intros.
unfold OnCircle in *.
assert(A = C \/ Midpoint O A C).
apply l7_20; Col.
eCong.

induction H5.
treat_equalities.
unfold OS in H0.
ex_and H1 R.
unfold TS in H1.
spliter.
apply False_ind.
apply H1; Col.

assert(HH:=midpoint_existence A B).
ex_and HH T.
exists T.
assert_diffs.
assert(O <> T).
{
  intro.
  treat_equalities;tauto.
}
split.
unfold InAngle.
repeat split; auto.
exists T.
split.
Between.
right.
apply out_trivial; auto.
assert(HN: ~Col O A B).
{
  intro.
  unfold OS in H0.
  ex_and H1 R.
  unfold TS in H1.
  spliter.
  contradiction.
}

assert(CongA O B C O C B /\ CongA O B C B O T /\ CongA O C B A O T).
{
  assert_diffs.
  apply(cong_mid2__conga3 O B T C A); Midpoint.
  eCong.
}
spliter.

assert(CongA A C B O C B).
{
  apply(out_conga O C B O C B A B O B);try (apply out_trivial; auto).
  apply conga_refl; auto.
  unfold Midpoint  in H5.
  spliter.
  unfold Out.
  repeat split; auto.
  left; Between.
}


split.
apply(conga_trans _ _ _ O C B); CongA.
apply(conga_trans _ _ _ O B C); CongA.
apply(conga_trans _ _ _ O C B); CongA.
Qed.

Lemma inscribed_angleg_aux : forall  O P A B C,
  O <> P -> OS A B O C ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
 exists T, InAngle T A O B /\ CongA A O T A C B /\ CongA B O T A C B.
Proof.
intros.
induction(Col_dec A O C).
apply (inscribed_angle_col O P);auto.
induction(Col_dec B O C).
assert(exists T : Tpoint,
       InAngle T B O A /\ CongA B O T B C A /\ CongA A O T B C A).
{
  apply(inscribed_angle_col O P B A C H5 H);auto.
  apply invert_one_side; auto.
}
ex_and H6 T.
exists T.
split.
apply l11_24; auto.
split; CongA.

(******** general case **********)
assert(HH:=one_or_two_sides O C A B H4 H5).
induction HH.

(* case TS O C A B *)


apply(inscribed_angle_ts O P); auto.
assert(TS O A C B \/ TS O B C A).
{
  apply(two_sides_cases O C A B);auto.
  unfold OS in H0.
  ex_and H0 R.
  unfold TS in H0.
  spliter.
  Col.
}

induction H7.

assert(exists T : Tpoint,
       InAngle T B O A /\ CongA B O T B C A /\ CongA A O T B C A).
{
  apply(inscribed_angle_os O P B A C); auto.
  apply l9_2; auto.
  apply one_side_symmetry; auto.
  apply invert_one_side; auto.
}
ex_and H8 T.
exists T.
split.
apply l11_24;auto.
split; CongA.
apply l9_2 in H7.
apply(inscribed_angle_os O P); auto.
Qed.

Lemma inscribed_angleg : forall O P A B C,
  O <> P -> OS A B O C -> OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
  gHalfA A C B A O B.
Proof.
intros.
unfold gHalfA.
assert(HH:=inscribed_angleg_aux O P A B C H H0 H1 H2 H3).
ex_and HH T.
exists T.
split; CongA.
unfold HalfA.
split.
intro.
unfold OS in H0.
ex_and H0 R.
unfold TS in H0.
spliter.
apply H0.
Col.
split; auto.
apply (conga_trans _ _ _ A C B); CongA.
Qed.

End Inscribed_angle.
