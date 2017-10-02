Require Export GeoCoq.Tarski_dev.Ch12_parallel.


Section HalfAngle.

Context `{TE:Tarski_2D}.


Definition HalfA P A O B := ~ Bet A O B /\ InAngle P A O B /\ CongA A O P B O P.

Lemma halfa_exists : forall A O B, ~Col A O B -> exists P, HalfA P A O B.
Proof.
intros.
assert_diffs.
assert(exists X : Tpoint, (Bet O B X \/ Bet O X B) /\ Cong O X O A).
{
  apply(segment_construction_2 B O O A); auto.
}
ex_and H0 A'.
assert(Out O B A').
unfold Out.
repeat split; auto.
intro.
treat_equalities.
tauto.

assert(HM:=midpoint_existence A A').
ex_and HM P.
assert(P<> O).
{
  intro.
  apply H.
  ColR.
}
exists P.
unfold HalfA.
split.
intro; ColR.
split.
unfold InAngle.
repeat split; auto.

induction H0.
assert(exists X : Tpoint, Bet P X O /\ Bet B X A).
{
  apply(inner_pasch A O A' P B); auto.
  unfold Midpoint in H6.
  spliter.
  auto.
}
ex_and H8 P'.
exists P'.
split; Between.
right.
unfold Out.
repeat split; auto.
intro.
treat_equalities; ColR.
left; Between.
assert(exists X : Tpoint, Bet B X A /\ Bet O P X).
{
  apply(outer_pasch B A A' O P); Between.
}
ex_and H8 P'.
exists P'.
split; Between.
right.
unfold Out.
repeat split; auto.
try intro; treat_equalities.
Col.

apply(l11_10 A O P A' O P A P B P); try(auto; apply out_trivial; auto).
apply(cong3_conga); auto.
repeat split;  Cong.
Qed.

Lemma halfa_sym : forall A O B P, HalfA P A O B -> HalfA P B O A.
Proof.
intros.
unfold HalfA in *.
spliter.
split.
intro. Between.
split.
apply l11_24; auto.
apply conga_sym; auto.
Qed.

Lemma halfa_nbet : forall A O B P, HalfA P A O B -> ~ Bet A O P.
Proof.
intros.
unfold HalfA in *.
spliter.
intro.
unfold InAngle in *.
spliter.
ex_and H5 X.
induction H6.
treat_equalities.
contradiction.
induction H6.
spliter.
induction H8.
assert(Bet A O X).
{
  apply(between_inner_transitivity _ _ _ P); auto.
}
apply H.
apply between_symmetry.
apply(between_exchange2 B X O A); Between.

assert(Bet A O X).
{
  apply(outer_transitivity_between A O P X);auto.
}
apply H.
apply(between_exchange4 A O X B); auto.
Qed.

Lemma halfA_nbet2 : forall A O B P, HalfA P A O B -> ~Bet A O P /\ ~Bet B O P.
Proof.
intros.
split.
apply (halfa_nbet A O B P); auto.
apply halfa_sym in H.
apply (halfa_nbet B O A P); auto.
Qed.


Lemma halfa_chara1 : forall P A O B, HalfA P A O B -> 
 exists A', exists M, Cong O A' O A /\ Out O A' B /\ Midpoint M A A' /\ Out O M P.
Proof.
intros.
assert(HA:=H).
unfold HalfA in H.
spliter.
induction(Col_dec  O A B).
exists A.
exists A.
split; Cong.
assert_diffs.
assert(Out O A B).
assert(HH:= or_bet_out A O B).
induction HH.
contradiction.
induction H6.
assumption.
apply False_ind.
apply H6.
Col.
split.
auto.
split; Midpoint.
apply(in_angle_out A O B P); auto.

assert_diffs.
assert(exists X : Tpoint, (Bet O B X \/ Bet O X B) /\ Cong O X O A).
{
  apply(segment_construction_2 B O O A); auto.
}
ex_and H4 A'.
exists A'.
assert(Out O B A').
unfold Out.
repeat split; auto.
intro.
treat_equalities.
Col.
assert(HM:=midpoint_existence A A').
ex_and HM M.
exists M.
unfold Midpoint in *; spliter.
repeat split; auto.
intro.
apply sym_equal in H12.
treat_equalities.
Col.
tauto.

intro.
apply sym_equal in H12.
treat_equalities.
apply H2.
ColR.

assert(HH:=segment_construction_2 P O O M H3).
ex_and HH M'.

assert(Out O P M').
{
  repeat split; auto.
  intro.
  apply H2.
  ColR.
}

assert(CongA A O M' A' O M').
{
  apply (out_conga A O P B O P A M' A' M');auto; try(apply out_trivial; auto).
}
assert(Cong A M' A' M').
{
  apply(cong2_conga_cong A O M' A' O M'); Cong.
}

induction(eq_dec_points M M').
subst M'.
tauto.

assert(Per M' M A).
unfold Per.
exists A'.
split; Cong.
split; auto.


assert(Col M' O M).
{
  apply(per_per_col M' O A M); auto.
  intro; treat_equalities.
  apply H2; ColR.
  unfold Per.
  exists A'.
  split; Cong.
  split; auto.
}
induction(eq_dec_points P M).
subst M.
left; Between.

assert(O <> M').
{
  intro.
  treat_equalities; tauto.
}
assert(Col O M P).
{
  induction H12;
  ColR.
}

assert(Out O P M).
{
  apply(col_inangle2__out A O A' P M).
  intro.
  apply H2.
  ColR.
  apply(l11_25 P A O B A A' P); auto; try(apply out_trivial; auto).
  apply l6_6; auto.
  unfold InAngle.
  repeat split; auto.
  intro; treat_equalities; tauto.
  intro; treat_equalities; tauto.
  exists M.
  split; auto.
  right.
  apply out_trivial.
  intro; treat_equalities; tauto.
  Col.
}
unfold Out in H23.
spliter.
tauto.
Qed.

Lemma halfa_chara2 : forall P A O B, (exists A', exists M, Cong O A' O A /\ Out O A' B /\ Midpoint M A A' /\ Out O M P) -> HalfA P A O B.
Proof.
intros.
ex_and H A'.
ex_and H0 M.
unfold HalfA.
assert_diffs.

assert(~Bet A O B).
induction(Col_dec A O B).

assert(Col O A A').
ColR.
assert(A = A' \/ Midpoint O A A').
apply l7_20; Col.
Cong.
induction H10.
treat_equalities.
induction H0.
spliter.
intro.
induction H1.
apply H4.

apply (between_equality _ _ B); Between.
apply H7.
apply (between_equality _ _ M); Between.
intro.
apply H4.
apply (l7_17 A A'); Midpoint.
intro.
Col.
split.
assumption.
split.
unfold InAngle.
repeat split; auto.
induction(Col_dec O A B).
assert(A = A').
{
  apply(l6_11_uniqueness O O A B A A'); auto.
  assert(HH:= or_bet_out A O B).
  induction HH.
  contradiction.
  induction H10.
  assumption.
  apply False_ind.
  apply H10.
  Col.
  Cong.
}
treat_equalities.
exists M.
split.
Between.
right; auto.
induction H0.
spliter.
induction H11.

assert(exists X : Tpoint, Bet B X A /\ Bet O M X).
{
  apply(outer_pasch B A A' O M);
  Between.
}
ex_and H12 P'.
exists P'.
split.
Between.
right.
unfold Out in  H2.
spliter.
induction H15.

unfold Out.
repeat split; auto.
intro.
treat_equalities; tauto.

assert(Bet O P P' \/ Bet O P' P).
apply(l5_1 O M P P'); Between.
tauto.
apply l6_6.
apply(l6_7 O P M P');
apply bet_out; auto.
assert(exists X : Tpoint, Bet M X O /\ Bet B X A).
apply (inner_pasch A O A' M B); Between.
ex_and H12 P'.
exists P'.
split; Between.
right.
unfold Out in  H2.
spliter.
induction H15.
unfold Out.
repeat split; auto.
intro.
treat_equalities.
apply H8; Between.
left.
apply(between_exchange4 O P' M P); Between.
unfold Out.
repeat split;auto.
intro.
treat_equalities.
apply H9; Col.
assert(Bet O P P' \/ Bet O P' P).
{
  apply(l5_3 O P P' M);
  Between.
}
tauto.
assert(CongA A O M A' O M).
apply(cong3_conga);auto.
repeat split; Cong.
apply(out_conga A O M A' O M A P B P);auto;try(apply out_trivial; auto).
Qed.


Lemma halfA_uniqueness : forall O A B P P', HalfA P A O B -> HalfA P' A O B -> Out O P P'.
Proof.
intros.
apply halfa_chara1 in H.
apply halfa_chara1 in H0.
ex_and H A1.
ex_and H1 M1.
ex_and H0 A2.
ex_and H4 M2.
assert(Out O A1 A2) by (apply l6_7 with B;finish).

assert (A1 = A2).
{
  assert_diffs.
  apply(l6_11_uniqueness O O A B A1 A2); auto.
}
subst A2.
assert(M1 = M2).
{
  apply(l7_17 A A1); auto.
}
subst M2.
eapply l6_7 with M1;finish.
Qed.

Lemma halfa_not_null : forall P A O B, ~Col A O B  -> HalfA P A O B -> ~Col A O P.
Proof.
intros.
intro.
unfold HalfA in *.
spliter.
unfold InAngle in *.
spliter.
ex_and H6 P'.
induction H7.
subst P'.
contradiction.
assert(CongA A O P' B O P').
{
  assert_diffs.
  apply l6_6 in H7.
  apply(out_conga A O P B O P A P' B P' H3); auto; try(apply out_trivial; auto).
}
assert(HH:= col_conga_col A O P B O P H1 H3). 
apply H.
ColR.
Qed.

Lemma null_halfa__null : forall P A O B, Col A O B  -> HalfA P A O B -> Out O A P.
Proof.
intros.
unfold HalfA in *.
spliter.
assert(Out O A B).
{
  induction H.
  contradiction.
  assert_diffs.
  repeat split; auto.
  induction H.
  right; auto.
  left; Between.
}
apply(in_angle_out A O B P); auto.
Qed.


Lemma halfa__acute : forall P A O B, HalfA P A O B -> Acute A O P.
Proof.
intros.
assert(HA:=H).
unfold HalfA in H.
spliter.
induction(Col_dec A O B).
assert(Out O A B).
induction H2.
contradiction.
assert_diffs.
unfold Out.
repeat split; auto.
induction H2.
right;Between.
left; Between.
assert(HH:= in_angle_out A O B P H3 H0).
apply out__acute; auto.

assert(HB:=HA).
assert(HH:=halfa_chara1 P A O B HB).
ex_and HH A'.
ex_and H3 M.

assert(exists Q : Tpoint, Perp P O Q O /\ OS P O A Q).
{
  apply(l10_15 P O O A).
  Col.
  intro.
  assert(Col P O A) by Col.
  apply (halfa_not_null P A O B); Col.
}
ex_and H7 Q.

assert(A <> M).
{
  intro.
  treat_equalities.
  apply H2; Col.
}

assert(Per O M A).
{
  unfold Per.
  exists A'.
  split; Cong.
}

assert_diffs.
apply per_perp_in in H10; auto.
apply perp_in_comm in H10.
apply perp_in_perp in H10.

assert(Perp O P A M).
{
  apply (perp_col O M A M P); Col.
  Perp.
}
assert(Par O Q A M).
{
  apply (l12_9 _ _ _ _ O P); Perp.
}

assert(HN:= halfa_not_null P A O B H2 HB).

assert(Par_strict O Q A M).
{
  induction H21.
  assumption.
  spliter.
  apply False_ind.
  apply HN; ColR.
}
clear H21.
assert(HP1:= l12_6 O Q A M H24).

assert(Par_strict O Q A A').
{    
  apply(par_strict_col_par_strict _ _ _ M); Col.
}
assert(HP2:= l12_6 O Q A A' H21).

assert(OS O Q M P).
{
  apply(out_one_side O Q M P); auto.
  right.
  apply perp_left_comm in H7.
  apply perp_not_col in H7.
  Col.
}
assert(InAngle A Q O P).
{
  apply(os2__inangle Q O P A).
  apply (one_side_transitivity _ _ _ M).
  apply one_side_symmetry; auto.
  apply one_side_symmetry;auto.
  apply invert_one_side.
  apply one_side_symmetry; auto.
}

assert(HP:Per P O Q).
{
  apply perp_left_comm in H7.
  apply perp_perp_in in H7.
  apply perp_in_comm in H7.
  apply perp_in_per in H7.
  auto.
}

unfold Acute.
exists P.
exists O.
exists Q.
split;auto.
assert_diffs.
unfold LtA.
split.
unfold LeA.
exists A.
split.
apply l11_24; auto.
apply conga_right_comm.
apply conga_refl; auto.
intro.
assert(CongA P O B P O Q).
{
  apply (conga_trans _ _ _ A O P);
  CongA.
}
assert(Per P O B).
{
  apply(l11_17 P O Q P O B); CongA.
}

assert(Per P O A).
{
  apply(l11_17 P O Q P O A); CongA.
}
assert(Col A B O).
{
  apply(per_per_col A B P O); Perp.
}
apply H2; Col.
Qed.


Lemma halfa_lea : forall P A O B, HalfA P A O B -> LeA A O P A O B.
Proof.
intros.
unfold HalfA in *.
spliter.
apply(inangle__lea).
assumption.
Qed.

Lemma halfa2_lea___lea : forall A O B A' B' P, HalfA P A O B -> HalfA P A' O B'
                                            -> LeA A' O P A O P -> LeA A' O B' A O B.
Proof.
intros.
assert(HH0:=H).
assert(HH1:=H0).
unfold HalfA in H0, H.
spliter.
assert(LeA B' O P B O P).
{
  apply(l11_30 A' O P A O P B' O P B O P); auto.
}
induction(Col_dec B P O).
assert(Out O B P).
{
  assert_diffs.
  repeat split; auto.
  induction H7.
  right; Between.
  induction H7.
  assert(~Bet B O P).
  {
    apply(halfa_nbet B O A P).
    apply halfa_sym; auto.
  }
  apply between_symmetry in H7; contradiction.
  left; auto.
}
assert(Out O A P).
{
  apply(l11_21_a B O P A O P); CongA.
}
assert (Out O A B) by (apply l6_7 with P;finish).

assert(HP:=out_lea__out A' O P A O P H9 H1).
assert(HQ:=out_lea__out B' O P B O P H8 H6).
assert (Out O A' B') by (apply l6_7 with P;finish).

assert_diffs.
apply l11_31_1; auto.

induction(Col_dec B' P O).
assert(Out O B' P).
{
  assert_diffs.
  repeat split; auto.
  induction H8.
  right; Between.
  induction H8.
  assert(~Bet B' O P).
  {
    apply(halfa_nbet B' O A' P).
    apply halfa_sym; auto.
  }
  apply between_symmetry in H8; contradiction.
  left; auto.
}
assert(Out O A' P).
{
  apply(l11_21_a B' O P A' O P); CongA.
}
assert (Out O A' B') by (apply l6_7 with P;finish).
assert_diffs.
apply l11_31_1; auto.

(* general case *)

assert(HH:=one_or_two_sides P O B B' H7 H8).
assert(~Col O A P).
{
  intro.
  assert(Col B O P).
  apply(col_conga_col A O P B O P); Col.
  apply H7; Col.
}

assert(TS P O A B).
{
  apply (in_angle_two_sides A O B P); Col.
}

assert(TS P O A' B').
{
  apply (in_angle_two_sides A' O B' P); Col.
  intro.
  assert(Col B' O P).
  {
    apply(col_conga_col A' O P B' O P); Col.
  }
  apply H8; Col.
}

induction HH.
assert(OS P O A B').
{
  apply(l9_8_1 P O A B' B); auto.
  apply l9_2; auto.
}

assert(InAngle B' P O A).
{
  apply(lea_in_angle P O A B');auto.
  assert_diffs.
  apply(l11_30 P O A' P O A); CongA.
  apply lea_comm; auto.
}

assert(InAngle A' P O B).
{
  apply(lea_in_angle P O B A');auto.
  assert_diffs.
  apply(l11_30 P O B' P O B); CongA.
  apply lea_comm; auto.
  apply one_side_symmetry.
  apply(l9_8_1 P O A' B B'); auto.
}
assert(InAngle B' A O B).
{
  apply(in_angle_trans A O B' P B); auto.
  apply l11_24; auto.
}

assert(InAngle A' B O A).
{
  apply(in_angle_trans B O A' P A); auto;
  apply l11_24; auto.
}
apply l11_24 in H17.

apply(inangle2__lea A O B A' B' H17 H16).

assert(InAngle B' P O B).
{
  apply(lea_in_angle P O B B');auto.
  assert_diffs.
  apply(l11_30 P O B' P O B); CongA.
  apply lea_comm; auto.
}

assert(InAngle A' P O A).
{
  apply(lea_in_angle P O A A');auto.
  assert_diffs.
  apply(l11_30 P O A' P O A); CongA.
  apply lea_comm; auto.
  apply (l9_8_1 P O A A' B); auto.
  apply l9_2.
  apply(l9_8_2 P O B' B A').
  apply l9_2; auto.
  apply one_side_symmetry; auto.
}
assert(InAngle B' A O B).
{
  apply l11_24.
  apply(in_angle_trans B O B' P A); apply l11_24; auto.
}

assert(InAngle A' A O B).
{
  apply(in_angle_trans A O A' P B); auto;
  apply l11_24; auto.
}

apply(inangle2__lea A O B A' B' H16 H15).
Qed.

Lemma halfa_ts : forall P A O B, ~Col A O B -> HalfA P A O B -> TS O P A B.
Proof.
intros.
assert(HM:=H0).
unfold HalfA in H0.
spliter.
assert(~Col A O P).
{
  apply(halfa_not_null P A O B H HM).
}

assert(~Col B O P).
{
  apply(halfa_not_null P B O A); Col.
  apply halfa_sym; auto.
}
apply invert_two_sides.
apply(in_angle_two_sides A O B P); Col.
Qed.


(*
Lemma out2_out13 : forall A B B' C, Out A B C -> Out A B' C -> Out A B B'.
Proof.
intros.
unfold Out in *.
spliter.
repeat split; auto.
induction H4; induction H2.
apply (l5_3 A B B' C);Between.
left.
apply (between_exchange4 A B C B'); Between.
right.
apply (between_exchange4 A B' C B); Between.
apply (l5_1 A C B B');Between.
Qed.
*)


Lemma conga_halfa__conga1 : forall P A O B A' B', 
 HalfA P A O B -> HalfA P A' O B' ->
 CongA A O P A' O P -> 
 CongA A O B A' O B'.
Proof.
intros.

induction(Col_dec A O B).
unfold HalfA in *.
spliter.
assert(Out O A B).
{
  assert_diffs.
  repeat split; auto.
  induction H2.
  contradiction.
  induction H2.
  right; auto.
  left; Between.
}

assert(HH:=in_angle_out A O B P H7 H5).
assert(HP:=l11_21_a A O P A' O P HH H1).
assert(HQ:=l11_21_a A' O P B' O P HP H4).
assert (HX:Out O A' B') by (apply l6_7 with P;finish).
apply(l11_21_b A O B A' O B' H7 HX).

assert(HH:=halfa_not_null P A O B H2 H).
assert(~Col A' O B').
{
  intro.
  unfold HalfA in *.
  spliter.
  assert(Out O A' B').
  {
    assert_diffs.
    repeat split; auto.
    induction H3.
    contradiction.
    induction H3.
    right; auto.
    left; Between.
  }
  assert(HT:=in_angle_out A' O B' P H8 H4).
  assert(Out O A P).
  {
    apply(l11_21_a A' O P A O P ); CongA.
  }
  assert(HQ:=l11_21_a A O P B O P H9 H7).
  assert(Out O A B) by (apply l6_7 with P;finish).
  apply H2; Col.
}

apply(l11_22a A O B P A' O B' P).
split.
apply halfa_ts; auto.
split.
apply halfa_ts; auto.
split; auto.
unfold HalfA in *.
spliter.
assert(CongA B' O P A O P).
{
  apply(conga_trans B' O P A' O P A O P); CongA.
}
apply(conga_trans P O B P O A P O B'); CongA.
Qed.

Lemma out_preserves_halfa : forall P A O B P' A' B', 
 Out O A A' -> Out O B B' -> Out O P P' ->
 HalfA P A O B -> HalfA P' A' O B'.
Proof.
intros.
unfold HalfA in *.
spliter.
split.
intro.
apply H2.
unfold Out in H, H0.
spliter.
induction H9; induction H7;
eBetween.
split.
apply (l11_25 P A O B); try (apply l6_6; auto); auto.
apply (out_conga A O P B O P A' P' B' P'); auto.
Qed.



Lemma conga_halfa__conga2 : forall P A O B A' B', 
 HalfA P A O B -> HalfA P A' O B' -> 
 CongA A O B A' O B' -> CongA A O P A' O P .
Proof.
intros.

induction(Col_dec A O B).
assert(Hp:= null_halfa__null P A O B H2 H).
assert(Col A' O B').
{
  apply(col_conga_col A O B); auto.
}
assert(Hq:= null_halfa__null P A' O B' H3 H0).
{
  apply l11_21_b; auto.
}

assert(exists X : Tpoint, (Bet O A' X \/ Bet O X A') /\ Cong O X O A).
{
  assert_diffs.
  apply(segment_construction_2 A' O O A);auto.
}
ex_and H3 A''.
assert(HalfA P A'' O B').
{
  unfold HalfA in H.
  spliter.
  assert_diffs.
  apply(out_preserves_halfa P A' O B' P A'' B'); try(apply out_trivial; auto); auto.
  repeat split; auto.
}
assert(O <> P).
intro.
treat_equalities.
unfold HalfA in H.
spliter.
unfold CongA in H7.
tauto.
assert_diffs.

assert(Out O A'' A').
{
  repeat split; auto.
  tauto.
}

apply(out_conga A O P A'' O P A P A' P);try(apply out_trivial;auto); auto.


apply halfa_chara1 in H.
apply halfa_chara1 in H5.
ex_and H C.
ex_and H14 M.
ex_and H5 C'.
ex_and H17 M'.

assert(CongA A O C A'' O C').
{
  apply(out_conga A O B A' O B' A C A'' C');
  try(apply out_trivial;auto); auto;
  apply l6_6; auto.
}

assert(Cong A C A'' C').
{
  apply(cong2_conga_cong A O C A'' O C'); eCong.
}

assert(Cong A M A'' M').
{
  apply(cong_cong_half_1 A M C A'' M' C'); auto.
}

assert(CongA A O C A'' O C' /\ CongA O A C O A'' C' /\ CongA A C O A'' C' O).
{
  assert_diffs.
  apply(l11_51 O A C O A'' C'); eCong.
  intro.
  treat_equalities.
  apply H2; Col.
}
spliter.
assert(CongA O A M O A'' M').
{
  unfold Midpoint in *.
  spliter.
  apply (out_conga O A C O A'' C' O M O M');
  try(apply out_trivial;auto); auto.
  apply l6_6.
  apply bet_out; auto.
  intro.
  treat_equalities.
  apply H2.
  Col.
  apply l6_6.
  apply bet_out; auto.
  intro.
  treat_equalities.
  apply H2.
  Col.
}
assert(Cong O M O M').
{
  apply(cong2_conga_cong O A M O A'' M'); Cong.
}
assert(M = M').
{
  apply(l6_11_uniqueness O O M P M M'); Cong.
  intro.
  treat_equalities.
  unfold Out in H16; tauto.
}
subst M'.


assert(CongA O A M O A'' M /\ CongA A O M A'' O M /\ CongA O M A O M A'').
{
  assert_diffs.
  apply(l11_51 A O M A'' O M); Cong.
}
spliter.
apply(out_conga A O M A'' O M A P A'' P);
try(apply out_trivial;auto); auto.
Qed.

Lemma halfa2_lta__lta1 : forall A O B A' B' P, HalfA P A O B -> HalfA P A' O B'
                                            -> LtA A' O P A O P -> LtA A' O B' A O B.
Proof.
intros.
unfold LtA in *.
spliter.
split.
apply(halfa2_lea___lea A O B A' B' P); auto.
intro.
apply H2.
apply (conga_halfa__conga2 P A' O B' A B); auto.
Qed.


Lemma lea_halfa_lea : forall  P A O B A' B', LeA A' O B' A O B -> HalfA P A O B -> HalfA P A' O B'
                                          -> LeA A' O P A O P.
intros.
assert(HH0:=H0).
assert(HH1:=H1).
unfold HalfA in H0, H1.
spliter.
assert(LeA A' O P A O P \/ LeA A O P A' O P).
{
  assert_diffs.
  apply(lea_total A' O P A O P);auto.
}
induction H6.
auto.

assert(HH:= halfa2_lea___lea A' O B' A B P HH1 HH0 H6).
assert(HP:= lea_asym A O B A' O B' HH H).
apply conga__lea.
apply(conga_halfa__conga2 P A' O B' A B); auto.
apply conga_sym; auto.
Qed.

Lemma halfa2_lta__lta2 : forall A O B A' B' P, HalfA P A O B -> HalfA P A' O B'
                                            -> LtA A' O B' A O B -> LtA A' O P A O P.
Proof.
intros.
unfold LtA in *.
spliter.
split.
apply(lea_halfa_lea P A O B A' B'); auto.
intro.
apply H2.
apply(conga_halfa__conga1 P A' O B' A B); auto.
Qed.

Lemma col_halfa__out : forall P A O B, Col A O B -> HalfA P A O B -> Out O A B.
Proof.
intros.
unfold HalfA in H0.
spliter.
unfold Out.
assert_diffs.
repeat split; auto.
induction H.
contradiction.
induction H.
right; auto.
left; Between.
Qed.

Lemma lta_nbet__ncol : forall A B C X Y Z, ~Bet X Y Z -> LtA A B C X Y Z -> ~Col X Y Z.
Proof.
intros.
intro.
unfold LtA in H0.
spliter.
assert(Out Y X Z).
assert_diffs.
repeat split; auto.
induction H1.
contradiction.
induction H1.
right; auto.
left; Between.
unfold LeA in H0.
ex_and H0 P.
assert(HH:=in_angle_out X Y Z P H3 H0).
apply H2.
assert(HP:= l11_21_b X Y Z X Y P H3 HH).
apply(conga_trans _ _ _ X Y P); CongA.
Qed.



Lemma col_halfa__out2 : forall P A O B, Col A O P -> HalfA P A O B -> Out O A P.
Proof.
intros.
assert(HH:= halfA_nbet2 A O B P H0).
spliter.

unfold HalfA in H0.
spliter.
induction H.

contradiction.
assert_diffs.
repeat split; auto.
induction H.
right; auto.
left; Between.
Qed.



Definition gHalfA A' O' B' A O B := exists P, HalfA P A O B /\ CongA A' O' B' A O P.

Lemma halfa_perp__os : forall P A O B T, HalfA P A O B -> Perp O P T O -> OS O T P A.
Proof.
intros.
assert(Ha:=halfa__acute P A O B H).
unfold Acute in Ha.
ex_and Ha A'.
ex_and H1 O'.
ex_and H2 B'.
assert(Per P O T).
{
  apply perp_perp_in in H0.
  apply perp_in_comm in H0.
  apply perp_in_per in H0.
  assumption.
}
assert(CongA A' O' B' P O T).
{
  assert_diffs. 
  apply(l11_16 A' O' B' P O T); auto.
}
assert(LtA A O P P O T).
{
  apply (conga_preserves_lta A O P A' O' B'); CongA.
  assert_diffs.
  apply conga_refl; auto.
}
induction(Col_dec A O P).
assert(Out O A P).
{
  apply (col_halfa__out2 P A O B); auto.
}
apply(out_one_side).
apply perp_not_col in H0.
left; Col.
apply l6_6; auto.

apply lta_left_comm in H2.
unfold LtA in H2.
spliter.
assert(TS P O T A \/ OS P O T A).
{
  apply(one_or_two_sides P O T A); Col.
  apply perp_not_col in H0.
  Col.
}

induction H8.
assert(HC:=symmetric_point_construction T O).
ex_and HC T'.
unfold Midpoint in *.
spliter.

assert(CongA P O T P O T').
{
  assert_diffs. 
  apply(l11_18_1 P O T T'); auto.
}
assert(LeA P O A P O T').
{
  unfold LtA in H5.
  spliter.
  apply (l11_30 P O A P O T); CongA.
  apply lea_left_comm.
  auto.
  assert_diffs.
  apply conga_refl;
  auto.
}

assert(Perp O T' P O).
{
  apply (perp_col O T P O T').
  intro.
  treat_equalities.
  assert_diffs; tauto.
  Perp.
  Col.
}

assert(TS P O T T').
{
  unfold TS.
  repeat split; Col.
  apply perp_not_col in H0.
  Col.
  apply perp_not_col in H13.
  Col.
  exists O.
  split; Col.
}

assert(InAngle A P O T').
{
  apply(lea_in_angle P O T' A H12).
  apply (l9_8_1 _ _ _ _ T);
  apply l9_2; auto.
}
apply(col_one_side O T' T P A); Col.
intro.
treat_equalities.
unfold TS in H14.
spliter.
apply H9; Col.
apply invert_one_side.
apply one_side_symmetry.
apply(in_angle_one_side T' O P A).
apply perp_not_col in H13.
Col.

intro.
assert(Col O T A).
{
  assert_diffs.
  ColR.
}
assert(Per P O A).
{
  assert_diffs.
  apply(per_col P O T A); auto.
}
unfold LtA in H5.
spliter.
apply H19.
assert_diffs.
apply l11_16; Perp.
apply l11_24.
auto.

assert(InAngle A P O T).
{
  apply(lea_in_angle P O T A).
  induction H5.
  apply lea_left_comm; auto.
  auto.
}
apply one_side_symmetry.
apply(invert_one_side).
apply(in_angle_one_side T O P A).
apply perp_not_col in H0.
Col.
intro.
assert(Per P O A).
{
  assert_diffs.
  apply(per_col P O T A); auto.
}
unfold LtA in H5.
spliter.
apply H12.
assert_diffs.
apply l11_16; Perp.
apply l11_24.
auto.
Qed.

Lemma halfa_perp__os2 : forall P A O B T, HalfA P A O B -> Perp O P T O -> OS O T P A /\ OS O T P B.
Proof.
intros.
split.
apply(halfa_perp__os P A O B); auto.
apply halfa_sym in H.
apply(halfa_perp__os P B O A); auto.
Qed.





 

Lemma galfa_preseves_lta : forall A B C X Y Z A' B' C' X' Y' Z', LtA A B C X Y Z -> gHalfA A' B' C' A B C -> gHalfA X' Y' Z' X Y Z -> LtA A' B' C' X' Y' Z'.
Proof.
intros.
unfold gHalfA in *.
ex_and H0 M.
ex_and H1 N.

assert(~Col X Y Z).
{
  unfold HalfA in H1.
  spliter.
  apply(lta_nbet__ncol A B C); auto.
}
assert(HH:=halfa_not_null N X Y Z H4 H1).
assert(Hp:~ Col Z Y N).
{
  apply(halfa_not_null N Z Y X );Col.
  apply halfa_sym; auto.
}

assert(~Col X' Y' Z').
intro.
apply HH.
apply(col_conga_col X' Y' Z'); auto.

induction(Col_dec A' B' C').
assert(Col A B M).
{
  apply(col_conga_col A' B' C'); auto.
}
assert(Out B' A' C').
{
  spliter.
  apply(out_conga_out A B M); CongA.
  assert(HP:= halfA_nbet2 A B C M H0).
  spliter.
  assert_diffs.
  repeat split; auto.
  induction H7.
  contradiction.
  induction H7.
  right; auto.
  left; Between.
}

unfold LtA.
split.
assert_diffs.
apply(l11_31_1); auto.
intro.
assert(Out Y' X' Z').
{
  apply (out_conga_out A' B' C'); auto.
}
apply H5.
Col.

assert(HC:~Col A B C).
{
  intro.
  unfold HalfA in H0.
  spliter.
  assert(Out B A C).
  assert_diffs.
  induction H7.
  contradiction.
  repeat split; auto.
  induction H7.
  right; Between.
  left; Between.
  assert(Out B A M).
  {
    apply(in_angle_out _ _ C); auto.
  }
  assert(Out B' A' C').
  {
    apply (out_conga_out A B M); CongA.
  }
  apply H6; Col.
}

assert(exists P : Tpoint, CongA A' B' C' N Y P /\ OS N Y P X).
apply(angle_construction_1 A' B' C' N Y X); Col.
ex_and H7 AA.

assert(exists P : Tpoint, CongA A' B' C' N Y P /\ OS N Y P Z).
apply(angle_construction_1 A' B' C' N Y Z); Col.
ex_and H9 CC.


assert(TS Y N X Z).
{
  apply halfa_ts; auto.
}

assert(HT:TS Y N AA CC).
{
  apply(l9_8_2 Y N X).
  apply l9_2.
  apply(l9_8_2 Y N Z).
  apply l9_2; auto.
  apply invert_one_side.
  apply one_side_symmetry; auto.
  apply invert_one_side.
  apply one_side_symmetry; auto.
}

assert(CongA A B C AA Y CC).
{
  apply (l11_22a A B C M AA Y CC N).
  split.
  apply halfa_ts; auto.
  split; auto.
  split.
  apply(conga_trans _ _ _ A' B' C'); CongA.
  unfold HalfA in H0.
  spliter.
  apply conga_sym.
  apply(conga_trans _ _ _ A B M); CongA.
  apply(conga_trans _ _ _ A' B' C'); CongA.
}

assert( exists X : Tpoint, Perp Y X N Y).
{
  apply(perp_exists Y N Y).
  assert_diffs.
  auto.
}
ex_and H13 P.
assert(OS Y P N AA).
{
  apply(acute_one_side AA N Y P); Perp.
  apply(acute_conga__acute A' B' C'); auto.
  apply(acute_conga__acute A B M);CongA.
  apply(halfa__acute _ _  _ C).
  assumption.
}
assert(OS Y P N CC).
{
  apply(acute_one_side CC N Y P); Perp.
  apply(acute_conga__acute A' B' C'); auto.
  apply(acute_conga__acute A B M);CongA.
  apply(halfa__acute _ _  _ C).
  assumption.
}

assert(~ Bet AA Y CC).
{
  intro.
  assert(TS Y P AA CC).
  {
    unfold TS.
    repeat split; Col.
    apply one_side_not_col124 in H13.
    Col.
    apply one_side_not_col124 in H15.
    Col.
    exists Y.
    split; Col.
  }
  apply l9_9 in H17.
  apply H17.
  apply (one_side_transitivity _ _ _ N); auto.
  apply one_side_symmetry; auto.
}

assert(OS Y P AA CC).
{
  apply(one_side_transitivity _ _ _ N); auto.
  apply one_side_symmetry; auto.
}

assert(InAngle N AA Y CC).
{
  assert_diffs.
  repeat split; auto.
  unfold TS in HT.
  spliter.
  ex_and H39 T.
  exists T.
  split; auto.
  right.
  assert(OS Y P AA T).
  {
    apply (l9_17 _ _ CC); auto.
  }
  apply(col_one_side_out Y P T N); Col.
  apply (one_side_transitivity _ _ _ AA);
  apply one_side_symmetry; auto.
}

assert(HalfA N AA Y CC).
{
  unfold HalfA.
  split; auto.
  split; auto.
  apply (conga_trans _ _ _ A' B' C'); CongA.
}

apply (conga_preserves_lta AA Y N X Y N); CongA.

apply(halfa2_lta__lta2 X Y Z AA CC N); auto.
apply (conga_preserves_lta A B C X Y Z); CongA.
assert_diffs.
apply conga_refl; auto.
Qed.

Lemma inangle_halfa_inangle : forall O A B C A' C',
  ~Col A O B -> InAngle C A O B ->
  HalfA A' A O B -> HalfA C' C O B ->
  InAngle C' A' O B.
Proof.
intros.
assert(HH1 := H1).
assert(HH2:= H2).
assert(HD:A' <> O).
{
  intro.
  treat_equalities.
  unfold HalfA in *.
  spliter.
  assert_diffs.
  intuition.
}

induction(Col_dec A O C).
assert(Out O A C).
{
  apply(col_in_angle_out A O B C); Col.
  intro.
  apply H.
  Col.
}

assert(HalfA A' C O B).
{
  unfold HalfA in HH1; spliter.
  assert_diffs.
  apply(out_preserves_halfa A' A O B A' C B); auto;
  try(apply out_trivial; auto).
}
assert(Out O A' C').
{
  apply(halfA_uniqueness O C B); auto.
}

assert(InAngle C' A' O B).
{
  assert_diffs.
  apply col_in_angle; auto.
}
assumption.


induction(Col_dec B O C).
assert(Out O B C).
{
  apply(col_in_angle_out B O A C); Col.
  intro.
  apply H.
  Col.
  apply l11_24; auto.
}


assert(Out O C C').
{
  apply (null_halfa__null C' C O B); Col.
}

assert(Out O B C').
{
  apply l6_7 with C;auto.
}

assert_diffs.
apply col_in_angle; auto.

assert(LtA C' O B A' O B).
{
  apply(galfa_preseves_lta C O B A O B C' O B A' O B).
  repeat split.
  apply lea_comm.
  apply inangle__lea.
  apply l11_24.
  auto.
  intro.
  assert(OS O B A C).
  {
    apply one_side_symmetry.
    apply invert_one_side.
    apply(in_angle_one_side).
    Col.
    intro.
    apply H.
    apply (col_conga_col C O B);Col.
    apply l11_24; auto.
  }
  assert(Out O A C).
  {
    apply(conga_os__out _ B); auto.
    CongA.
  }
  apply H3.
  Col.
  unfold gHalfA.
  exists C'.
  split; auto.
  unfold HalfA in H2.
  spliter.
  CongA.
  unfold gHalfA.
  exists A'.
  split; auto.
  unfold HalfA in H1.
  spliter.
  CongA.
}
unfold LtA in H5.
spliter.
apply l11_24.
apply lea_in_angle.
apply lea_comm.
auto.
assert(OS O B A A').
{
  unfold HalfA in H1.
  spliter.
  apply l11_24 in H7.
  apply in_angle_one_side in H7.
  apply invert_one_side.
  apply one_side_symmetry.
  auto.
  Col.
  assert(~ Col B O A').
  {
    apply (halfa_not_null _ _ _ A); Col.
    apply halfa_sym; auto.
  }
  Col.
}
assert(OS O B C C').
{
  unfold HalfA in H2.
  spliter.
  apply l11_24 in H8.
  apply in_angle_one_side in H8.
  apply invert_one_side.
  apply one_side_symmetry.
  auto.
  Col.
  assert(~ Col B O C').
  apply (halfa_not_null _ _ _ C); Col.
  apply halfa_sym; auto.
  Col.
}

apply (one_side_transitivity _ _ _ A).
apply invert_one_side.
apply one_side_symmetry; auto.
apply (one_side_transitivity _ _ _ C).
apply one_side_symmetry.
apply(in_angle_one_side); Col.
apply l11_24; auto.
apply invert_one_side.
auto.
Qed.

(** Given two angles a and b, a/2=b/2 -> a=b. *)

Lemma ghalfa_preserves_conga_1 : forall A B C A' B' C' X Y Z X' Y' Z', 
 gHalfA X Y Z A B C -> gHalfA X' Y' Z' A' B' C' ->
 CongA X Y Z X' Y' Z' -> CongA A B C A' B' C'.
Proof.
intros.
unfold gHalfA in *.
ex_and H P.
ex_and H0 P'.
assert(HA1:= H).
assert(HA2:= H0).
unfold HalfA in H.
unfold HalfA in H0.
spliter.

assert(CongA A B P A' B' P').
{
  apply(conga_trans _ _ _ X Y Z); CongA.
  apply(conga_trans _ _ _ X' Y' Z'); CongA.
}

assert(CongA C B P C' B' P').
{
  apply(conga_trans _ _ _ A B P); CongA.
  apply(conga_trans _ _ _ A' B' P'); CongA.
}

induction(Col_dec A B P).
assert(Col C B P).
{
  apply (col_conga_col A B P); Col.
}

assert(Col A B C).
{
  assert_diffs.
  ColR.
}

assert(Col A' B' P').
{
  apply(col_conga_col A B P); Col.
}

assert(Col C' B' P').
{
  apply(col_conga_col C B P); Col.
}

assert(Col A' B' C').
{
  assert_diffs.
  ColR.
}

assert(Out B A C).
{
  assert_diffs.
  repeat split; auto.
  induction H12.
  contradiction.
  induction H12.
  right; auto.
  left; Between.
}

assert(Out B' A' C').
{
  assert_diffs.
  repeat split; auto.
  induction H15.
  contradiction.
  induction H15.
  right; auto.
  left; Between.
}

apply l11_21_b; auto.

assert(~Col C B P).
{  
  intro.
  apply H10.
  apply (col_conga_col C B P); CongA.
}

assert(~Col A' B' P').
{
  intro.
  apply H10.
  apply (col_conga_col A' B' P'); CongA.
}

assert(~Col C' B' P').
{
  intro.
  apply H12.
  apply (col_conga_col C' B' P'); CongA.
}

assert(TS P B A C).
{
  apply(in_angle_two_sides A B C P); Col.
}

assert(TS P' B' A' C').
{
  apply(in_angle_two_sides A' B' C' P'); Col.
}

apply invert_two_sides in H14.
apply invert_two_sides in H15.

apply(l11_22a A B C P A' B' C' P' ).
split; auto.
split; auto.
split; CongA.
Qed.

(** Given two angles a and b,  a=b -> a/2 = b/2 . *)

Lemma ghalfa_preserves_conga_2 : forall A B C A' B' C' X Y Z X' Y' Z',
 gHalfA X Y Z A B C -> gHalfA X' Y' Z' A' B' C' -> CongA A B C A' B' C' ->
 CongA X Y Z X' Y' Z'.
Proof.
intros.
unfold gHalfA in *.
ex_and H P.
ex_and H0 P'.
assert(HA1:= H).
assert(HA2:= H0).
unfold HalfA in H.
unfold HalfA in H0.
spliter.

induction(Col_dec A B C).
assert(Out B A C).
{
  assert_diffs.
  repeat split; auto.
  induction H8.
  contradiction.
  induction H8.
  right; auto.
  left; Between.
}

assert(HH:= l11_21_a A B C A' B' C' H9 H1).

assert(HP:=out_in_angle_out A B C P H9 H6).
assert(HQ:=out_in_angle_out A' B' C' P' HH H4).

assert(HT:= l11_21_b A B P A' B' P' HP HQ).
apply(conga_trans _ _ _ A B P); CongA.
apply (conga_trans _ _ _ A' B' P'); CongA.

assert(~Col A' B' C').
{
  intro.
  apply H8.
  apply (col_conga_col A' B' C'); CongA.
}

assert(HM:=halfa_not_null P A B C H8 HA1).
assert(~ Col C B P).
{
  apply(halfa_not_null P C B A ).
  Col.
  apply halfa_sym; auto.
}
assert(HN:=halfa_not_null P' A' B' C' H9 HA2).
assert(~ Col C' B' P').
{
  apply(halfa_not_null P' C' B' A').
  Col.
  apply halfa_sym; auto.
}

assert(HH:= halfa_chara1 P A B C HA1).
ex_and HH CC.
ex_and H12 M.


assert(exists X : Tpoint, (Bet B' A' X \/ Bet B' X A') /\ Cong B' X A B).
{
  apply(segment_construction_2 A' B' A B).
  assert_diffs;auto.
}
ex_and H16 AA'.

assert(exists X : Tpoint, (Bet B' C' X \/ Bet B' X C') /\ Cong B' X A B).
{
  apply(segment_construction_2 C' B' A B).
  assert_diffs;auto.
}
ex_and H18 CC'.

assert(CongA A B C A B CC).
{
  assert_diffs.
  apply (out_conga A B C A B C A C A CC); try(apply out_trivial; auto).
  apply conga_refl; auto.
  apply l6_6; auto.
}

assert(CongA A' B' C' AA' B' CC').
{
  assert_diffs.
  apply (out_conga A' B' C' A' B' C' A' C' AA' CC'); try(apply out_trivial; auto).
  apply conga_refl; auto.
  repeat split; auto.
  repeat split; auto.
}

assert(CongA A B CC AA' B' CC').
{
  apply(conga_trans _ _ _ A B C); CongA.
  apply(conga_trans _ _ _ A' B' C'); CongA.
}
assert(Cong A CC AA' CC' /\
     (A <> CC -> CongA B A CC B' AA' CC' /\ CongA B CC A B' CC' AA')).
{
  apply(l11_49 A B CC AA' B' CC' H22); eCong.
}
spliter.


assert(A <> CC).
{
  intro.
  treat_equalities.
  apply H9.
  apply(col_conga_col AA' B' AA' A' B' C'); Col.
  CongA.
}
apply H24 in H25.
spliter.
clear H24.

assert(HH:= midpoint_existence AA' CC').
ex_and HH M'.

assert(Cong A M AA' M').
{
  apply(cong_cong_half_1 A M CC AA' M' CC'); auto.
}
assert(Cong B M B' M' /\
     (B <> M -> CongA A B M AA' B' M' /\ CongA A M B AA' M' B')).
{
  assert_diffs.
  unfold Midpoint in *.
  spliter.
  apply l11_49; eCong.
  apply (out_conga B A CC B' AA' CC' B M B' M'); try(apply out_trivial; auto).
  CongA.  
  repeat split; auto.
  repeat split; auto.
}
spliter.

assert(Out B' A' AA').
{
  assert_diffs.
  repeat split; auto.
}

assert(Out B' C' CC').
{
  assert_diffs.
  repeat split; auto.
}

assert(B <> M).
{
  intro.
  treat_equalities.
  apply H9.
  assert_diffs.
  ColR.
}

apply H29 in H32.
spliter.  
clear H29.




assert(HalfA M A B CC).
{
  apply(halfa_chara2 M A B CC).
  exists CC.
  exists M.
  assert_diffs.
  split; Cong.
  split.  
  apply out_trivial; auto.
  split; auto.
  apply out_trivial; auto.
}

assert(HalfA M' AA' B' CC').
{
  apply(halfa_chara2 M' AA' B' CC').
  exists CC'.
  exists M'.
  assert_diffs.
  split; eCong.
  split.
  apply out_trivial; auto.
  split; auto.
  apply out_trivial; auto.
}

assert(HalfA M A B C).
{
  assert_diffs.
  apply (out_preserves_halfa M A B CC M A C);auto;
  try(apply out_trivial; auto).
}

assert(HalfA M' A' B' C').
{
  assert_diffs.
  apply (out_preserves_halfa M' AA' B' CC' M' A' C');auto;
  try(apply out_trivial; auto).
  repeat split; auto.
  induction H16.
  right; auto.
  left; auto.
  repeat split; auto.
  induction H18.
  right; auto.
  left; auto.
}

assert(Out B M P).
{
  apply(halfA_uniqueness B A C M P); auto.
}

assert(Out B' M' P').
{
  apply(halfA_uniqueness B' A' C' M' P'); auto.
}
assert_diffs.
apply (conga_trans _ _ _ A B M).
apply (conga_trans _ _ _ A B P); CongA.
apply(out_conga A B P A B P A P A M);
try(apply out_trivial; auto).
apply conga_refl; auto.
apply l6_6; auto.
apply (conga_trans _ _ _ AA' B' M'); CongA.
apply (conga_trans _ _ _ A' B' P'); CongA.
apply(out_conga A' B' P' A' B' P' AA' M' A' P');
try(apply out_trivial; auto).
apply conga_refl; auto.
repeat split; auto.
apply l6_6; auto.
Qed.

End HalfAngle.
