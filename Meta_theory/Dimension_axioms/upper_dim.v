Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity.
Require Export GeoCoq.Tarski_dev.Coplanar_perm.

Section Upper_dim.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition upper_dim_axiom := forall A B C P Q : Tpoint,
  P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).

Definition all_coplanar_axiom := forall A B C D, Coplanar A B C D.

Lemma not_bet_out : forall A B C,
 Col A B C -> ~Bet A B C -> Out B A C.
Proof.
    intros.
    assert(A <> B) by (intro; subst; Between).
    assert(C <> B) by (intro; subst; Between).
    unfold Out.
    repeat split.
      assumption.
      assumption.
    unfold Col in H.
    induction H.
      contradiction.
    induction H.
      right.
      assumption.
    left.
    apply between_symmetry.
    assumption.
Qed.

Lemma or_bet_out : forall A B C, Bet A B C \/ Out B A C \/ ~Col A B C.
Proof.
    intros.
    elim(eq_dec_points A B).
      intro; left; Between.
    intro.
    elim(eq_dec_points C B).
      intro; left; Between.
    intro.
    induction(Col_dec A B C).
      unfold Col in *.
      decompose [or] H1.
        left.
        assumption.
        right;left.
        apply not_bet_out.
          unfold Col.
          assumption.
        intro.
        assert (Bet C B A) by Between.
        apply H0.
        symmetry.
        apply (between_equality B C A).
          assumption.
        assumption.
      right;left.
      apply not_bet_out.
        unfold Col.
        assumption.
      intro.
      assert (Bet B A C) by Between.
      apply H.
      apply (between_equality A B C).
        assumption.
      assumption.
    right;right.
    assumption.
Qed.

Lemma upper_dim_implies_per_per_col :
  upper_dim_axiom ->
  (forall A B C X, Per A X C -> X <> C -> Per B X C -> Col A B X).
Proof.
intros HUD A B C X HPer1 HDiff HPer2.
destruct HPer1 as [C' HPer1].
destruct HPer2 as [C'' HPer2].
assert (C' = C'') by (apply symmetric_point_unicity with C X; spliter; auto); treat_equalities.
unfold upper_dim_axiom in HUD.
spliter; assert_diffs; unfold Midpoint in *; spliter; apply HUD with C C'; Cong.
Qed.

Lemma upper_dim_implies_col_perp_perp_col :
  upper_dim_axiom ->
  (forall A B X Y P,
   P <> A ->
   Col A B P ->
   Perp A B X P ->
   Perp P A Y P ->
   Col Y X P).
Proof.
intro HUP; intros.
eapply upper_dim_implies_per_per_col; auto.
apply perp_in_per.
apply perp_in_sym.
apply perp_perp_in.
apply H2.
assumption.
apply perp_in_per.
apply perp_in_sym.
apply perp_perp_in.
apply perp_left_comm.
eapply perp_col.
auto.
apply H1.
assumption.
Qed.

Lemma out_two_sides_two_sides :
 forall A B X Y P PX,
  A <> PX ->
  Col A B PX ->
  Out PX X P ->
  TS A B P Y ->
  TS A B X Y.
Proof.
    intros.
    assert(OS A B P X).
      eapply (col_one_side _ PX).
        Col.
        unfold TS in H2.
        spliter.
        auto.
      apply invert_one_side.
      apply out_one_side.
        left.
        intro.
        unfold TS in H2.
        spliter.
        apply H4.
        ColR.
      apply l6_6.
      assumption.
    eapply l9_8_2.
      apply H2.
    assumption.
Qed.

Lemma upper_dim_implies_not_two_sides_one_side_aux :
  upper_dim_axiom ->
  (forall A B X Y PX,
   A <> B -> PX <> A ->
   Perp A B X PX ->
   Col A B PX ->
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ TS A B X Y ->
   OS A B X Y).
Proof.
intro HUD; intros.
assert(exists P, exists T, Perp PX A P PX /\ Col PX A T /\ Bet Y T P).
apply l8_21.
assumption.
ex_elim H6 P.
ex_and H7 T.
assert(HH:= upper_dim_implies_col_perp_perp_col HUD A B X P PX H0 H2 H1 H6).
assert(~Col P A B).
apply perp_not_col in H6.
intro.
apply H6.
ColR.
assert(TS PX A P Y).
repeat split.
assumption.
intro.
apply H9.
ColR.
intro.
apply H4.
ColR.
exists T.
split.
apply col_permutation_2.
assumption.
apply between_symmetry.
assumption.
assert(X <> PX).
apply perp_not_eq_2 in H1.
assumption.
assert(P <> PX).
apply perp_not_eq_2 in H6.
assumption.
assert(HA:= (or_bet_out X PX P)).
induction HA.
assert(TS PX A P X).
repeat split; try assumption.
intro.
apply H9.
ColR.
intro.
apply H3.
ColR.
exists PX.
split.
apply col_trivial_1.
apply between_symmetry.
assumption.
eapply l9_8_1.
apply l9_2.
eapply (col_two_sides _ PX).
apply col_permutation_5.
assumption.
assumption.
apply invert_two_sides.
apply H14.
eapply (col_two_sides _ PX).
apply col_permutation_5.
assumption.
assumption.
apply invert_two_sides.
apply l9_2.
assumption.
induction H13.
assert(TS A B P Y).
eapply (col_two_sides _ PX).
Col.
assumption.
apply  invert_two_sides.
assumption.
assert(HO:= out_two_sides_two_sides A B X Y P PX (sym_not_eq H0) H2 H13 H14).
contradiction.
apply col_permutation_1 in HH.
contradiction.
Qed.

Lemma upper_dim_implies_not_two_sides_one_side :
  upper_dim_axiom ->
  (forall A B X Y,
   A <> B ->
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ TS A B X Y ->
   OS A B X Y).
Proof.
    intro HUD; intros.
    assert(exists PX, Col A B PX /\ Perp A B X PX).
      apply l8_18_existence.
      intro.
      apply H0.
      apply col_permutation_2.
      assumption.
    ex_and H3 PX.
    induction(eq_dec_points PX A).
      subst PX.
      apply invert_one_side.
      eapply (upper_dim_implies_not_two_sides_one_side_aux HUD _ _ _ _ A); auto.
        apply perp_left_comm.
        assumption.
        Col.
        intro.
        apply H0.
        Col.
        intro.
        apply H1.
        Col.
      intro.
      apply H2.
      apply invert_two_sides.
      assumption.
    apply (upper_dim_implies_not_two_sides_one_side_aux HUD _ _ _ _ PX); auto.
Qed.

(* TODO cleanup the proof *)

Lemma l8_21_bis : forall A B C X Y, A <> B -> X <> Y ->  ~Col C A B -> exists P T : Tpoint, Cong A P X Y /\ Perp A B P A /\ Col A B T /\ TS A B C P.
Proof.
intros.
assert(HH:= l8_21 A B C H).
ex_and HH P.
ex_and H2 T.

assert(TS A B C P).
unfold TS.
repeat split; auto.
intro.
apply perp_not_col in H2.
apply H2.
Col.
exists T.
split; Col.
assert(P <> A).
apply perp_distinct in H2.
tauto.

assert(HH:= segment_construction_2 P A X Y H6).
ex_and HH P'.
exists P'.
exists T.

assert(Perp A B P' A).
apply perp_sym.
apply perp_left_comm.
apply (perp_col _ P).
intro.
subst P'.
apply cong_symmetry in H8.
apply cong_identity in H8.
contradiction.
Perp.
induction H7.

apply bet_col in H7.
Col.
apply bet_col in H7.
Col.

repeat split;auto.
apply perp_not_col in H9.
intro.
apply H9.
Col.

assert(OS A B P P').
apply out_one_side.
left.
apply perp_not_col in H2.
assumption.
repeat split; auto.
apply perp_distinct in H9.
tauto.
assert(TS A B C P').
apply l9_2.
apply(l9_8_2 A B P P' C); auto.
apply l9_2.
assumption.
unfold TS in H11.
spliter.
ex_and H14 T'.
exists T'.
split; auto.
Qed.

(* TODO cleanup the proof *)

Lemma upper_dim_implies_two_sides_dec :
  upper_dim_axiom ->
  (forall A B C D, TS A B C D \/ ~ TS A B C D).
Proof.
    intro HUD; intros.
    elim (Col_dec C A B); intro HCol1.
      right.
      intro H.
      destruct H as [C' [Hts1 Hts2]].
      unfold TS in *.
      intuition.
    elim (Col_dec D A B); intro HCol2.
      right.
      intro H.
      destruct H as [C' [Hts1 Hts2]].
      unfold TS in *.
      intuition.


assert( exists X : Tpoint, Col A B X /\ Perp A B D X).
apply(l8_18_existence A B D); Col.
ex_and H D'.

assert(A <> B).
intro.
subst B.
apply HCol1.
Col.

induction(eq_dec_points D' B).
subst D'.




assert(exists P T : Tpoint,
       Cong B P B D /\ Perp B A P B /\ Col B A T /\ TS B A C P).
apply(l8_21_bis B A C B D); auto.
intro.
subst D.
apply HCol2.
Col.
Col.
ex_and H2 P.
ex_and H3 T.

assert(NPB : P <> B).
intro.
subst P.
apply perp_distinct in H3.
tauto.

assert(Per A B D).
apply perp_in_per.
apply perp_left_comm in H0.
apply perp_perp_in in H0.
Perp.

assert(Per A B P).
apply perp_in_per.
apply perp_perp_in in H3.
Perp.
assert(Col D P B).
apply (upper_dim_implies_per_per_col HUD _ _ A); Perp.

assert(D = P \/ Midpoint B D P).
apply(l7_20 B D P); finish.
apply invert_two_sides in H5.

induction H9.
subst P.
left.
assumption.
right.
intro.
assert(OS A B D P).
apply (l9_8_1 _ _ _ _ C);
apply l9_2;
assumption.

assert(TS A B D P).
repeat split; Col.
intro.
unfold Midpoint in H9.
spliter.
apply bet_col in H9.
apply HCol2.
ColR.
exists B.
unfold Midpoint in H9.
spliter.
split; Col.
apply l9_9 in H12.
contradiction.
(*
assert(TS A B D P).
unfold Midpoint in H10.
spliter.
repeat split; Col.
apply per_not_col in H8.
intro.
apply H8.
Col.
assumption.
intro.
subst P.
apply cong_identity in H11.
subst D.
apply HCol2.
Col.
exists B.
split; Col.
unfold OS.
exists P.
split; auto.
*)
assert(exists P T : Tpoint,
       Cong D' P D' D /\ Perp D' B P D' /\ Col D' B T /\ TS D' B C P).
apply(l8_21_bis D' B C D' D); auto.
intro.
subst D.
apply HCol2.
Col.
intro.
apply HCol1.
ColR.
ex_and H3 P.
ex_and H4 T.

assert(Perp D' B D D').
apply perp_left_comm.
apply(perp_col _ A); Perp.
Col.

assert(Per B D' D).
apply perp_in_per.
apply perp_perp_in in H7.
Perp.

assert(Per B D' P).
apply perp_in_per.
apply perp_perp_in in H4.
Perp.
assert(Col D P D').
apply (upper_dim_implies_per_per_col HUD _ _ B); Perp.
assert(D = P \/ Midpoint D' D P).
apply(l7_20 D' D P); finish.
apply invert_two_sides in H6.

assert(TS A B C P).
apply(col_preserves_two_sides B D' A B C P); Col.

induction H11.
subst P.
left.
assumption.

right.

assert(TS A B D P).
unfold Midpoint in H12.
spliter.
repeat split; Col.
apply per_not_col in H9; auto.
intro.
apply H9.
ColR.
intro.
subst P.
apply cong_symmetry in H3.
apply cong_identity in H3.
subst D'.
apply perp_distinct in H4.
tauto.
unfold Midpoint in H11.
spliter.
exists D'.
split; Col.
intro.
assert(OS A B C D).
apply (l9_8_1 _ _ _ _ P); auto.
apply l9_9 in H14.
contradiction.
Qed.

Lemma upper_dim_implies_not_one_side_two_sides :
  upper_dim_axiom ->
  (forall A B X Y,
   A <> B ->
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ OS A B X Y ->
   TS A B X Y).
Proof.
    intro HUD; intros.
    intros.
    induction(upper_dim_implies_two_sides_dec HUD A B X Y).
      assumption.
    apply upper_dim_implies_not_two_sides_one_side in H3; try assumption.
    contradiction.
Qed.

Lemma upper_dim_implies_one_or_two_sides :
  upper_dim_axiom ->
  (forall A B X Y,
   ~ Col X A B ->
   ~ Col Y A B ->
   TS A B X Y \/ OS A B X Y).
Proof.
intro HUD; intros.
induction(upper_dim_implies_two_sides_dec HUD A B X Y).
left.
assumption.
right.
apply upper_dim_implies_not_two_sides_one_side in H1; try assumption.
intro;subst;Col.
Qed.

Lemma upper_dim_implies_all_coplanar : upper_dim_axiom -> all_coplanar_axiom.
Proof.
intro HUD; unfold all_coplanar_axiom; intros.
elim (Col_dec A B C); Cop; intro HABC.
elim (Col_dec A B D); Cop; intro HABD.
elim (Col_dec A C D); Cop; intro HACD.
elim (upper_dim_implies_one_or_two_sides HUD A B C D); Col;
elim (upper_dim_implies_one_or_two_sides HUD A C B D); Col.

  {
  intros HTS1 HTS2; destruct HTS1 as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]].
  clear Hc1; clear Hc2; clear Hc3; exists I; right; left; assert_cols; Col.
  }

  {
  intros HOS HTS; destruct HTS as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]].
  clear Hc1; clear Hc2; clear Hc3; exists I; left; assert_cols; Col.
  }

  {
  intros HTS HOS; destruct HTS as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]].
  clear Hc1; clear Hc2; clear Hc3; exists I; right; left; assert_cols; Col.
  }

  {
  intros HOS1 HOS2; destruct (l9_31 A B D C) as [Hc1 [Hc2 [Hc3 [I [HCol HBet]]]]];
  try (apply one_side_symmetry; auto); clear Hc1; clear Hc2; clear Hc3;
  exists I; right; right; assert_cols; Col.
  }
Qed.

Lemma cop_per_per_col : forall A X Y Z,
  Coplanar A X Y Z ->  A <> Z -> Per X Z A -> Per Y Z A -> Col X Y Z.
Proof.
intros A X Y Z HC HAZ HPer1 HPer2.
destruct HPer1 as [B' [HMid1 HCong1]]; destruct HPer2 as [B [HMid2 HCong2]]; treat_equalities.
elim (eq_dec_points X Y); intro HXY; treat_equalities; Col.
elim (eq_dec_points X Z); intro HXZ; treat_equalities; Col.
elim (eq_dec_points Y Z); intro HYZ; treat_equalities; Col.
destruct HC as [I HC].
elim HC; clear HC; intro HC; try (elim HC; clear HC);
try (intros HCol1 HCol2); try (intro H; destruct H as [HCol1 HCol2]).

  {
  elim (eq_dec_points X I); intro HXI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with Y Z; unfold Midpoint in *; spliter; Cong).
  elim HCol1; clear HCol1; intro HCol1; try (elim HCol1; clear HCol1; intro HCol1).

    {
    assert (HLe : Le A X B I).
      {
      apply l5_6 with A X A I; Cong.
      apply l6_13_2; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col); Col.
      }
    assert (H := le_bet B I A X HLe); destruct H as [X' [HBet HCong4]]; clear HLe.
    assert (HCong5 : Cong A X' B X).
      {
      apply five_segment with I I X X'; Cong; Between.
      apply l4_3 with A B; Cong; Between.
      apply l4_3 with B A; Cong; Between.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; eCong.
      apply l4_3 with A B; Cong; Between.
      }
    assert (H : A = B) by (apply construction_unicity with I X X A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := segment_construction B I I X); destruct H as [X' [HBet HCong4]].
    assert (HCong5 : Cong A X' B X).
      {
      apply five_segment with X X' I I; Cong; Between.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; eCong.
      }
    assert (H : A = B) by (apply construction_unicity with X I I A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := segment_construction I B A X); destruct H as [X' [HBet HCong4]].
    assert (HCong5 : Cong X B X' A).
      {
      apply five_segment with I I A B; Cong; intro; treat_equalities; Col.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; eCong; apply l2_11 with A B; Cong.
      }
    assert (H : A = B) by (apply between_cong_2 with I X; Col).
    treat_equalities; intuition.
    }
  }

  {
  elim (eq_dec_points Y I); intro HYI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with X Z; unfold Midpoint in *; spliter; Cong).
  elim HCol1; clear HCol1; intro HCol1; try (elim HCol1; clear HCol1; intro HCol1).

    {
    assert (HLe : Le A Y B I).
      {
      apply l5_6 with A Y A I; Cong.
      apply l6_13_2; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col); Col.
      }
    assert (H := le_bet B I A Y HLe); destruct H as [Y' [HBet HCong4]]; clear HLe.
    assert (HCong5 : Cong A Y' B Y).
      {
      apply five_segment with I I Y Y'; Cong; Between.
      apply l4_3 with A B; Cong; Between.
      apply l4_3 with B A; Cong; Between.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; eCong.
      apply l4_3 with A B; Cong; Between.
      }
    assert (H : A = B) by (apply construction_unicity with I Y Y A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := segment_construction B I I Y); destruct H as [Y' [HBet HCong4]].
    assert (HCong5 : Cong A Y' B Y).
      {
      apply five_segment with Y Y' I I; Cong; Between.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; eCong.
      }
    assert (H : A = B) by (apply construction_unicity with Y I I A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := segment_construction I B A Y); destruct H as [Y' [HBet HCong4]].
    assert (HCong5 : Cong Y B Y' A).
      {
      apply five_segment with I I A B; Cong; intro; treat_equalities; Col.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; eCong; apply l2_11 with A B; Cong.
      }
    assert (H : A = B) by (apply between_cong_2 with I Y; Col).
    treat_equalities; intuition.
    }
  }

  {
  elim (eq_dec_points Z I); intro HZI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with X Y; unfold Midpoint in *; spliter; Cong).
  assert (H := l7_20 I A B). elim H; clear H; try intro H;
  treat_equalities; assert_diffs; assert_cols; try ColR; Cong; intuition.
  }
Qed.

Lemma all_coplanar_implies_upper_dim : all_coplanar_axiom -> upper_dim_axiom.
Proof.
intro HUD; unfold upper_dim_axiom; intros.
destruct (midpoint_existence P Q) as [M HMid].
assert (Per A M P) by (exists Q; Cong).
assert (Per B M P) by (exists Q; Cong).
assert (Per C M P) by (exists Q; Cong).
elim (eq_dec_points A M); intro HAM; treat_equalities;
[assert (HCol : Col B C A) by (apply cop_per_per_col with P; try apply HUD; assert_diffs; auto)|];
try (elim HCol; clear HCol; intro HCol; Between; elim HCol; clear HCol; intro HCol; Between).
assert (Col A B M) by (apply cop_per_per_col with P; try apply HUD; assert_diffs; auto).
assert (Col A C M) by (apply cop_per_per_col with P; try apply HUD; assert_diffs; auto).
assert (HCol : Col A B C) by ColR.
elim HCol; clear HCol; intro HCol; Between; elim HCol; clear HCol; intro HCol; Between.
Qed.

Lemma all_coplanar_upper_dim : all_coplanar_axiom <-> upper_dim_axiom.
Proof.
split;
try apply all_coplanar_implies_upper_dim;
apply upper_dim_implies_all_coplanar.
Qed.

End Upper_dim.