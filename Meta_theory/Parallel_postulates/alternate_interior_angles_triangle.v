Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section alternate_interior_angles_postulate_triangle.

Context `{T2D:Tarski_2D}.

Lemma alternate_interior__triangle :
  alternate_interior_angles_postulate ->
  triangle_postulate.
Proof.
intros AIA A B C D E F HTrisuma.
elim(Col_dec A B C); [intro; apply (col_trisuma__bet A B C); auto|intro HNCol].
destruct(ex_conga_ts B C A C B A) as [B1 [HConga HTS]]; Col.
assert (HPar : Par A C B B1)
  by (apply par_left_comm, par_symmetry, l12_21_b; Side; CongA).
apply (par_not_col_strict _ _ _ _ B) in HPar; Col.
assert (HNCol1 : ~ Col C B B1) by (apply (par_not_col A C); Col).
assert (HNCol2 : ~ Col A B B1) by (apply (par_not_col A C); Col).
destruct (symmetric_point_construction B1 B) as [B2 [HBet HCong]]; assert_diffs.
assert (HTS1 : TS B A B1 B2)
  by (repeat split; Col; [intro; apply HNCol2; ColR|exists B; Col]).
assert (HTS2 : TS B A C B2)
  by (apply (l9_8_2 _ _ B1); auto; apply os_ts1324__os; Side).
apply (bet_conga_bet B1 B B2); auto.
destruct HTrisuma as [D1 [E1 [F1 []]]].
apply (suma2__conga D1 E1 F1 C A B); auto.
assert (CongA A B B2 C A B).
  {
  apply conga_left_comm, AIA; Side.
  apply par_symmetry, (par_col_par _ _ _ B1); Col; Par.
  }
apply (conga3_suma__suma B1 B A A B B2 B1 B B2); try (apply conga_refl); auto;
[exists B2; repeat (split; CongA); apply l9_9; auto|].
apply (suma2__conga A B C B C A); auto.
apply (conga3_suma__suma A B C C B B1 A B B1); CongA.
exists B1; repeat (split; CongA); apply l9_9; Side.
Qed.

(*
Lemma playfair__triangle :
  playfair_s_postulate ->
  triangle_postulate.
Proof.
intros HP A B C D E F HTrisuma.
elim(Col_dec A B C); [intro; apply (col_trisuma__bet A B C); auto|intro HNCol].
destruct (midpoint_existence B C) as [MBC HMid1].
destruct (symmetric_point_construction A MBC) as [B1 HMid2].
destruct (midpoint_existence A B) as [MAB HMid3].
destruct (symmetric_point_construction C MAB) as [B2 HMid4].
assert (HCong5 : Cong A C B B2)
  by (unfold Midpoint in *; spliter; apply l7_13 with MAB; split; finish).
assert (HCong6 : Cong C A B B1)
  by (unfold Midpoint in *; spliter; apply l7_13 with MBC; split; finish).
assert (HCongA1 : CongA B C A C B B1).
  {
  unfold Midpoint in *; spliter; assert_diffs; apply l11_10 with MBC A MBC B1;
  destruct (l11_51 A MBC C B1 MBC B) as [_ [_ HC]]; finish; try repeat split;
  try (intro; treat_equalities; auto); assert_cols; Between; Col.
  }
assert (HCongA2 : CongA B A C A B B2).
  {
  unfold Midpoint in *; spliter; assert_diffs; apply l11_10 with MAB C MAB B2;
  destruct (l11_51 C MAB A B2 MAB B) as [_ [_ HC]]; finish; try repeat split;
  try (intro; treat_equalities; auto); assert_cols; Between; Col.
  }
assert (HPar1 : Par A C B B2) by (apply l12_17 with MAB; assert_diffs; finish).
assert (HPar2 : Par C A B B1) by (apply l12_17 with MBC; assert_diffs; finish).
assert (HTS1 : TS A B B1 B2).
  {
  assert_diffs; assert_cols; apply l9_8_2 with C.

    {
    apply l9_18 with MAB; try repeat split; finish.
    apply par_not_col with A C; try apply par_not_col_strict with B; finish.
    }

    {
    apply one_side_transitivity with MBC;
    [apply l9_19 with B|apply l9_19 with A]; try repeat split; Between; Col;
    intro; treat_equalities; Col; apply HNCol; ColR.
    }
  }
assert (HTS2 : TS C B A B1).
  {
  assert_diffs; apply l9_18 with MBC; try repeat split; finish.
  apply par_not_col with A C; try apply par_not_col_strict with B; finish.
  }
assert (HBet : Bet B1 B B2).
  {
  destruct (HP A C B B1 B B2 B) as [_ HCol]; finish.
  apply col_two_sides_bet with A; Col; Side.
  }
destruct HTrisuma as [D1 [E1 [F1 []]]].
apply (bet_conga_bet B1 B B2); auto.
apply (suma2__conga D1 E1 F1 C A B); auto.
apply (conga3_suma__suma B1 B A A B B2 B1 B B2); try solve [assert_diffs; CongA;
try (apply l11_10 with MAB B2 C MAB; CongA; repeat split; Between)];
[assert_diffs; exists B2; repeat (split; CongA); Side|].
apply (suma2__conga A B C B C A); auto.
assert_diffs; exists B1; repeat (split; CongA); Side.
Qed.
*)

End alternate_interior_angles_postulate_triangle.