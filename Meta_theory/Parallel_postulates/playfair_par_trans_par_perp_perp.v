Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section playfair_par_trans_par_perp_perp.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

(** This is Legendre theorem XXV http://gallica.bnf.fr/ark:/12148/bpt6k202689z/f29.image *)

Lemma playfair_implies_par_trans :
  playfair_s_postulate -> postulate_of_transitivity_of_parallelism.
Proof.
intros HP A1; intros.
apply par_distincts in H.
apply par_distincts in H0.
spliter.
induction (Col_dec A1 A2 C1).

  right.
  assert (Col A1 C1 C2 /\ Col A2 C1 C2) by (apply (HP B1 B2 C1 C2 A1 A2 C1);Par;Col;apply par_symmetry;assumption).
  intuition.

  left.
  repeat split; try assumption; try apply all_coplanar.
  intro HX.
  ex_and HX X.
  assert (Col C1 A1 A2 /\ Col C2 A1 A2) by (apply (HP B1 B2 A1 A2 C1 C2 X);Par;Col;apply par_symmetry;assumption).
  intuition.
Qed.

Lemma playfair_implies_par_perp_perp :
  playfair_s_postulate ->
  perpendicular_transversal_postulate.
Proof.
intros HP A B C D P Q HPar1 HPerp1.
assert (H := HPerp1); destruct H as [X HX];
apply perp_in_col in HX; destruct HX as [HCol1 HCol2].
elim (line_dec A B C D); intro HCol;
try (destruct HCol as [HCol3 HCol4]; apply par_distinct in HPar1; spliter;
     assert_diffs; apply perp_sym; apply perp_col0 with A B; Col).
assert (H : Par_strict A B C D); try (clear HPar1; clear HCol; rename H into HPar1).
  {
  elim HPar1; Col; intro; spliter; exfalso; apply HCol; assert_diffs; split; ColR.
  }
destruct (l8_18_existence C D X) as [Y [HCol3 HPerp2]];
try (intro; apply HPar1; exists X; Col).
elim (line_dec P Q X Y); intro HCol;
try (destruct HCol as [HCol4 HCol5]; assert_diffs;
     apply perp_col0 with X Y; Perp; ColR).
assert (H : ~ Col P Q Y) by (intro; apply HCol; Col); clear HCol.
assert (HR : exists R, Col P Q R /\ ~ Col R X Y /\ ~ Col C D R).
  {
  assert (HR : exists R, Col P Q R /\ ~ Col R X Y).
    {
    assert (HR : exists R, Col P Q R /\ R <> X).
      {
      induction (eq_dec_points P X); [|exists P; Col]; induction (eq_dec_points Q X);
      treat_equalities; [exfalso; apply H; Col| exists Q; Col].
      }
    destruct HR as [R [HCol4 HDiff]]; exists R; split;
    Col; intro; assert_diffs; assert_cols; apply H; ColR.
    }
  destruct HR as [R [HCol4 HNC]]; induction (Col_dec C D R); [|exists R; Col].
  destruct (symmetric_point_construction R X) as [R' HR']; exists R';
  assert_diffs; assert_cols; split; try ColR; split; intro;
  [apply HNC|apply HPar1; exists X; split]; ColR.
  }
clear H; destruct HR as [R [HCol4 [HNC1 HNC2]]].
destruct (l8_18_existence C D R) as [Z [HCol5 HPerp3]]; Col.
destruct (midpoint_existence X Z) as [T HMid1].
destruct (symmetric_point_construction Y T) as [W HMid2].
assert (H : Cong W X Y Z /\ Cong W Z Y X /\ Par W X Y Z /\ Par W Z Y X).
  {
  do 3 (split; try apply l7_13 with T; try apply l12_17 with T; Midpoint);
  try (intro; treat_equalities; Col); try (apply HNC1; apply col_permutation_1;
                                           apply perp_perp_col with C D; Perp).
  }
destruct H as [HCong1 [HCong2 [HPar2 HPar3]]].
assert (HCol6 : Col A B W).
  {
  destruct (HP C D A B X W X) as [H1 H2]; Col;
  [apply par_strict_par|apply par_symmetry; apply par_col2_par with Y Z];
  assert_diffs; assert_cols; Par; ColR.
  }
assert (HCol7 : Col R W Z).
  {
  destruct (HP X Y W Z R Z Z) as [H1 H2]; Col; Par; apply l12_9 with C D; Perp.
  }
destruct (symmetric_point_construction W X) as [W' HMid3].
destruct (symmetric_point_construction R X) as [R' HMid4].
assert (HNC3 : ~ Col C D W').
  {
  apply par_distincts in HPar2; intro; apply HPar1; exists W';
  spliter; assert_diffs; assert_cols; split; ColR.
  }
destruct (l8_18_existence C D W') as [Z' [HCol8 HPerp4]]; Col.
assert (H : Cong W R W' R' /\ Par W R W' R' /\ Par W R' W' R).
  {
  do 2 (split; try apply l7_13 with X; try apply l12_17 with X; Midpoint);
  try (intro; treat_equalities; assert_diffs; assert_cols);
  [elim (eq_dec_points X W)|elim (eq_dec_points X W')]; try intro HDiff;
  treat_equalities; Col; try apply HDiff; try (elim (perp_not_col2 A B P Q);
  try intro; Col; try (apply l6_21 with A B Q P; Col; ColR);
  apply l6_21 with A B P Q; Col; ColR).
  }
destruct H as [HCong3 [HPar4 HPar5]].
assert (HCol9 : Col R' W' Z').
  {
  destruct (HP R W R' W' W' Z' W') as [H1 H2]; Col; Par.
  apply l12_9 with C D; Perp.
 apply perp_col2 with R Z; Col; Perp; try intro;
  treat_equalities.
 apply par_distincts in HPar4; intuition.
  }
destruct (midpoint_existence W' Y) as [T' HMid6].
destruct (symmetric_point_construction Z' T') as [X' HMid7].
assert (HYZ' : Y <> Z').
  {
  intro; treat_equalities.
  assert (X = X'); treat_equalities.
    {
    assert (Col Y X X') by (apply perp_perp_col with C D; Perp).
    assert_diffs; assert_cols; apply l6_21 with X Y A B; Col;
    try (intro; apply HNC1; ColR).
    induction (eq_dec_points X W); Col; ColR.
    }
  apply par_distincts in HPar2; intuition.
  }
assert (H : Cong Y Z' W' X' /\ Cong Y X' W' Z' /\ Par Y Z' W' X' /\ Par Y X' W' Z').
  {
  do 3 (split; try apply l7_13 with T'; try apply l12_17 with T'; Midpoint);
  intro; treat_equalities; Col.
  }
destruct H as [HCong4 [HCong5 [HPar6 HPar7]]].
assert (X = X'); treat_equalities.
  {
  assert (Col X X' Y).
    {
    destruct (HP W' Z' Y X' X Y Y); Col; Par;
    apply l12_9 with C D; Perp.
    }
  assert (X <> W') by (intro; treat_equalities; apply par_distincts in HPar2; intuition).
  assert (Col X X' W').
    {
    destruct (HP Y Z' W' X' X W' W'); Col; assert_diffs; assert_cols; Par.
    apply par_col2_par with A B; Col; try ColR;
    apply par_symmetry; apply par_col2_par with C D; Col;
    apply par_strict_par; Par.
    }
  assert_diffs; assert_cols; apply l6_21 with X Y W' X'; Col;
  intro; apply HPar1; exists Y; split; ColR.
  }
destruct (l10_2_existence X Y R') as [R'' HR''].
elim HR''; clear HR''; intro HR''; destruct HR'' as [H HR''];
[clear H|treat_equalities; apply par_distincts in HPar3; intuition].
unfold ReflectL in HR''.
destruct HR'' as [[I [HMid5 HCol10]] H]; elim H; clear H; intro HPerp5;
[|treat_equalities; exfalso; apply HNC1; assert_diffs; assert_cols; ColR].
destruct (midpoint_existence R' Y) as [T'' HMid8].
destruct (symmetric_point_construction Z' T'') as [I' HMid9].
assert (I = I'); treat_equalities.
  {
  elim (eq_dec_points I' Y); intro HI'Y; treat_equalities.

    {
    assert (Col C D I).
      {
      induction (eq_dec_points C R'); treat_equalities; assert_diffs; assert_cols;
      [assert (Col C D R'')|assert (Col R' C R'')]; try ColR;
      apply perp_perp_col with X I'; Perp; apply perp_col2 with C D; Col.
      }
    apply l6_21 with C D X I; Col; intro; treat_equalities; apply HPar1; exists X; Col.
    }

    {
    assert (H : Cong Y Z' R' I' /\ Cong Y I' R' Z' /\ Par Y Z' R' I' /\ Par Y I' R' Z')
      by (do 3 (split; try apply l7_13 with T''; try apply l12_17 with T''; Midpoint)).
    destruct H as [H1 [H2 [H3 H4]]].
    assert (Col I I' R').
      {
      destruct (HP Y Z' R' I R' I' R'); Col.
      apply l12_9 with X Y; assert_diffs; assert_cols;
      [apply perp_col2 with C D|apply perp_col2 with R' R'']; Col; Perp.
      }
    assert (HDiff : R' <> Z') by (intro; treat_equalities; apply HI'Y; Col).
    assert (Col I I' Y).
      {
      destruct (HP R' Z' Y I Y I' Y); Col; Par.
      apply l12_9 with C D; assert_diffs; assert_cols;
      [apply perp_col2 with W' Z'|apply perp_col2 with X Y]; Col; Perp.
      intro; treat_equalities; apply HDiff.
      assert_diffs; assert_cols; apply l6_21 with Y Z' W' Z'; Col;
      try (intro; apply HNC3; ColR); apply perp_perp_col with X Y;
      [apply perp_col2 with C D|apply perp_col2 with R' R'']; Col; Perp.
      }
    apply l6_21 with I' Y R' I'; Col; intro; treat_equalities; Col.
    assert_diffs; assert_cols; apply HNC1; show_distinct I Y; try ColR.
    elim H4; clear H4; intro H4; [apply H4; exists R'; Col|].
    spliter; apply HDiff; apply l6_21 with Z' W' I Z'; Col; intro; apply HNC3; ColR.
    }
  }
assert (HCong7 : Cong I R' Y Z').
  {
  induction (eq_dec_points I Y); treat_equalities; Cong.
  assert (Cong I R' Z' Y); Cong; apply l7_13 with T''; Midpoint.
  }
destruct (midpoint_existence I Z) as [T''' HMid10].
destruct (symmetric_point_construction Y T''') as [R''' HMid11].
assert (R'' = R'''); treat_equalities.
  {
  elim (eq_dec_points R''' Z); intro HR'''Z; treat_equalities.

    {
    assert (Col C D R'').
      {
      induction (eq_dec_points C R'); treat_equalities; assert_diffs; assert_cols;
      [assert (Col C D R'')|assert (Col R' C R'')]; try ColR;
      apply perp_perp_col with X I'; Perp; apply perp_col2 with C D; Col.
      }
    elim (l7_20 I R'' R'''); try (assert_diffs; ColR);
    try intro; treat_equalities; Col;
    assert (Cong I R'' I R') by (unfold Midpoint in *; spliter; eCong);
    assert (Cong I R'' X W') by (unfold Midpoint in *; spliter; eCong);
    assert (Cong I R'' X W) by (unfold Midpoint in *; spliter; eCong); eCong.
    }

    {
    assert (H : Cong Z Y I R''' /\ Cong Z R''' I Y /\ Par Z Y I R''' /\ Par Z R''' I Y).
      {
      do 3 (split; try apply l7_13 with T'''; try apply l12_17 with T''';
            try intro; treat_equalities; Midpoint).
      }
    destruct H as [H1 [H2 [H3 H4]]].
    assert (Col R'' R''' I).
      {
      destruct (HP Z Y R'' I R''' I I); Col; Par.
      apply l12_9 with X Y; assert_diffs; assert_cols;
      [apply perp_col2 with C D|apply perp_col2 with R' R'']; Col; Perp.
      }
    elim (l7_20 I R'' R'''); try (intro; treat_equalities); Col.
    assert (Cong I R'' I R') by (unfold Midpoint in *; spliter; eCong).
    assert (Cong I R'' Y Z') by (unfold Midpoint in *; spliter; eCong).
    assert (Cong I R'' X W') by (unfold Midpoint in *; spliter; eCong).
    assert (Cong I R'' X W) by (unfold Midpoint in *; spliter; eCong).
    assert (Cong I R'' Y Z) by (unfold Midpoint in *; spliter; eCong); eCong.
    }
  }
assert (HCong8 : Cong I Y R'' Z).
  {
  induction (eq_dec_points I Y); treat_equalities; Cong.
  assert (Cong Y I R'' Z); Cong; apply l7_13 with T'''; Midpoint.
  }
assert (HPar8 : Par W W' R' R'').
  {
  assert (HTP := playfair_implies_par_trans HP); apply HTP with C D;
  [apply par_symmetry; apply par_col2_par with A B; try apply par_strict_par|];
  assert_diffs; assert_cols; Col; Par; try ColR; elim (eq_dec_points I Y); intro HIY;
  treat_equalities.

    {
    right; assert_diffs; assert_cols; repeat (split; Col; try ColR).
    }

    {
    assert_diffs; assert_cols; apply par_col2_par with I R''; Col.
    apply par_symmetry; apply par_col2_par with Y Z; Col; try ColR.
    assert (Par Y Z R'' I); Par; apply l12_17 with T'''; Midpoint.
    }
  }
assert (HRWR'' : Bet R W R'').
  {
  assert (HCol : Col R R'' Z).
    {
    induction (eq_dec_points I Y); treat_equalities; Col.
    destruct (HP I Y R'' Z R Z Z); Col;
    [assert (Par Y I R'' Z); Par; apply l12_17 with T'''; Midpoint|].
    apply par_col2_par with W Z; try (intro; treat_equalities; assert_diffs); Col.
    apply par_symmetry; apply par_col2_par with X Y; Col; Par.
    }
  assert (HNC : ~ Col R W X).
    {
    assert (H : R <> X) by (assert_diffs; Col); intro; apply H.
    elim (perp_not_col2 A B P Q); Col; intro; assert_diffs; assert_cols;
    [apply l6_21 with A B P Q|apply l6_21 with A B Q P]; Col; ColR.
    }
  assert (HTS : TS W X R R'').
    {
    assert (HWX : W <> X)
      by (intro; treat_equalities; apply par_distinct in HPar6; intuition).
    apply l9_2; apply l9_8_2 with R'; assert_diffs; assert_cols;
    try (apply l12_6; apply par_not_col_strict with R'; Col);
    try (intro; apply HNC; ColR);
    try (apply par_symmetry; apply par_col2_par with W W'; Col; Par).
    split; Col.
    assert_diffs; assert_cols; split; try (intro; apply HNC; ColR).
    split; Col; exists X; unfold Midpoint in *; spliter; split; Col; Between.
    }
  destruct HTS as [Hc1 [Hc2 [Hc3 [W'' [HCol' HBet]]]]];
  clear Hc1; clear Hc2; clear Hc3.
  assert (W = W''); treat_equalities; Col.
    {
    assert (R <> R'') by (intro; treat_equalities; Col).
    assert_diffs; assert_cols; apply l6_21 with W X R W; Col; ColR.
    }
  }
assert (HCong9 : Cong R W R'' W).
  {
  assert (HElim : Col W R'' Z).
    {
    induction (eq_dec_points R W); treat_equalities; Col;
    induction (eq_dec_points R'' W); treat_equalities; Col; assert_cols; ColR.
    }
  elim (eq_dec_points R'' Z); intro HR''Z; treat_equalities; [eCong|].
  assert (Cong W R'' W' R'); [|eCong].
  assert (HNC4 : ~ Col R' R'' X).
    {
    assert (H : R' <> X) by (assert_diffs; Col).
    intro; apply H; apply l6_21 with R' R'' X R;
    assert_diffs; assert_cols; Col;
    intro; apply (perp_not_col I R' X); try ColR.
    apply perp_col2 with R' R''; Col; apply perp_sym;
    apply perp_col2 with X Y; Col; intro;
    treat_equalities; apply par_distincts in HPar4; intuition.
    }
  assert (HParS1 : Par_strict R' R'' W W')
    by (apply par_not_col_strict with X; assert_cols; Col; Par).
  assert (HParS2 : Par_strict Z Z' W W').
    {
    assert (HZZ': Z <> Z') by (intro; treat_equalities; Col).
    apply par_not_col_strict with W'; Col;
    try (intro; assert_diffs; apply HNC3; ColR).
    apply par_col2_par with A B; assert_diffs; assert_cols;
    try (intro; treat_equalities); Col; try ColR; apply par_symmetry;
    apply par_col2_par with C D; Col; apply par_strict_par; Par.
    }
  assert (HIY : I <> Y) by (assert_diffs; Col).
  assert (HParS3 : Par_strict R' R'' Z Z').
    {
    apply par_not_col_strict with Y; assert (HTP := playfair_implies_par_trans HP);
    try apply HTP with W W'; try apply par_strict_par; Par; assert_diffs; assert_cols;
    try ColR; intro; apply HIY; apply l6_21 with R' R'' I Y; Col.
    intro; apply (perp_not_col I R' X); try ColR.
    apply perp_col2 with R' R''; Col; apply perp_sym;
    apply perp_col2 with X Y; Col; intro;
    treat_equalities; apply par_distincts in HPar4; intuition.
    }
  elim (HElim); clear HElim; intro HElim;
  try (elim (HElim); clear HElim; intro HElim).

    {
    apply l4_3 with Z Z'; eCong.
    assert (HTS : TS R' R'' W' Z').
      {
      assert (HR'R' : R' <> R'') by (intro; assert_diffs; Col).
      apply l9_2; apply l9_8_2 with Z; try apply l12_6; Par.
      apply l9_2; apply l9_8_2 with W; try apply l12_6; Par.
      split; Col.
      split; try (intro; apply HParS1; exists W; Col).
      split; try (intro; apply HParS3; exists Z; Col); exists R''; Col.
      }
    destruct HTS as [Hc1 [Hc2 [Hc3 [R''' [HCol HBet]]]]];
    clear Hc1; clear Hc2; clear Hc3.
    assert (R' = R'''); treat_equalities; Col.
      {
      assert_diffs; assert_cols; apply l6_21 with R' R'' W' Z'; Col;
      intro; apply HParS1; exists W'; Col.
      }
    }

    {
    apply l2_11 with Z Z'; Between; eCong.

    assert (HTS : TS Z Z' W' R').
      {
      assert (HR'R' : Z <> Z') by (intro; treat_equalities; assert_diffs; Col).
      apply l9_8_2 with W; try apply l12_6; Par.
      apply l9_2; apply l9_8_2 with R''; try apply l12_6; Par.
      split; Col.
      split; try (intro; apply HParS3; exists R''; Col).
      split; try (intro; apply HParS2; exists W; Col); exists Z; Col.
      }
    destruct HTS as [Hc1 [Hc2 [Hc3 [Z''' [HCol HBet]]]]];
    clear Hc1; clear Hc2; clear Hc3.
    assert (Z' = Z'''); treat_equalities; Col.
      {
      assert_diffs; assert_cols; apply l6_21 with Z Z' W' R';
      try (intro; treat_equalities); Col; apply HParS2; exists W'; Col.
      }
    }

    {
    assert (HCong: Cong Z R'' Z' R')
      by (assert (Cong Y I R'' Z) by (apply l7_13 with T'''; Midpoint); eCong).
    assert (Cong R'' W R' W'); Cong; apply l4_3 with Z Z'; Between; eCong.
    assert (HTS : TS W W' R' Z').
      {
      assert (HR'R' : W <> W') by (intro; treat_equalities; assert_diffs; Col).
      apply l9_8_2 with R''; try apply l12_6; Par.
      apply l9_2; apply l9_8_2 with Z; try apply l12_6; Par.
      split; Col.
      split; try (intro; apply HParS2; exists Z; Col).
      split; try (intro; apply HParS1; exists R''; Col); exists W; Col.
      }
    destruct HTS as [Hc1 [Hc2 [Hc3 [W'' [HCol HBet]]]]];
    clear Hc1; clear Hc2; clear Hc3.
    assert (W' = W''); treat_equalities; Col.
      {
      assert_diffs; assert_cols; apply l6_21 with W W' R' Z';
      try (intro; treat_equalities); Col; apply HParS1; exists R'; Col.
      }
    }
  }
assert (HCong10 : Cong R X R'' X).
  {
  assert (Cong R' X R'' X).
    {
    apply perp_bisect_cong_2 with I; apply perp_mid_perp_bisect;
    unfold Midpoint in *; spliter; Between; Cong.
    apply perp_col2 with X Y; Col; intro; treat_equalities.
    destruct (not_strict_par W W' R' R'' I); Col.
    show_distinct W W'; Col; assert_diffs; assert_cols.
    apply perp_not_col2 in HPerp1; elim HPerp1; intro HF; apply HF; ColR.
    }
  unfold Midpoint in *; spliter; eCong.
  }
assert (HPerp6 : Perp X W W R).
  {
  apply per_perp; assert_diffs; Col; try (exists R''; repeat split; Between; Cong);
  intro; treat_equalities; apply par_distincts in HPar4; intuition.
  }
assert (HFalse : Par_strict R W R X).
  {
  apply par_not_col_strict with X; Col; assert_diffs; assert_cols;
  try (intro; elim (perp_not_col2 R W W X); Col; Perp).
  apply l12_9 with A B;
  [apply perp_sym; apply perp_col2 with W X|apply perp_col2 with P Q]; Perp; ColR.
  }
exfalso; apply HFalse; exists R; Col.
Qed.

End playfair_par_trans_par_perp_perp.
