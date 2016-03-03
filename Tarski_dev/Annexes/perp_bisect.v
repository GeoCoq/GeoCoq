Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity_2D.

Section PerpBisect_1.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

(** PQ is the perpendicular bisector of segment AB *)

Definition Perp_bisect P Q A B :=
  ReflectL A B P Q /\ A <> B.

Definition Perp_bisect_bis P Q A B :=
  exists I, Perp_at I P Q A B /\ Midpoint I A B.

Lemma perp_bisect_equiv_def :
  forall P Q A B, Perp_bisect P Q A B <-> Perp_bisect_bis P Q A B.
Proof.
intros; unfold Perp_bisect; unfold Perp_bisect_bis; unfold ReflectL; split.

  {
  intro H; destruct H as [[[X [HMid HCol]] HPerp] HDiff].
  exists X; split; Midpoint.
  elim HPerp; clear HPerp; intro HPerp; intuition.
  apply l8_14_2_1b_bis; assert_cols; Col; Perp.
  }

  {
  intro H; destruct H as [I [HPerp HMid]].
  assert_diffs; split; Col.
  split; try (left; apply l8_14_2_1a with I); Perp.
  exists I; split; Midpoint.
  unfold Perp_at in *; spliter; Col.
  }
Qed.

Lemma perp_bisect_sym_1 :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp_bisect Q P A B.
Proof.
intros.
apply perp_bisect_equiv_def in H.
apply perp_bisect_equiv_def.
unfold Perp_bisect_bis in *.
elim H;intros.
exists x.
intuition; Perp.
Qed.

Lemma perp_bisect_sym_2 :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp_bisect P Q B A.
Proof.
intros.
apply perp_bisect_equiv_def in H.
apply perp_bisect_equiv_def.
unfold Perp_bisect_bis in *.
elim H;intros.
exists x.
intuition; Perp.
Qed.

Lemma perp_bisect_sym_3 : forall A B C D,
 Perp_bisect A B C D ->
 Perp_bisect B A D C.
Proof.
intros.
apply perp_bisect_sym_1.
apply perp_bisect_sym_2.
trivial.
Qed.

Lemma perp_in_per_1 :
 forall A B C D X,
  Perp_at X A B C D ->
  Per A X C.
Proof.
intros.
unfold Perp_at in *.
decompose [and] H.
apply H5;
Col.
Qed.

Lemma perp_in_per_2 :
 forall A B C D X,
  Perp_at X A B C D ->
  Per A X D.
Proof.
intros.
unfold Perp_at in *.
decompose [and] H.
apply H5;
Col.
Qed.

Lemma perp_in_per_3 :
 forall A B C D X,
  Perp_at X A B C D ->
  Per B X C.
Proof.
intros.
unfold Perp_at in *.
decompose [and] H.
apply H5;
Col.
Qed.

Lemma perp_in_per_4 :
 forall A B C D X,
  Perp_at X A B C D ->
  Per B X D.
Proof.
intros.
unfold Perp_at in *.
decompose [and] H.
apply H5;
Col.
Qed.

Lemma perp_bisect_perp :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp P Q A B.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold Perp_bisect_bis in *.
decompose [and ex] H;clear H.
unfold Perp.
exists x.
assumption.
Qed.

End PerpBisect_1.

Hint Resolve perp_in_per_1 perp_in_per_2 perp_in_per_3 perp_in_per_4 : perp.

Hint Resolve perp_bisect_perp : Perp_bisect.

Section PerpBisect_2.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma perp_bisect_cong_1 :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A P B P.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold Perp_bisect_bis in *.
elim H;intros I;intros;clear H.
decompose [and] H0;clear H0.
assert (Cong P A P B).
apply (per_double_cong P I A B);
eauto with perp.
Cong.
Qed.

Lemma perp_bisect_cong_2 :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A Q B Q.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold Perp_bisect_bis in *.
elim H;intros I;intros;clear H.
decompose [and] H0;clear H0.
assert (Cong Q A Q B).
apply (per_double_cong Q I A B);
eauto with perp.
Cong.
Qed.

End PerpBisect_2.

Hint Resolve perp_bisect_cong_1 perp_bisect_cong_2 : Perp_bisect.

Section PerpBisect_3.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma perp_bisect_cong :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A P B P /\ Cong A Q B Q.
Proof.
intros.
split.
eauto using perp_bisect_cong_1.
eauto using perp_bisect_cong_2.
Qed.

Lemma perp_bisect_conc :
 forall A A1 B B1 C C1 O: Tpoint,
 ~ Col A B C ->
 Perp_bisect O A1 B C -> Perp_bisect O B1 A C -> Perp_bisect O C1 A B ->
 Cong A O B O -> Cong B O C O ->
 Cong A O C O.
Proof.
intros.
apply (cong_transitivity A O B O C O); assumption.
Qed.

(* TODO add coplanar:not true in 3D *)
Lemma cong_perp_bisect :
 forall P Q A B,
 P <> Q -> A <> B ->
 Cong A P B P ->
 Cong A Q B Q ->
 Perp_bisect P Q A B.
Proof.
intros.
apply perp_bisect_equiv_def.
unfold Perp_bisect_bis.
elim (midpoint_existence A B).
intros I HI.
exists I.
split;try assumption.
assert (Per P I A)
 by (unfold Per;exists B;Cong).

show_distinct A I.
unfold Midpoint in *.
spliter.
treat_equalities.
intuition.

show_distinct B I.
unfold Midpoint in *.
spliter.
treat_equalities.
intuition.

induction(eq_dec_points P I).
subst.
eapply l8_13_2;Col.
exists Q. exists B;repeat split;Col.
unfold Per.
exists A.
split.
Midpoint.
Cong.

eapply l8_13_2.
assumption.
assumption.

apply col_permutation_2.
apply per_per_col with A; Col.
exists B; split; Cong.

apply midpoint_col;auto.
exists P.
exists A.
repeat split;Col.
Qed.

Definition Is_on_perp_bisect P A B := Cong A P P B.

Lemma perp_bisect_is_on_perp_bisect :
 forall A B C P,
  Is_on_perp_bisect P A B ->
  Is_on_perp_bisect P B C ->
  Is_on_perp_bisect P A C.
Proof.
intros.
unfold Is_on_perp_bisect in *.
eCong.
Qed.

Lemma perp_mid_perp_bisect : forall A B C D,
 Midpoint C A B -> Perp C D A B ->
 Perp_bisect C D A B.
Proof with finish.
intros.
apply perp_bisect_equiv_def.
unfold Perp_bisect_bis in *.
exists C...
split...
assert_cols; apply l8_14_2_1b_bis...
Qed.

Lemma cong_perp_bisect_col : forall A B C D E,
  Cong C D C E ->
  Perp_bisect A B D E ->
  Col A B C.
Proof.
intros A B C D E HCong1 HPerp.
assert (HCong2 := HPerp); apply perp_bisect_cong in HCong2; destruct HCong2 as [HCong2 Hc]; clear Hc.
apply perp_bisect_equiv_def in HPerp.
destruct HPerp as [F [HPerp [HBet HCong3]]].
assert (HDE : D <> E) by (assert_diffs; auto).
assert (HCol := HPerp); apply perp_in_col in HCol; destruct HCol as [HCol Hc]; clear Hc.
apply l8_14_2_1a in HPerp.
elim (eq_dec_points A C); intro; try (subst; Col).
apply perp_perp_col with D E; Perp. apply perp_bisect_perp; apply cong_perp_bisect; Cong.
Qed.

End PerpBisect_3.
