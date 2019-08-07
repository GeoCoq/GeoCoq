Require Export GeoCoq.Highschool.bisector.
Require Export GeoCoq.Tarski_dev.Ch13_1.

Section InCenter.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Definition is_incenter I A B C :=
 ~ Col A B C /\ CongA B A I I A C /\ CongA A B I I B C /\ CongA A C I I C B.

(** Proof of the existence of the incenter of a triangle. *)

Lemma incenter_exists : forall A B C, ~ Col A B C -> exists I, is_incenter I A B C.
Proof.
intros A B C HNCOL.
(*----construction---*)
assert_diffs.
destruct (bisector_existence A B C) as [IB HCONA];auto.
destruct (bisector_existence B A C) as [IA HCONB];auto.
destruct HCONA as [HBINANGLE HCONGAA].
destruct HCONB as [HAINANGLE HCONGBB].
destruct HBINANGLE as [HBAB [HBCB [HBIBB HBEXI]]].
destruct HAINANGLE as [HABA [HACA [HAIAA HAEXI]]].
destruct HAEXI as [XA [HXABET HXAO]].
destruct HBEXI as [XB [HXBBET HXBO]].
assert (HXEXISTS : exists X : Tpoint, Bet XB X B /\ Bet XA X A).
apply (inner_pasch A B C XB XA);assumption.
destruct HXEXISTS as [X [HXBET1 HXBET2]].
destruct HXAO as [HXAEQ | HXAOUT].
subst.
elim HNCOL;ColR.
destruct HXBO as [HXBEQ | HXBOUT].
subst.
elim HNCOL;ColR.
assert (XA <> B) by (intro;subst;assert (Col B A C) by (col_with_conga);Col).
assert (XB <> A) by (intro;subst;elim HNCOL;col_with_conga).
assert (X <> A) by (intro;subst;elim HNCOL;col_with_conga).
assert (X <> B) by (intro;subst;assert (Col B A C) by (col_with_conga);elim HNCOL;Col).
assert (~ Col A B X) by (intro;elim HNCOL;col_with_conga).
assert (~ Col A C X) by (intro;assert (Col C A B) by (col_with_conga);elim HNCOL;Col).
assert (~ Col B C X) by (intro;assert (Col C B A) by (col_with_conga);elim HNCOL;Col).
destruct (l8_18_existence A B X) as [HC [HCC1 HCC2]];auto.
destruct (l8_18_existence A C X) as [HB [HBC1 HBC2]];auto.
destruct (l8_18_existence B C X) as [HA [HAC1 HAC2]];auto.
exists X.
unfold is_incenter.
split.
assumption.
(*-prove some conclusions which will be required later for many times.-*)
assert (Out A X IA) by (assert (Out A X XA) by (assert_diffs;apply (bet_out A X XA);Between);
apply (l6_7 A X XA IA);auto).
assert (Out B X IB) by (assert (Out B X XB) by (assert_diffs;apply (bet_out B X XB);Between);
apply (l6_7 B X XB IB);auto).
assert (CongA B A X X A C).
{ apply (l11_10 B A IA IA A C B X X C);Out.
}
assert (CongA A B X X B C).
{ apply (l11_10 A B IB IB B C A X X C);Out.
}
assert (Coplanar C A B X) by (exists XB; left; split; Col).
assert (Cong X HB X HC) by (apply (bisector_perp_equality C A B X HB HC);Col;Perp;CongA).
assert (Cong X HC X HA) by (apply (bisector_perp_equality A B C X HC HA);Col;Cop).
assert (Cong X HB X HA) by (apply (cong_transitivity X HB X HC X HA);auto).
assert (CongA A C X X C B).
{ 
 apply (perp_equality_bisector A C B X HB HA);Col;Perp.
 assert (InAngle X A B C).
 repeat split;auto.
 exists XB.
 split;auto.
 right.
 apply (l6_6 B X XB);auto.
 apply (bet_out B X XB);auto.
 Between.
 assert (InAngle X B A C).
 assert_diffs.
 repeat split;auto.
 exists XA.
 split;auto.
 right.
 apply (l6_6 A X XA);auto.
 apply (bet_out A X XA);auto.
 Between.
 apply (os2__inangle A C B X).
 apply (one_side_symmetry C A X B).
 apply (in_angle_one_side C A B X);Col.
 apply (l11_24 X B A C);auto.
 apply (one_side_symmetry C B X A).
 apply (in_angle_one_side C B A X);Col.
 apply (l11_24 X A B C);auto.
}
split;auto.
Qed.

Lemma incenter_permut132 : forall A B C I, is_incenter I A B C -> is_incenter I A C B.
Proof.
unfold is_incenter.
intros A B C I HIABC.
destruct HIABC as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
split.
Col.
split;CongA.
Qed.

Lemma incenter_permut213 : forall A B C I, is_incenter I A B C -> is_incenter I B A C.
Proof.
unfold is_incenter.
intros A B C I HIABC.
destruct HIABC as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
split.
intro;Col.
split;auto.
split;CongA.
Qed.

Lemma incenter_permut231 : forall A B C I, is_incenter I A B C -> is_incenter I B C A.
Proof.
intros A B C I HIABC.
apply (incenter_permut132 B A C I).
apply (incenter_permut213 A B C I);auto.
Qed.

Lemma incenter_permut312 : forall A B C I, is_incenter I A B C -> is_incenter I C A B.
Proof.
intros A B C I HIABC.
apply (incenter_permut213 A C B I).
apply (incenter_permut132 A B C I);auto.
Qed.

Lemma incenter_permut321 : forall A B C I, is_incenter I A B C -> is_incenter I C B A.
Proof.
intros A B C I HIABC.
apply (incenter_permut312 B A C I).
apply (incenter_permut213 A B C I);auto.
Qed.

Lemma incenter_dec : forall A B C I, is_incenter I A B C \/ ~ is_incenter I A B C.
Proof.
intros A B C I.
unfold is_incenter.
destruct (col_dec A B C) as [HCOL | HNCOL].
right.
intro HCOLIN.
destruct HCOLIN as [HNCOL [HCONGAA [HCONGAB HCONGAC]]].
elim HNCOL;auto.
destruct (conga_dec B A I I A C) as [HAC | HANC].
destruct (conga_dec A B I I B C) as [HBC | HBNC].
destruct (conga_dec A C I I C B) as [HCC | HCNC].
left;split;auto.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HCNC;auto.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HBNC;CongA.
right;intro HN.
destruct HN as [HNCOL1 [HCONGA [HCONGAB HCONGAC]]].
elim HANC;auto.
Qed.

End InCenter.