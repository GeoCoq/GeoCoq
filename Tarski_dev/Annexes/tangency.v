Require Export GeoCoq.Axioms.elementary_continuity.
Require Export GeoCoq.Tarski_dev.Ch12_parallel.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Export GeoCoq.Tarski_dev.Annexes.circles.

Section Tangency.

Context `{TE:Tarski_2D}.

(** The line AB is tangent to the circle OP *)

Definition Tangent A B O P :=
  exists !X, Col A B X /\ OnCircle X O P.

Definition TangentCC A B C D :=
 exists !X, OnCircle X A B /\ OnCircle X C D.

Definition TangentAt A B O P T := Tangent A B O P /\ Col A B T /\ OnCircle T O P.

(** Euclid Book III, Prop 11 and Prop 12
 We do not need to distinguish between internal or external tangency. *)

(** If two circles are tangent, the common point is on the line joining the centers. *)

Lemma TangentCC_Col : forall A B C D X,
 TangentCC A B C D ->
 OnCircle X A B ->
 OnCircle X C D ->
 Col X A C.
Proof.
intros.

unfold TangentCC in *.

induction(eq_dec_points A C).
subst C.
Col.

assert(HS:=ex_sym1 A C X H2).
ex_and HS Y.
ex_and H4 M.

assert(Cong X A Y A).
apply(is_image_col_cong A C X Y A H2 H6); Col.
assert(Cong X C Y C).
apply(is_image_col_cong A C X Y C H2 H6); Col.

destruct H.
unfold unique in H.

assert(x =X).
apply H.
split; auto.
subst x.
assert(OnCircle Y A B).
unfold OnCircle in *.
eCong.
assert(OnCircle Y C D).
unfold OnCircle in *.
eCong.
assert(X = Y).
apply H.
split; auto.
subst Y.

unfold Reflect in H6.
induction H6.
spliter.
unfold ReflectL in *.
spliter.
ex_and H11 Z.

assert(Z = X).
apply l7_3; auto.
subst Z.
Col.
spliter.
contradiction.
Qed.

Lemma tangent_neq : forall A B O P,
 O<>P -> Tangent A B O P -> A<>B.
Proof.
intros.
intro.
subst B.
unfold Tangent in *.
unfold unique in *.
ex_and H0 T.
assert(HH:=symmetric_point_construction T O).
ex_and HH T'.
assert(OnCircle T' O P).
apply (symmetric_oncircle T T' O P); auto.
assert(T = T').
apply H1.
split; Col.
subst T'.
apply H.
apply l7_3 in H3.
subst T.
unfold OnCircle in H2.
treat_equalities; tauto.
Qed.

(** A line going through the center is not tangent to the circle. *)

Lemma diam_not_tangent : forall O P A B, 
  P <> O -> A <> B -> Col O A B -> ~ Tangent A B O P.
Proof.
intros.
intro.
unfold Tangent in *.
unfold unique in *.
ex_and H2 Q.
induction(eq_dec_points A O).
subst A.
assert(exists Q1 Q2 : Tpoint,
       Q1 <> Q2 /\
       Col O B Q1 /\ Col O B Q2 /\ OnCircle Q1 O P /\ OnCircle Q2 O P).
apply (diam_points O P B);
auto.
ex_and H5 Q1.
ex_and H6 Q2.

assert(Q = Q1).
apply H3; auto.
subst Q.
assert(Q1 = Q2).
apply H3; auto.
contradiction.

assert(exists Q1 Q2 : Tpoint,
       Q1 <> Q2 /\
       Col O A Q1 /\ Col O A Q2 /\ OnCircle Q1 O P /\ OnCircle Q2 O P).
apply (diam_points O P A);
auto.
ex_and H6 Q1.
ex_and H7 Q2.

assert(Q = Q1).
apply H3.
split.
ColR.
auto;
subst Q.
subst Q.
assert(Q1 = Q2).
apply H3.
split.
ColR.
auto.
contradiction.
Qed.


(** Every point on the tangent different from the point of tangency is strictly outside the circle. *)

Lemma tangent_out : forall A B O P T X,
  X <> T -> Col A B X -> TangentAt A B O P T -> OutCircleS X O P.
Proof.
intros.
unfold TangentAt in *.
spliter.

induction(eq_dec_points O P).
subst P.
unfold OutCircleS.
unfold Lt.

split.
apply le_trivial.
intro.
unfold OnCircle in *.
assert(T = O).
eCong.
assert(X = O).
eCong.
subst O.
contradiction.

assert(InCircle X O P -> X = T).
intro.

assert(HH:= chord_completion O P T X H3 H5).
ex_and HH T'.
assert(A <> B).
apply (tangent_neq A B O P); auto.
unfold Tangent in *.
unfold unique in *.
ex_and H1 TT.
assert(TT= T).
apply H9.
split; auto.
subst TT.
assert(T = T').
apply H9.
split; auto.
apply bet_col in H7.

assert(Col A X T); ColR.
subst T'.
apply between_identity in H7.
subst X.
tauto.

assert(~InCircle X O P).
intro.
apply H5 in H6.
contradiction.
apply ninc__outcS.
assumption.
Qed.

(** If line AB is tangent to a circle of center O at a point T, then OT is perpendicular to AB.
This is Euclid Book III, Prop 18 *)

Lemma tangentat_perp : 
forall A B O P T, O <> P -> TangentAt A B O P T -> Perp A B O T.
Proof.
intros.
assert(TA:=H0).
unfold TangentAt in H0.
spliter.
assert(A <> B).
apply (tangent_neq A B O P); auto.
assert(~Col A B O).
intro.
assert(~Tangent A B O P).
apply(diam_not_tangent); Col.
contradiction.

assert(HH:= l8_18_existence A B O H4).
ex_and HH R.

induction(eq_dec_points T R).
subst R.
auto.

assert(HH:= (symmetric_point_construction T R)).
ex_and HH T'.

induction(eq_dec_points A R).
subst A.
assert(Perp T R R O).
apply perp_comm.
apply (perp_col R B O R T); Col.
assert(Perp_at R T R R O).
apply perp_in_comm.
apply perp_perp_in.
Perp.
assert(Per O R T).
apply l8_2.
apply perp_in_per; auto.
unfold Per in *.
ex_and H11 T''.
assert(T' = T'').
apply (symmetric_point_uniqueness T R T' T''); auto.
subst T''.

assert(T <> T').
intro.
subst T'.
apply H7.
apply sym_equal.
apply l7_3; auto.

assert(OnCircle T' O P).
unfold OnCircle in *.
eCong.

assert(OutCircleS T' O P).
apply (tangent_out R B O P T T'); ColR.
unfold OutCircleS in *.
unfold Lt in *.
spliter.
unfold OnCircle in H14.
apply False_ind.
apply H16.
Cong.


assert(Perp T R R O).
apply perp_comm.
apply (perp_col R A O R T); Col.
apply perp_left_comm.
eapply (perp_col A B O R R); auto.
unfold Midpoint in *.
spliter.
apply bet_col in H8.
eCol.
assert(Perp_at R T R R O).
apply perp_in_comm.
apply perp_perp_in.
Perp.


assert(Per O R T).
apply l8_2.
apply perp_in_per; auto.
unfold Per in *.
ex_and H12 T''.
assert(T' = T'').
apply (symmetric_point_uniqueness T R T' T''); auto.
subst T''.

assert(T <> T').
intro.
subst T'.
apply H7.
apply sym_equal.
apply l7_3; auto.

assert(OnCircle T' O P).
unfold OnCircle in *.
eCong.

assert(OutCircleS T' O P).
unfold Midpoint in *.
spliter.
apply bet_col in H12.
apply (tangent_out A B O P T T'); auto.
ColR.
unfold OutCircleS in *.
unfold Lt in *.
spliter.
unfold OnCircle in H14.
apply False_ind.
apply H17.
Cong.
Qed.

(** AB is the tangent of circle (O,P) iff there is a point on the circle
such that AB is perpendicular to OP. *)

Lemma tangency_chara : forall A B O P, P <> O ->
 (exists X, OnCircle X O P /\ Perp_at X A B O X) <-> Tangent A B O P.
Proof.
intros.

split.
intro.
ex_and H0 T.
unfold Tangent.
unfold unique.
exists T.
split.
split; auto.
apply perp_in_col in H1.
tauto.
intros.
spliter.
assert(Col A B T).
apply perp_in_col in H1.
tauto.

induction(eq_dec_points T x').
auto.
apply False_ind.

assert(Perp T x' O T).
apply (perp_col2 A B); auto.
apply perp_in_perp in H1.
auto.

assert(Perp_at T T x' O T).
apply perp_perp_in; auto.

assert(Per x' T O).
apply perp_in_comm in H7.
apply perp_in_per; auto.

assert(~Col x' T O).
apply perp_not_col in H6.
ColR.

assert(Lt T x' x' O /\ Lt T O x' O).
apply(l11_46 x' T O H9).
tauto.
spliter.
unfold OnCircle in *.
unfold Lt in H11.
spliter.
apply H12.
eCong.

intros.
assert(HT:=H0).
unfold Tangent in H0.
unfold unique in H0.
ex_and H0 T.

assert(TangentAt A B O P T).
unfold TangentAt.
repeat split; auto.
exists T.
split; auto.
assert(HH:=tangentat_perp A B O P T).
assert(Perp A B O T).
apply HH; auto.

apply(l8_14_2_1b_bis A B O T T H4); Col.
Qed.


Lemma tangency_chara2 : forall A B O P Q,
 OnCircle Q O P -> Col Q A B -> 
 ((forall X, Col A B X -> X = Q \/ OutCircleS X O P) <-> Tangent A B O P).
Proof.
intros.
split.
intros.
unfold Tangent.
unfold unique.
exists Q.
repeat split; Col.
intros.
spliter.
assert(HH:=(H1 x' H2)).
induction HH.
auto.
unfold OnCircle in *.
unfold OutCircleS in *.
unfold Lt in *.
spliter.
apply False_ind.
apply H5; eCong.

intros.
assert(TangentAt A B O P Q).
unfold TangentAt.
repeat split; Col.

induction(eq_dec_points X Q).
left; auto;

unfold Tangent in H1.
right.

apply(tangent_out A B O P Q X); auto.
Qed.


Lemma tangency_chara3 : forall A B O P Q, A <> B ->
 OnCircle Q O P -> Col Q A B -> 
 ((forall X, Col A B X -> OutCircle X O P) <-> Tangent A B O P).
Proof.

intros.
split.
intros.

assert(HT:= (tangency_chara2 A B O P Q H0 H1)); auto.
apply HT.
intros.
induction(eq_dec_points X Q).
left; auto.
right.
assert(OutCircle X O P).
apply H2; Col.

unfold OutCircleS.
unfold OutCircle in H5.
unfold Lt.
split; auto.
intro.

assert(HH:=midpoint_existence X Q).
ex_and HH M.
assert(InCircleS M O P). 
apply(bet_onc2__incS O P Q X M); auto.
intro.
subst M.

apply l7_2 in H7.
apply is_midpoint_id in H7.
subst X; tauto.
intro.
subst M.
apply is_midpoint_id in H7.
contradiction.
unfold Midpoint in H7.
spliter.
Between.
unfold OnCircle; Cong.

assert(Col A B M).
unfold Midpoint in *.
spliter.
ColR.
assert(HH:=(H2 M H9)).
unfold InCircleS in *.
unfold OutCircle in *.

apply le__nlt in HH.
contradiction.

intros.
assert(TangentAt A B O P Q).
unfold TangentAt.
repeat split; Col.

induction(eq_dec_points X Q).
subst X.
unfold TangentAt in *.
spliter.
apply onc__outc; auto.

assert(OutCircleS X O P).
apply(tangent_out A B O P Q X); auto.
unfold OutCircleS in *.
unfold OutCircle.
unfold Lt in H6.
tauto.
Qed.


(** Euclid Book III Prop 3.
 If a straight line passing through the center of a circle 
 bisects a straight line not passing through the center,
 then it also cuts it at right angles; and if it cuts it at right angles, then it also bisects it.
*)

Lemma onc2_mid__perp1 : forall O P A B X, 
 O<>X -> A<>B ->
 OnCircle A O P ->
 OnCircle B O P ->
 Midpoint X A B ->
 Perp O X A B.
Proof.
intros.
assert (Perp_bisect O X A B).
 apply cong_perp_bisect.
assumption.
assumption.
unfold OnCircle in *.
eCong.
apply midpoint_cong in H3.
Cong.
apply perp_bisect_perp.
assumption.
Qed.

(** Euclid Book III Prop 4. 
 If in a circle two straight lines which do not pass through the center cut one another, then they do not bisect one another.
 *)

Lemma onc4_mid2_eq : forall O P A B C D X, B <> C-> A <> B -> 
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Midpoint X A C ->
 Midpoint X B D ->
 X=O.
Proof.
intros O P A B C D X Hbc.
intros.
assert(HH:=onc2_mid__per O P A C X H0 H2 H4).
assert(HP:=onc2_mid__per O P B D X H1 H3 H5).

induction(eq_dec_points X O).
auto.
assert(Col A B X).
apply(per_per_col A B O X); Perp.
unfold Midpoint in *.
spliter.
assert(Col B X D).
apply bet_col; auto.
assert(Col A X C).
ColR.

induction(eq_dec_points A X).
subst X.
treat_equalities.
assert(OutCircleS D O P).
apply(onc2_out__outcs O P A B D); auto.
assert_diffs.
unfold Out.
split.
auto.
split.
auto.
left;finish.

unfold OutCircleS in *.
unfold Lt in *.
spliter.
unfold OnCircle in H3.
apply False_ind.
absurd (Cong O P O D);Cong.

assert(Col A B C). 
ColR.

assert(C = A \/ C = B).
apply(line_circle_two_points O P A B C); Col.
destruct H14.
treat_equalities.
intuition.
treat_equalities.
assert(A = D) by
(apply (symmetric_point_uniqueness C X);unfold Midpoint;split; finish).
treat_equalities.
tauto.
Qed.

(** Euclid Book III Prop 5 
 If two circles cut one another, then they do not have the same center. *)

Lemma intercc__neq :  forall A B C D,
 InterCC A B C D -> A<>C.
Proof.
intros.
unfold InterCC in *.
ex_and H P.
ex_and H0 Q.
unfold InterCCAt in *.
spliter.
unfold OnCircle in *.
intro.
subst C.
apply H.
unfold EqC.
intros.
split.
intro.
unfold OnCircle in *.
assert(Cong A B A D);
eCong.
intro.
unfold OnCircle in *.
assert(Cong A B A D);
eCong.
Qed.

(** Euclid Book III Prop 6 
If two circles touch one another, then they do not have the same center.
*)

Lemma tangentcc__neq: forall A B C D,
 A<>B ->
 TangentCC A B C D ->
 A<>C.
Proof.
intros.
unfold TangentCC in *.
unfold unique in *.
ex_and H0 T.
intro.
subst C.
unfold OnCircle in *.
assert(Cong A B A D); eCong.
assert(T = B).
apply(H1 B); Cong.
subst T.
assert(HH:=symmetric_point_construction B A).
ex_and HH B'.
unfold Midpoint in *.
spliter.
assert(B = B').
apply(H1 B'); eCong.
subst B'.
treat_equalities; tauto.
Qed.

End Tangency.