Require Export GeoCoq.Tarski_dev.Ch12_parallel.

Section Circle.

Context `{TE:Tarski_2D}.

(*
Lemma EqC_chara: forall A B C D, EqC A B C D <-> A=C /\ Cong A B C D.
Proof.
intros.
split.
intros.
unfold EqC in *.
assert (Cong C B C D).
 { specialize H with B.
   unfold OnCircle in *.
   apply H;Cong. }
assert (Cong A D A B).
 { specialize H with D.
   unfold OnCircle in *.
    apply H;Cong. }
.

Lemma nEqC_chara : forall A B C D,
  ~ EqC A B C D <->
  (exists X, OnCircle X A B /\ ~ OnCircle X C D).
Proof.
.
*)

Lemma inc112 : forall A B,
 InCircle A A B.
Proof.
  unfold InCircle.
  Le.
Qed.

(*
Lemma outc212 : forall A B,
 OutCircle B A B.
Proof.
intros.
unfold OutCircle.
Le.
Qed.

Lemma inc212 : forall A B,
 InCircle B A B.
Proof.
intros.
unfold InCircle.
Le.
Qed.
*)

Lemma onc212 : forall A B,
 OnCircle B A B.
Proof.
  unfold OnCircle.
  Cong.
Qed.

Lemma onc_sym : forall A B P, OnCircle P A B -> OnCircle B A P.
Proof.
  unfold OnCircle.
  Cong.
Qed.

Lemma ninc__outcs : forall X O P, ~ InCircle X O P -> OutCircleS X O P.
Proof.
intros.
unfold OutCircleS.
unfold InCircle in *.
apply nle__lt in H; auto.
Qed.

Lemma inc__outc : forall A B P, InCircle P A B <-> OutCircle B A P.
Proof.
  split; trivial.
Qed.

Lemma incs__outcs : forall A B P, InCircleS P A B <-> OutCircleS B A P.
Proof.
  split; trivial.
Qed.

Lemma onc__inc : forall A B P, OnCircle P A B -> InCircle P A B.
Proof.
unfold OnCircle, InCircle.
Le.
Qed.

Lemma onc__outc : forall A B P, OnCircle P A B -> OutCircle P A B.
Proof.
unfold OnCircle, OutCircle.
Le.
Qed.

Lemma inc_outc__onc : forall A B P, InCircle P A B -> OutCircle P A B -> OnCircle P A B.
Proof.
  intros A B P HIn HOut.
  apply le_anti_symmetry; trivial.
Qed.

Lemma incs__inc : forall A B P, InCircleS P A B -> InCircle P A B.
Proof.
unfold InCircleS, InCircle.
Le.
Qed.

Lemma outcs__outc : forall A B P, OutCircleS P A B -> OutCircle P A B.
Proof.
unfold OutCircleS, OutCircle.
Le.
Qed.

Lemma incs__noutc : forall A B P, InCircleS P A B <-> ~ OutCircle P A B.
Proof.
intros.
split; intro; [apply lt__nle|apply nle__lt]; assumption.
Qed.

Lemma outcs__ninc : forall A B P, OutCircleS P A B <-> ~ InCircle P A B.
Proof.
intros.
split; intro; [apply lt__nle|apply nle__lt]; assumption.
Qed.

Lemma inc__noutcs : forall A B P, InCircle P A B <-> ~ OutCircleS P A B.
Proof.
intros.
split; intro; [apply le__nlt|apply nlt__le]; assumption.
Qed.

Lemma outc__nincs : forall A B P, OutCircle P A B <-> ~ InCircleS P A B.
Proof.
intros.
split; intro; [apply le__nlt|apply nlt__le]; assumption.
Qed.

Lemma inc_eq : forall A P, InCircle P A A -> A = P.
Proof.
intros A B HIn.
apply le_zero with A; assumption.
Qed.

Lemma outc_eq : forall A B, OutCircle A A B -> A = B.
Proof.
intros A B HOut.
apply le_zero with A; assumption.
Qed.


End Circle.


Hint Resolve inc112 onc212 onc_sym inc__outc onc__inc onc__outc
             inc_outc__onc incs__inc outcs__outc : circle.

Ltac Circle := auto with circle.

Ltac treat_equalities :=
try treat_equalities_aux;
repeat
  match goal with
   | H:(Cong ?X3 ?X3 ?X1 ?X2) |- _ =>
      apply cong_symmetry in H; apply cong_identity in H;
      smart_subst X2;clean_reap_hyps
   | H:(Cong ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply cong_identity in H;smart_subst X2;clean_reap_hyps
   | H:(Bet ?X1 ?X2 ?X1) |- _ =>
      apply  between_identity in H;smart_subst X2;clean_reap_hyps
   | H:(Midpoint ?X ?Y ?Y) |- _ => apply l7_3 in H; smart_subst Y;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T : A=B) by (apply (between_equality A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?A ?C ?B |- _ =>
     let T := fresh in not_exist_hyp (B=C); assert (T : B=C) by (apply (between_equality_2 A B C); finish);
                       smart_subst B;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?C ?A ?B |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T : A=B) by (apply (between_equality A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?C ?A |- _ =>
     let T := fresh in not_exist_hyp (B=C); assert (T : B=C) by (apply (between_equality_2 A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H:(Le ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply le_zero in H;smart_subst X2;clean_reap_hyps
   | H : Midpoint ?P ?A ?P1, H2 : Midpoint ?P ?A ?P2 |- _ =>
     let T := fresh in not_exist_hyp (P1=P2);
                      assert (T := symmetric_point_uniqueness A P P1 P2 H H2);
                      smart_subst P1;clean_reap_hyps
   | H : Midpoint ?A ?P ?X, H2 : Midpoint ?A ?Q ?X |- _ =>
     let T := fresh in not_exist_hyp (P=Q); assert (T := l7_9 P Q A X H H2);
                       smart_subst P;clean_reap_hyps
   | H : Midpoint ?A ?P ?X, H2 : Midpoint ?A ?X ?Q |- _ =>
     let T := fresh in not_exist_hyp (P=Q); assert (T := l7_9_bis P Q A X H H2);
                       smart_subst P;clean_reap_hyps
   | H : Midpoint ?M ?A ?A |- _ =>
     let T := fresh in not_exist_hyp (M=A); assert (T : l7_3 M A H);
                       smart_subst M;clean_reap_hyps
   | H : Midpoint ?A ?P ?P', H2 : Midpoint ?B ?P ?P' |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := l7_17 P P' A B H H2);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?P ?P', H2 : Midpoint ?B ?P' ?P |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := l7_17_bis P P' A B H H2);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?B ?A |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := is_midpoint_id_2 A B H);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?A ?B |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := is_midpoint_id A B H);
                       smart_subst A;clean_reap_hyps
   | H : OnCircle ?A ?A ?B |- _ =>
      apply cong_reverse_identity in H;smart_subst B;clean_reap_hyps
   | H : OnCircle ?B ?A ?A |- _ =>
      apply cong_identity in H;smart_subst B;clean_reap_hyps
   | H : InCircle ?B ?A ?A |- _ =>
      apply le_zero in H;smart_subst B;clean_reap_hyps
   | H : OutCircle ?A ?A ?B |- _ =>
      apply le_zero in H;smart_subst B;clean_reap_hyps
end.

Section Circle_2.


Context `{TE:Tarski_2D}.

(** If A and B are two points inside the circle, then all points on the segment AB are also
    in the circle, i.e. a circle is a convex figure.
*)

Lemma bet_inc2__inc : forall A B U V P, InCircle U A B -> InCircle V A B -> Bet U P V ->
  InCircle P A B.
Proof.
  intros A B U V P HU HV HBet.
  destruct (eq_dec_points U P).
    subst P; assumption.
  destruct (eq_dec_points P V).
    subst P; assumption.
  destruct (le_cases A U A V).
  - apply le_transitivity with A V; trivial.
    apply le_comm, lt__le, (bet_le__lt U); Le.
  - apply le_transitivity with A U; trivial.
    apply le_comm, lt__le, (bet_le__lt V); Between; Le.
Qed.

(** Given two points U and V on a circle, the points of the line UV which are inside the circle are between U and V. *) 

Lemma col_inc_onc2__bet : forall A B U V P, U <> V -> OnCircle U A B -> OnCircle V A B ->
  Col U V P -> InCircle P A B -> Bet U P V.
Proof.
  intros A B U V P HUV HU HV HCol HIn.
  assert (Cong A U A V) by (apply cong_transitivity with A B; Cong).
  destruct HCol as [HBet|[HBet|HBet]]; Between.
  - destruct (eq_dec_points P V); try (subst; Between).
    exfalso.
    assert (HLt : Lt V A U A).
      apply (bet_le__lt P); Between.
      apply (l5_6 A P A B); Cong.
    destruct HLt as [HLe HNCong].
    apply HNCong; Cong.
  - destruct (eq_dec_points P U); try (subst; Between).
    exfalso.
    assert (HLt : Lt U A V A).
      apply (bet_le__lt P); trivial.
      apply (l5_6 A P A B); Cong.
    destruct HLt as [HLe HNCong].
    apply HNCong; Cong.
Qed.

(** Given two points U and V on a circle, all points of line UV which are outside the segment UV are outside the circle. *)

Lemma onc2_out__outcs : forall A B U V P, U <> V -> OnCircle U A B -> OnCircle V A B -> Out P U V ->
  OutCircleS P A B.
Proof.
  intros A B U V P HUV HUOn HVOn HOut.
  apply outcs__ninc.
  intro HIn.
  apply (not_bet_and_out U P V).
  split; trivial.
  apply (col_inc_onc2__bet A B); Col.
Qed.

(** Given two points U and V inside a circle, all points of line UV which are outside the circle are outside the segment UV. *)

Lemma col_inc2_outcs__out : forall A B U V P, InCircle U A B -> InCircle V A B ->
  Col U V P -> OutCircleS P A B -> Out P U V.
Proof.
  intros A B U V P HUIn HVIn HCol HOut.
  apply not_bet_out; Col.
  intro HBet.
  apply outcs__ninc in HOut.
  apply HOut, bet_inc2__inc with U V; trivial.
Qed.

(** Given a point U on a circle and a point V inside the circle, there is a point V such as UV is a chord of the circle
    going through P. *)

Lemma chord_completion : forall A B U P, OnCircle U A B -> InCircle P A B ->
  exists V, OnCircle V A B /\ Bet U P V.
Proof.
  intros A B U P HOn HIn.
  destruct (eq_dec_points U A).
    unfold OnCircle, InCircle in *|-.
    treat_equalities; exists U; split; Circle; Between.
  assert (HA' : exists A', U <> A' /\ Col U P A' /\ Per A A' U).
  { destruct (Col_dec U P A) as [HCol|HNCol].
      exists A; split; Col; Perp.
    destruct (l8_18_existence U P A) as [A' [HCol HPerp]]; trivial.
    assert (U <> A').
    { intro; treat_equalities.
      destruct (l11_46 P U A) as [_ HLt]; Col.
        left; Perp.
      apply lt__nle in HLt.
      apply HLt.
      apply (l5_6 A P A B); Cong.
    }
    exists A'; repeat split; trivial.
    apply l8_2, perp_per_1.
    apply perp_left_comm, perp_col with P; trivial.
  }
  destruct HA' as [A' [HUA' [HCol HPer]]].
  destruct (symmetric_point_construction U A') as [V HV].
  assert_diffs.
  assert (HCong := per_double_cong A A' U V HPer HV).
  assert (HVOn : OnCircle V A B).
    unfold OnCircle in *.
    apply cong_transitivity with A U; Cong.
  exists V; split; trivial.
  apply (col_inc_onc2__bet A B); trivial.
  ColR.
Qed.

(** Given a circle, there is a point strictly outside the circle. *)

Lemma outcs_exists : forall O P, exists Q, OutCircleS Q O P.
Proof.
intros.
induction(eq_dec_points O P).
subst P.
assert(HH:=another_point O).
ex_and HH Q.
exists Q.
unfold OutCircleS.
apply lt1123;auto.

assert(HH:=segment_construction O P O P).
ex_and HH Q.
exists Q.
split.
exists P.
split; Cong.
intro.
assert (P=Q) by eauto using between_cong.
treat_equalities;intuition.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray which is also strictly outside the circle. *)

Lemma outcs_exists1 : forall O P X, X <> O -> exists Q, Out O X Q /\ OutCircleS Q O P.
Proof.
intros O P X HOX.
destruct (segment_construction O X O P) as [Q [HQ1 HQ2]].
exists Q; split.
  apply bet_out; auto.
split.
- apply le_comm.
  exists X.
  split; Between; Cong.
- intro.
  apply HOX.
  apply between_cong with Q; Between.
  apply cong_transitivity with O P; Cong.
Qed.

(** Given a circle there is a point which is strictly inside. *)

Lemma incs_exists : forall O P, O <> P -> exists Q, InCircleS Q O P.
Proof.
intros.
exists O.
apply lt1123;auto.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray which is also on strictly inside circle. *)

Lemma incs_exists1 : forall O P X, X <> O -> P <> O -> exists Q, Out O X Q /\ InCircleS Q O P.
Proof.
intros O P X HOX HOP.
destruct (midpoint_existence O P) as [M HM].
destruct (segment_construction_3 O X O M) as [Q [HQ1 HQ2]]; auto.
  intro; treat_equalities; auto.
exists Q; split; auto.
apply (cong2_lt__lt O M O P); Cong.
apply mid__lt; auto.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray which is also on the circle. *)

Lemma onc_exists : forall O P X,  X <> O -> O <> P -> exists Q, OnCircle Q O P /\ Out O X Q.
Proof.
intros.
assert(HH:=segment_construction_2 X O O P H).
ex_and HH Q.
exists Q.
split.
unfold OnCircle.
Cong.
unfold Out.
repeat split; auto.
intro.
subst Q.
treat_equalities; tauto.
Qed.

Lemma diam_points : forall O P X, exists Q1 Q2,
  Bet Q1 O Q2 /\ Col Q1 Q2 X /\ OnCircle Q1 O P /\ OnCircle Q2 O P.
Proof.
intros O P X.
destruct (eq_dec_points X O).
  subst X.
  destruct (segment_construction P O O P) as [P' [HP'1 HP'2]].
  exists P, P'; repeat split; Col; Circle.
destruct (eq_dec_points O P).
  subst P.
  exists O, O; repeat split; finish; Circle.
assert(HH:= onc_exists O P X H H0).
ex_and HH Q1.
assert(HH:= segment_construction Q1 O O Q1).
ex_and HH Q2.
exists Q1, Q2.
repeat split; Col.
ColR.
apply cong_transitivity with O Q1; Cong.
Qed.

(** The symmetric of a point on a circle relative to the center is also on the circle. *)

Lemma symmetric_oncircle : forall X Y O P, 
 Midpoint O X Y -> OnCircle X O P -> OnCircle Y O P.
Proof.
intros.
apply cong_transitivity with O X; Cong.
Qed.


(** The middle of a chord together with the center of the circle and one end of the chord form a right angle *)

Lemma mid_onc2__per : forall O P U V X,
 OnCircle U O P -> OnCircle V O P -> Midpoint X U V -> Per O X U.
Proof.
intros.
unfold Per.
exists V.
unfold OnCircle in *.
split; trivial.
apply cong_transitivity with O P; Cong.
Qed.

(** Euclid Book III Prop 3 (two lemmas).
 If a straight line passing through the center of a circle 
 bisects a straight line not passing through the center,
 then it also cuts it at right angles; and if it cuts it at right angles, then it also bisects it.
*)

(** The line from the center of a circle to the midpoint of a chord is perpendicular to the chord. *)

Lemma mid_onc2__perp : forall O P A B X,
 O <> X -> A <> B -> OnCircle A O P -> OnCircle B O P -> Midpoint X A B -> Perp O X A B.
Proof.
intros.
assert(Per O X A).
apply (mid_onc2__per O P A B X); auto.
unfold Midpoint in *.
spliter.

apply per_perp_in in H4; auto.
apply perp_in_perp in H4.
apply perp_sym.

apply (perp_col _ X); Perp.
Col.
intro.
subst X.
treat_equalities; tauto.
Qed.

(** If a line passing through the center of a circle is perpendicular to a chord, then they intersect at the middle of the chord *)

Lemma col_onc2_perp__mid : forall O P A B X,
 O<>X -> A<>B -> Col A B X -> OnCircle A O P -> OnCircle B O P -> Perp O X A B -> Midpoint X A B.
Proof.
  intros O P A B X HOX HAB HCol HAOn HBOn HPerp.
  destruct (midpoint_existence A B) as [M HM].
  cut (X = M).
    intro; subst; trivial.
  assert (HNCol : ~ Col A B O) by (destruct (perp_not_col2 A B O X); Perp; Col).
  apply (l8_18_uniqueness A B O); Col; Perp.
  apply perp_sym, mid_onc2__perp with P; auto.
  intro; subst; apply HNCol; Col.
Qed.

(** The center of a circle belongs to the perpendicular bisector of each chord *)

Lemma mid_onc2_perp__col : forall O P A B X Y,
 A <> B -> OnCircle A O P -> OnCircle B O P -> Midpoint X A B -> Perp X Y A B -> Col X Y O.
Proof.
  intros O P A B X Y HAB HAOn HBOn HX HPerp.
  destruct (eq_dec_points O X).
    subst; Col.
  apply perp_perp_col with A B; trivial.
  apply perp_left_comm, mid_onc2__perp with P; auto.
Qed.

(** A circle does not cut a line at more than two points. *)

Lemma line_circle_two_points : forall O P U V W,
 U <> V -> Col U V W -> OnCircle U O P -> OnCircle V O P -> OnCircle W O P -> 
 W = U \/ W = V.
Proof.
intros O P U V W HUV HCol HUOn HVOn HWOn.
destruct (eq_dec_points W U); auto.
right.
apply between_equality with U; apply col_inc_onc2__bet with O P; Col; Circle.
Qed.

(** If a point is strictly inside a chord, it is strictly inside the circle. *)

Lemma bet_onc2__incs : forall O P U V X,
 X <> U -> X <> V -> Bet U X V ->
 OnCircle U O P -> OnCircle V O P ->
 InCircleS X O P.
Proof.
intros O P U V X HUX HVX HBet HUOn HVOn.
assert (HIn : InCircle X O P) by (apply bet_inc2__inc with U V; Circle).
split; auto.
intro.
assert_diffs.
destruct (line_circle_two_points O P U V X); Col.
Qed.

(** The midpoint of a chord is strictly inside the circle. *)

Lemma onc2_mid__incs : forall O P U V M, 
 U <> V -> OnCircle U O P -> OnCircle V O P -> Midpoint M U V ->
 InCircleS M O P.
Proof.
intros O P U V M HUV HUOn HVOn HM.
assert_diffs.
apply bet_onc2__incs with U V; Between.
Qed.

(** A point is either strictly inside, on or strictly outside a circle. *)

Lemma circle_cases : forall O P X,
  OnCircle X O P \/ InCircleS X O P \/ OutCircleS X O P.
Proof.
intros O P X.
destruct (Cong_dec O X O P); auto.
right.
destruct (le_cases O P O X); [right|left]; split; Cong.
Qed.

(** If a point is inside a circle, then it lies on a radius. *)

Lemma inc__radius : forall O P X, InCircle X O P ->
  exists Y, OnCircle Y O P /\ Bet O X Y.
Proof.
  intros O P X HIn.
  destruct (eq_dec_points O P).
    unfold InCircle in HIn; treat_equalities.
    exists O; split; Circle; Between.
  destruct (eq_dec_points O X).
    subst; exists P; split; Circle; Between.
  destruct (segment_construction_3 O X O P) as [Y [HY1 HY2]]; auto.
  exists Y; split; auto.
  apply l6_13_1; trivial.
  apply (l5_6 O X O P); Cong.
Qed.

(** Euclid Book III Prop 4. 
 If in a circle two straight lines which do not pass through the center cut one another,
 then they do not bisect one another.
 *)

Lemma mid2_onc4__eq : forall O P A B C D X, B <> C-> A <> B -> 
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
assert(HH:=mid_onc2__per O P A C X H0 H2 H4).
assert(HP:=mid_onc2__per O P B D X H1 H3 H5).

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
left; Between.

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
(apply (symmetric_point_uniqueness C X); split; Between; Cong).
treat_equalities.
tauto.
Qed.

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle,
 then the point taken is the center of the circle.
*)

Lemma cong2_onc3__eq : forall O P X A B C, A <> B -> A <> C -> B <> C ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
  Cong X A X B -> Cong X A X C ->
  X = O.
Proof.
  intros O P X A B C HAB HAC HBC HAOn HBOn HCOn HCong1 HCong2.
  destruct (midpoint_existence A B) as [M1 HM1].
  destruct (midpoint_existence A C) as [M2 HM2].
  destruct (perp_exists M1 A B) as [P1 HPerp1]; auto.
  destruct (perp_exists M2 A C) as [P2 HPerp2]; auto.
  assert (HColX1 : Col M1 P1 X) by (apply (mid_onc2_perp__col X A A B); Circle).
  assert (HColO1 : Col M1 P1 O) by (apply (mid_onc2_perp__col O P A B); auto).
  assert (HColX2 : Col M2 P2 X) by (apply (mid_onc2_perp__col X A A C); Circle).
  assert (HColO2 : Col M2 P2 O) by (apply (mid_onc2_perp__col O P A C); auto).
  assert_diffs.
  destruct (Col_dec M1 P1 M2); [apply (l6_21 M2 P2 M1 P1)|apply (l6_21 M1 P1 M2 P2)]; Col.
  intro.
  apply HBC.
  destruct (eq_dec_points M1 M2).
    apply (symmetric_point_uniqueness A M1); subst; trivial.
  apply l10_2_uniqueness_spec with M1 P1 A.
    split; auto; exists M1; Col.
  split.
    exists M2; auto.
  left.
  apply (perp_col2 M2 P2); ColR.
Qed.

Lemma onc2_mid_cong_col : forall O P U V M X, U <> V -> OnCircle U O P -> OnCircle V O P -> Midpoint M U V -> Cong U X V X -> Col O X M.
Proof.
intros.
assert(HH:=mid_onc2__per O P U V M H0 H1 H2).
assert(Per X M U).
unfold Per.
exists V.
unfold OnCircle in *.
split; Cong.
apply(per_per_col _ _ U); auto.
assert_diffs.
auto.
Qed.


Lemma onc_not_center : forall O P A, O <> P -> OnCircle A O P -> A <> O.
Proof.
intros.
intro.
unfold OnCircle in *.
treat_equalities; tauto.
Qed.


Lemma onc2_per__mid : forall O P U V M, U <> V -> M <> U ->
 OnCircle U O P -> OnCircle V O P -> Col M U V -> Per O M U -> Midpoint M U V .
Proof.
intros.
assert(HH:=midpoint_existence U V).
ex_and HH M'.
assert(HH:=(mid_onc2__per O P U V M' H1 H2 H5)).
assert(M = M' \/ ~ Col M' U V).
apply(col_per2_cases O M U V M'); Col.
assert_diffs;auto.
induction H6.
subst M'.
assumption.
apply False_ind.
apply H6.
ColR.
Qed.

(** Euclid Book III Prop 14
Equal straight lines in a circle are equally distant from the center, 
and those which are equally distant from the center equal one another.
*)

Lemma cong_chord_cong_center : forall O P A B C D M N,
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Midpoint M A B ->
 Midpoint N C D ->
 Cong A B C D ->
 Cong O N O M.
Proof.
intros.
assert(Cong M B N D).
apply cong_commutativity.
eapply (cong_cong_half_1 _ _ A _ _ C); Midpoint.
Cong.
unfold Midpoint in *.
unfold OnCircle in *.
spliter.
apply cong_commutativity.
apply cong_symmetry.
apply(l4_2 A M B O C N D O).
unfold IFSC.
repeat split; Cong.
apply (cong_transitivity _ _ O P); Cong.
apply (cong_transitivity _ _ O P); Cong.
Qed.

(** variant *)
Lemma cong_chord_cong_center1 : forall O P A B C D M N,
 A <> B -> C <> D -> M <> A -> N <> C ->
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Col M A B ->
 Col N C D ->
 Per O M A ->
 Per O N C ->
 Cong A B C D ->
 Cong O N O M.
Proof.
intros.
assert(Midpoint M A B).
apply(onc2_per__mid O P A B M H H1 H3 H4 H7 H9).
assert(Midpoint N C D).
apply(onc2_per__mid O P C D N H0 H2 H5 H6 H8 H10).
apply (cong_chord_cong_center O P A B C D M N); auto.
Qed.

(** Prop 7   **)

Lemma onc_sym__onc : forall O P A B X Y, 
Bet O A B -> OnCircle A O P -> OnCircle B O P -> OnCircle X O P -> ReflectL X Y A B -> OnCircle Y O P.
Proof.
intros.
unfold OnCircle in *.
assert(Cong X O Y O).
  {
    apply(is_image_spec_col_cong A B X Y O H3);Col.
  }
apply cong_transitivity with O X; Cong.
Qed.


Definition Diam A B O P := Bet A O B /\ OnCircle A O P /\ OnCircle B O P.

Lemma mid_onc__diam : forall O P A B, OnCircle A O P -> Midpoint O A B -> Diam A B O P.
Proof.
  intros O P A B HA HB.
  repeat split; Between.
  apply (symmetric_oncircle A); trivial.
Qed.

Lemma chord_le_diam : forall O P A B U V,
 Diam A B O P -> OnCircle U O P -> OnCircle V O P -> Le U V A B.
Proof.
intros.
unfold OnCircle in *.
unfold Diam in *.
spliter.
apply(triangle_inequality_2 U O V A O B); trivial;
apply cong_transitivity with O P; Cong.
Qed.

Lemma chord_lt_diam : forall O P A B U V, 
 ~ Col O U V -> Diam A B O P -> OnCircle U O P -> OnCircle V O P ->
 Lt U V A B.
Proof.
intros.
assert(HH:= chord_le_diam O P A B U V H0 H1 H2).
unfold Lt.
split; auto.
intro.
apply H.
unfold Diam in *.
assert(HP:=midpoint_existence U V).
ex_and HP O'.
unfold Midpoint in *.
spliter.
unfold OnCircle in *.
assert(Cong O A O B) by (apply cong_transitivity with O P; Cong).
assert(Cong A O U O').
apply(cong_cong_half_1 A O B U O' V); unfold Midpoint; try split; Cong.
assert(Cong B O V O').
apply(cong_cong_half_2 A O B U O' V); unfold Midpoint; try split; Cong.
apply(l4_13 O A B).
Col.
unfold Cong_3.
repeat split; Cong; apply cong_transitivity with O P; Cong.
Qed.


Lemma inc2_le_diam: forall O P A B U V, Diam A B O P -> InCircle U O P -> InCircle V O P -> Le U V A B.
Proof.
intros.
unfold InCircle in *.
unfold Diam in *.
spliter.
unfold OnCircle in *.
assert(HH:= segment_construction U O O V).
ex_and HH W.
assert(Le U V U W).
{
  apply (triangle_inequality U O); Between; Cong.
}

assert(Le U W A B).
{
  apply(bet2_le2__le O O A B U W); Between.

  apply (l5_6 O U O P O U O A);Cong.
  apply (l5_6 O V O P O W O B);Cong.
}
apply(le_transitivity U V U W A B); auto.
Qed.


Lemma onc_col_diam__eq : forall O P A B X, Diam A B O P -> OnCircle X O P -> Col A B X -> X = A \/ X = B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold OnCircle in *.
induction(eq_dec_points O P).
treat_equalities.
left; auto.

induction(eq_dec_points X B).
right; auto.
left.
assert_diffs.
assert(Cong O A O X) by (apply cong_transitivity with O P; Cong).
assert(Col A O X) by ColR.
assert(HH:= l7_20 O A X H11 H10).
induction HH.
auto.
assert(Midpoint O A B).
unfold Midpoint; split; trivial.
apply cong_transitivity with O P; Cong.
apply False_ind.
apply H5.
apply (symmetric_point_uniqueness A O ); auto.
Qed.

Lemma onc2_out__eq : forall O P A B, OnCircle A O P -> OnCircle B O P -> Out O A B -> A = B.
Proof.
  intros O P A B HAOn HBOn HOut.
  destruct (symmetric_point_construction A O) as [A' HA'].
  destruct (onc_col_diam__eq O P A A' B); auto.
    apply mid_onc__diam; assumption.
    ColR.
  exfalso.
  subst A'.
  apply (not_bet_and_out A O B); Between.
Qed.

Lemma bet_onc_le_a : forall O P A B T X, Diam A B O P -> Bet B O T -> OnCircle X O P -> Le T A T X.
Proof.
intros.
unfold Diam in*.
spliter.
unfold OnCircle in *.
assert(Cong O X O A) by (apply cong_transitivity with O P; Cong).
induction(eq_dec_points P O).
treat_equalities.
apply le_reflexivity.
induction(eq_dec_points T O).
subst T.
apply cong__le;Cong.
assert_diffs.
apply(triangle_reverse_inequality O T X A); Cong.
assert_diffs.
repeat split; auto.
apply (l5_2 B); Between.
Qed.


Lemma bet_onc_lt_a : forall O P A B T X,
 Diam A B O P -> O <> P -> O <> T -> X <> A -> Bet B O T  -> OnCircle X O P ->
 Lt T A T X.
Proof.
intros.
assert(HH:= bet_onc_le_a O P A B T X H H3 H4).
assert(Lt T A T X \/ Cong T A T X).
{
  induction(Cong_dec T A T X).
  right; auto.
  left.
  unfold Lt.
  split; auto.
}
induction H5; auto.
unfold Diam in*.
spliter.
unfold OnCircle in *.
assert_diffs.
assert(Bet O A T \/ Bet O T A).
apply(l5_2 B O A T); Between.
assert (Cong O A O X) by (apply cong_transitivity with O P; Cong).
induction H13.
assert(Bet O X T).
{
  apply(l4_6 O A T O X T); auto.
  unfold Cong_3.
  repeat split; Cong.
}
apply False_ind.
apply H2.
apply(between_cong_2 O T); Cong.
assert(Bet O T X).
{
  apply(l4_6 O T A O T X); auto.
  unfold Cong_3.
  repeat split; Cong.
}
apply False_ind.
apply H2.
apply(between_cong_3 O T); Cong.
Qed.



Lemma bet_onc_le_b : forall O P A B T X,
 Diam A B O P -> Bet A O T -> OnCircle X O P ->
 Le T X T A.
Proof.
intros.
unfold Diam in *.
spliter.
unfold OnCircle in *.
apply(triangle_inequality T O X A).
Between.
apply cong_transitivity with O P; Cong.
Qed.


Lemma bet_onc_lt_b : forall O P A B T X,
 Diam A B O P -> T <> O -> X <> A -> Bet A O T -> OnCircle X O P ->
 Lt T X T A.
Proof.
intros.
assert(HH:= bet_onc_le_b O P A B T X H H2 H3 ).
assert(Lt T X  T A \/ Cong T A T X).
{
  induction(Cong_dec T A T X).
  right; auto.
  left.
  unfold Lt.
  split; Cong.
}
unfold Diam in *.
spliter.
unfold OnCircle in *.
induction H4; auto.
apply False_ind.
assert(Bet T O A) by eBetween.
assert(Bet T O X).
{
  apply(l4_6 T O A T O X); auto.
  repeat split; eCong.
}
apply H1.
apply(between_cong_3 T O); trivial.
apply cong_transitivity with O P; Cong.
Qed.



Lemma incs2_lt_diam : forall O P A B U V, Diam A B O P -> InCircleS U O P -> InCircleS V O P -> Lt U V A B.
Proof.
intros.
unfold Diam in H.
spliter.
unfold OnCircle in *.
unfold InCircleS in *.

induction(eq_dec_points O P).
treat_equalities.
unfold Lt in H0.
spliter.
apply le_zero in H.
treat_equalities.
apply False_ind.
apply H0; Cong.

assert(Lt A O A B /\ Lt B O A B).
{
  assert (Midpoint O A B) by (split;eCong).
  split.
  apply(mid__lt );  assert_diffs;auto.
  assert (Lt B O B A) by (apply mid__lt;assert_diffs;finish).
  auto using lt_right_comm.
}
spliter.

induction(eq_dec_points O U).
treat_equalities.
spliter.
assert(Lt O V O A).
{
  apply(cong2_lt__lt O V O P); Cong.
}
apply (lt_transitivity O V O A A B); auto.
apply lt_left_comm; auto.

assert(HH:=segment_construction U O O V).
ex_and HH V'.

assert(Le U V U V').
{
  apply(triangle_inequality U O V V' H8); Cong.
}
assert(Lt U V' A B).
{
  apply(bet2_lt2__lt O O A B U V' H8 H).
  apply(cong2_lt__lt O U O P O U O A); Cong.
  apply(cong2_lt__lt O V O P O V' O B); Cong.
}

apply(le1234_lt__lt U V U V' A B); auto.
Qed.




Lemma incs_onc_diam__lt : forall O P A B U V, Diam A B O P -> InCircleS U O P -> OnCircle V O P -> Lt U V A B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold OnCircle in *.
unfold InCircleS in *.

assert(HH:=segment_construction V O O U).
ex_and HH U'.
assert(Lt V U' A B).
{
  apply(bet2_lt_le__lt O O A B V U' H4 H).
  apply cong_transitivity with O P; Cong.
  apply(cong2_lt__lt O U O P); Cong.
}
assert(Le V U V U').
{
  apply(triangle_inequality V O U U' H4); Cong.
}
apply lt_left_comm.
apply(le1234_lt__lt V U V U'); auto.
Qed.


Lemma diam_cong_incs__outcs : forall O P A B U V, Diam A B O P -> Cong A B U V -> InCircleS U O P -> OutCircleS V O P.
Proof.
intros.
induction(eq_dec_points O P).
treat_equalities.
unfold InCircleS in H1.

unfold Lt in H1.
spliter.
apply le_zero in H1.
treat_equalities.
apply False_ind.
apply H2; Cong.

assert(HH:= circle_cases O P V).
induction HH.
assert(Lt U V A B) by  apply(incs_onc_diam__lt O P A B U V H H1 H3).
unfold Lt in H4.
spliter.
apply False_ind.
apply H5; Cong.

induction H3.
assert(HH:=incs2_lt_diam O P A B U V H H1 H3).
unfold Lt in HH.
spliter.
apply False_ind.
apply H5; Cong.
assumption.
Qed.


Lemma diam_uniqueness : forall O P A B X, Diam A B O P -> Cong A X A B -> OnCircle X O P -> X = B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold OnCircle in *.
induction(eq_dec_points O P).
treat_equalities; auto.
assert(Bet A O X).
{
  apply(l4_6 A O B A O X); auto.
  repeat split; Cong.
  apply cong_transitivity with O P; Cong.
}
assert_diffs.
apply(between_cong_3 A O); auto.
apply cong_transitivity with O P; Cong.
Qed.


Lemma cong_onc3_cases : forall O P A X Y,
 Cong A X A Y ->
 OnCircle A O P -> OnCircle X O P -> OnCircle Y O P ->
 X = Y \/ ReflectL X Y O A.
Proof.
intros.
unfold OnCircle in *.
induction(eq_dec_points X Y).
left; auto.
right.
assert(HH:= midpoint_existence X Y).
ex_and HH M.
assert(Per O M X).
{
  apply(mid_onc2__per O P X Y M); Circle.
}
assert(Per A M X).
{
  unfold Per.
  exists Y.
  split; auto.
}
assert(Col A O M).
{
  apply (per_per_col _ _ X); auto.
  intro.
  treat_equalities; tauto.
}

unfold ReflectL.
split.
exists M.
split; Midpoint.
Col.
left.

unfold Midpoint in *.
spliter.

induction(eq_dec_points M O).
subst M.
apply per_perp_in in H6.
apply perp_in_comm in H6.
apply perp_in_perp in H6.
apply perp_sym in H6.
apply (perp_col X O O A Y) in H6; Col.
Perp.
intro.
treat_equalities; tauto.
intro.
treat_equalities; tauto.

apply(perp_col O M Y X A);Col.
intro.
treat_equalities; tauto.
apply per_perp_in in H5.
apply perp_in_comm in H5.
apply perp_in_perp in H5.
apply perp_sym in H5.
apply(perp_col X M M O Y) in H5; auto.
Perp.
Col.
auto.
intro.
treat_equalities; tauto.
Qed.


Lemma bet_cong_onc3_cases : forall O P A X Y T,
 T <> O -> Bet A O T -> Cong T X T Y ->
 OnCircle A O P  -> OnCircle X O P  -> OnCircle Y O P ->
 X = Y \/ ReflectL X Y O A.
Proof.
intros.
unfold OnCircle in *.
induction(eq_dec_points O P).
treat_equalities.
left; auto.

induction(eq_dec_points T X).
treat_equalities.
left; auto.

assert(CongA T O X T O Y /\ CongA O T X O T Y /\ CongA T X O T Y O).
{
  apply(l11_51 O T X O T Y); Cong.
    intro.
    treat_equalities; tauto.
  apply cong_transitivity with O P; Cong.
}
spliter.
assert(Out T O A).
{
  unfold Out.
  repeat split; auto.
  intro.
  treat_equalities; tauto.
  Between.
}
assert(Cong A X A Y).
{ apply(cong2_conga_cong A T X A T Y); Cong.
  apply (out_conga O T X O T Y); auto.
  apply out_trivial; auto.
  apply out_trivial.
  intro.
  treat_equalities; tauto.
}
apply (cong_onc3_cases O P); auto.
Qed.

Lemma onc3__ncol : forall O P A B C,
 A <> B -> A <> C -> B <> C ->
 OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
 ~ Col A B C.
Proof.
intros.
unfold OnCircle in *.
intro.
induction H5.
assert(InCircleS B O P).
{
  apply(bet_onc2__incs O P A C B); Circle.
}
unfold InCircleS in *.
unfold Lt in *.
tauto.
induction H5.
assert(InCircleS C O P).
{
  apply(bet_onc2__incs O P B A C); Circle.
}
unfold InCircleS in *.
unfold Lt in *.
tauto.
assert(InCircleS A O P).
{
  apply(bet_onc2__incs O P C B A); Circle.
}
unfold InCircleS in *.
unfold Lt in *.
tauto.
Qed.

Lemma prop_7_8 : forall O P A B T X Y , Diam A B O P -> Bet A O T 
                               -> OnCircle X O P -> OnCircle Y O P
                               -> LeA A O X A O Y -> Le T Y T X.
Proof.
intros.
assert(HD:=H).
unfold Diam in H.
spliter.
unfold OnCircle in *.
induction(eq_dec_points O P).
subst P.
treat_equalities; auto.
apply le_reflexivity.

induction(eq_dec_points O T).
treat_equalities.
apply cong__le, cong_transitivity with O P; Cong.

induction(Cong_dec A X A Y).
assert(X = Y \/ ReflectL X Y O A).
{
  apply(cong_onc3_cases O P A X Y); Circle.
}
induction H9.
treat_equalities.
apply le_reflexivity.
apply cong__le.
apply cong_symmetry.
apply cong_commutativity.
apply(is_image_spec_col_cong O A X Y T); auto.
unfold Diam in *.
spliter.
ColR.

assert(Le T X T A).
{
  apply(bet_onc_le_b O P A B T X HD H0).
  Circle.
}
assert_diffs.

assert(LeA Y O T X O T).
{
  apply lea_comm.
  apply(l11_36 A O X A O Y T T); auto.
}

assert(Lt T Y T X).
{
  assert(Cong O X O Y) by (apply cong_transitivity with O P; Cong).
  apply(t18_18 O T X O T Y); Cong.
  unfold LtA.
  split; auto.
  intro.
  assert(Cong Y T X T).
  {
    apply(cong2_conga_cong Y O T X O T); Cong.
  }
  assert(CongA A O X A O Y).
  apply(l11_13 T O X T O Y A A); Between.
  CongA.
  apply H8.
  apply(cong2_conga_cong A O X A O Y); Cong.
}
apply lt__le.
assumption.
Qed.




Lemma Prop_7_8_uniqueness : forall O P A X Y Z T, T <> O -> X <> Y -> Bet A O T -> Cong T X T Y -> Cong T X T Z
                                                -> OnCircle A O P  
                                                -> OnCircle X O P -> OnCircle Y O P -> OnCircle Z O P
                                               -> Z = X \/ Z = Y.
Proof.
intros.
induction(eq_dec_points O P).
unfold OnCircle in *.
treat_equalities.
auto.
assert(X = Y \/ ReflectL X Y O A).
{
  apply(bet_cong_onc3_cases O P A X Y T); auto.
}
assert(X = Z \/ ReflectL X Z O A).
{
  apply(bet_cong_onc3_cases O P A X Z T); auto.
}
assert(Y = Z \/ ReflectL Y Z O A).
{
  apply(bet_cong_onc3_cases O P A Y Z T); auto.
  apply cong_transitivity with T X; Cong.
}
induction H9.
contradiction.
induction H10.
auto.
induction H11.
auto.
assert(HH:=l10_2_uniqueness_spec O A Z X Y H10 H11).
contradiction.
Qed.

Lemma diam_exists : forall O P T, exists A, exists B, Diam A B O P /\ Col A B T.
Proof.
intros.
induction(eq_dec_points O P).
subst P.
exists O.
exists O.
split; Col.
repeat split; Circle;
unfold Diam.
apply between_trivial.

induction(eq_dec_points T O).
subst T.
assert(HH:= another_point O).
ex_and HH T.
assert(exists Q : Tpoint, OnCircle Q O P /\ Out O T Q).
apply(onc_exists O P T); auto.
ex_and H1 A.
exists A.
assert(HH:=symmetric_point_construction A O).
ex_and HH B.
exists B.
unfold Midpoint in *.
spliter.
split; Col.
unfold Diam.
unfold OnCircle in *.
repeat split; trivial.
apply cong_transitivity with O A; Cong.
assert(exists Q : Tpoint, OnCircle Q O P /\ Out O T Q).
apply(onc_exists O P T); auto.
ex_and H1 A.
exists A.
assert(HH:=symmetric_point_construction A O).
ex_and HH B.
exists B.
unfold Midpoint in *.
spliter.
split; Col.
unfold Diam.
unfold OnCircle in *.
repeat split; trivial.
apply cong_transitivity with O A; Cong.
assert_diffs.
apply out_col in H2.
ColR.
Qed.

Lemma ray_cut_chord : forall O P A B X Y,
  O <> P ->  Diam A B O P -> OnCircle X O P -> OnCircle Y O P -> TS A B X Y -> OS X Y A O ->
 TS X Y O B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold TS in H3.
spliter.
ex_and H8 T.
assert(InCircleS T O P).
{
  apply(bet_onc2__incs O P X Y T); try(auto; intro; treat_equalities; contradiction).
}
unfold InCircleS in *.
apply(cong2_lt__lt O T O P O T O B) in H10; eCong.
assert(Hlt:= H10).
assert(~Col O X Y).
{
  unfold OS in *.
  ex_and H4 R.
  unfold TS in H11.
  spliter.
  assumption.
}

assert(TS X Y A B).
{
  unfold TS.
  repeat split.
  apply (onc3__ncol O P); Circle; try(intro; treat_equalities).
  apply H3; Col.
  apply H7; Col.
  apply H11; Col.
  apply (onc3__ncol O P); Circle; try(intro; treat_equalities).
  apply H3; Col.
  apply H7; Col.
  apply H11; Col.
  exists T.
  split.
  Col.
  induction H8.
  assert(Bet O A T) by eBetween.
  apply(bet__le1213) in H12.
  apply (cong2_lt__lt O T O B O T O A) in Hlt; eCong.
  apply le__nlt in H12.
  contradiction.
  induction H8.
  assert(Bet O B T) by eBetween.
  apply(bet__le1213) in H12.
  apply le__nlt in H12.
  contradiction.
  Between.
}
apply(l9_8_2 X Y A O B); auto.
Qed.

Lemma center_col__diam : forall O P A B,
 A <> B -> Col O A B -> OnCircle A O P -> OnCircle B O P ->
 Diam A B O P.
Proof.
intros.
unfold Diam.
split; Circle.
assert(Cong O A O B).
{
  unfold OnCircle in *.
  eCong.
}
assert(A = B \/ Midpoint O A B).
{
  apply(l7_20 O A B); Col.
}
induction H4.
contradiction.
Between.
Qed.

Lemma diam__midpoint: forall O P A B, Diam A B O P -> Midpoint O A B.
Proof.
intros.
unfold Diam in *.
spliter.
unfold Midpoint.
unfold OnCircle in *.
split; eCong.
Qed.

Lemma chords_midpoints_col_par : forall O P A M B C N D, 
 O <> P ->
 OnCircle A O P -> OnCircle B O P ->
 OnCircle C O P -> OnCircle D O P ->
 Midpoint M A B -> Midpoint N C D ->
 Col O M N -> ~ Col O A B -> ~ Col O C D -> Par A B C D.
Proof.
intros.
assert(Perp O M A B).
{
  apply(mid_onc2__perp O  P A B M); Circle.
  intro.
  treat_equalities.
  apply H7.
  Col.
  intro.
  treat_equalities.
  apply H7; Col.
}
assert(Perp O N C D).
{
  apply(mid_onc2__perp O  P C D N); Circle.
  intro.
  treat_equalities.
  apply H8.
  Col.
  intro.
  treat_equalities.
  apply H8; Col.
}
assert(Perp O M C D).
{
  apply (perp_col O N C D M); Col.
  intro.
  treat_equalities.
  apply H7; Col.
}
apply (l12_9 A B C D O M); Perp.
Qed.

Lemma onc3_mid2__ncol : forall O P A B C A' B',
 O <> P -> 
 OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
 Midpoint A' A C -> Midpoint B' B C -> ~ Col A B C ->
 ~ Col O A' B' \/ A' = O \/ B' = O.
Proof.
intros.
induction(Col_dec O A C).
assert(A = C \/ Midpoint O A C).
{
  unfold OnCircle in *.
  apply l7_20; eCong.
  Col.
}
induction H7.
treat_equalities.
apply False_ind.
apply H5; Col.
right; left.
apply (l7_17 A C); auto.

induction(Col_dec O B C).
assert(B = C \/ Midpoint O B C).
{
  unfold OnCircle in *.
  apply l7_20; eCong.
  Col.
}
induction H8.
treat_equalities.
apply False_ind.
apply H5; Col.
right; right.
apply (l7_17 B C); auto.
left.
intro.
assert(HH:=chords_midpoints_col_par O P A A' C B B' C H H0 H2 H1 H2 H3 H4 H8 H6 H7).
induction HH.
apply H9.
exists C.
split; Col.
spliter; contradiction.
Qed.

Lemma diam_sym : forall O P A B, Diam A B O P -> Diam B A O P.
Proof.
intros.
unfold Diam in *.
spliter.
repeat split; Between.
Qed.

Lemma diam_end_uniqueness : forall O P A B C, Diam A B O P -> Diam A C O P -> B = C.
Proof.
intros.
apply diam__midpoint in H.
apply diam__midpoint in H0.
apply (symmetric_point_uniqueness A O); Midpoint.
Qed.


Lemma center_onc2_mid__ncol : forall O P A B M ,
 O <> P -> ~ Col O A B ->
 OnCircle A O P -> OnCircle B O P ->
 Midpoint M A B  -> ~ Col A O M.
Proof.
intros.
intro.
assert_diffs.
unfold Midpoint in H3.
spliter.
apply H0.
ColR.
Qed.


Lemma bet_chord__diam_or_ncol : forall O P A B T,
  A <> B -> T <> A -> T <> B -> OnCircle A O P -> OnCircle B O P -> Bet A T B ->
  Diam A B O P \/ ~Col O A T /\ ~Col O B T.
Proof.
intros.
induction(Col_dec O A B).
left.
apply(center_col__diam); Col.
right.
split.
intro.
apply H5; ColR.
intro.
apply H5; ColR.
Qed.

Lemma mid_chord__diam_or_ncol : forall O P A B T,
 A <> B -> OnCircle A O P -> OnCircle B O P ->
 Midpoint T A B ->
 Diam A B O P \/ ~Col O A T /\ ~Col O B T.
Proof.
intros.
unfold Midpoint in H2.
spliter.
apply(bet_chord__diam_or_ncol);auto.
intro.
treat_equalities; tauto.
intro.
treat_equalities; tauto.
Qed.

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle, 
 then the point taken is the center of the circle.*)

Lemma onc4_cong2__eq: 
 forall A B C D O P X,
 A<>B -> C<>D ->
 ~ Par A B C D ->
 OnCircle A O P ->
 OnCircle B O P ->
 OnCircle C O P ->
 OnCircle D O P ->
 Cong A X B X ->
 Cong C X D X ->
 O=X.
Proof.
intros.

assert(HP:O <> P).
{
intro.
unfold OnCircle in *.
treat_equalities. intuition.
}

assert(HH:= midpoint_existence A B).
ex_and HH M.
assert(HH:= midpoint_existence C D).
ex_and HH N.

assert(Col O X M)
 by (apply(onc2_mid_cong_col O P A B M X); auto).
assert(Col O X N)
 by (apply(onc2_mid_cong_col O P C D N X); auto).

induction(eq_dec_points O X).
- auto.
- assert(Col O M N); eCol.


assert(HH1:=cong_perp_or_mid A B M X H H8 H6).
assert(HH2:=cong_perp_or_mid C D N X H0 H9 H7).

induction HH1.
subst X.
induction HH2.
subst N.

induction(Col_dec O A B).
assert(A = B \/ Midpoint O A B).
unfold OnCircle in *.
apply l7_20; Col.
apply cong_transitivity with O P; Cong.
induction H15.
contradiction.
assert(M = O).
apply (l7_17 A B); auto.
subst M; tauto.

induction(Col_dec O C D).
assert(C = D \/ Midpoint O C D).
unfold OnCircle in *.
apply l7_20; Col.
apply cong_transitivity with O P; Cong.
induction H16.
contradiction.
apply (l7_17 C D); auto.
assert(HM1:=mid_onc2__perp O P A B M H12 H H2 H3 H8).
assert(HM2:=mid_onc2__perp O P C D M H12 H0 H4 H5 H9).
apply False_ind.
apply H1.
apply (l12_9 _ _ _ _ O M); Perp.

spliter.
apply perp_in_perp in H15.
induction(Col_dec O A B).
assert(A = B \/ Midpoint O A B).
unfold OnCircle in *.
apply l7_20; Col.
apply cong_transitivity with O P; Cong.
induction H17.
contradiction.
assert(M = O).
apply (l7_17 A B); auto.
subst M; tauto.
assert(HM1:=mid_onc2__perp O P A B M H12 H H2 H3 H8).
apply(perp_col M N C D O ) in H15; Col.
apply False_ind.
apply H1.
apply (l12_9 _ _ _ _ O M); Perp.
induction HH2.
subst X.
spliter.

induction(Col_dec O C D).
assert(C = D \/ Midpoint O C D).
unfold OnCircle in *.
apply l7_20; Col.
apply cong_transitivity with O P; Cong.
induction H17.
contradiction.
apply (l7_17 C D); auto.

assert(HM1:=mid_onc2__perp O P C D N H12 H0 H4 H5 H9).
apply perp_in_perp in H15.
apply False_ind.
apply H1.
apply(perp_col N M A B O) in H15; Col.

apply (l12_9 _ _ _ _ O N); Perp.
spliter.
apply perp_in_perp in H17.
apply perp_in_perp in H16.

apply(perp_col X M A B O) in H17; Col.
apply(perp_col X N C D O) in H16; Col.
apply False_ind.
apply H1.
apply (l12_9 _ _ _ _ O X); Perp.
Qed.


End Circle_2.