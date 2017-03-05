Require Export GeoCoq.Tarski_dev.Ch11_angles.

Section Circle.

Context `{TE:Tarski_2D}.

(** P is on cercle of center A going through B *)

Definition OnCircle P A B := Cong A P A B.

(** P is inside or on the circle of center A going through B *)

Definition InCircle P A B := Le A P A B.

(** P is outside or on the circle of center A going through B *)

Definition OutCircle P A B := Le A B A P.

(** P is strictly inside the circle of center A going through B *)

Definition InCircleS P A B := Lt A P A B.

(** P is strictly outside the circle of center A going through B *)

Definition OutCircleS P A B := Lt A B A P.

Definition EqC A B C D := 
 forall X, OnCircle X A B <-> OnCircle X C D.

(** The circles of center A passing through B and
                of center C passing through D intersections
                in two distinct points P and Q. *)

Definition InterCCAt A B C D P Q :=
 ~ EqC A B C D /\
 P<>Q /\ OnCircle P C D /\ OnCircle Q C D /\ OnCircle P A B /\ OnCircle Q A B.


(** The circles of center A passing through B and
                of center C passing through D have two distinct intersections. *)

Definition InterCC A B C D :=
 exists P Q, InterCCAt A B C D P Q .

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

Lemma ninc__outcS : forall X O P, ~ InCircle X O P -> OutCircleS X O P.
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


End Circle.


Hint Resolve inc112 onc212 onc_sym inc__outc onc__inc onc__outc
             inc_outc__onc incs__inc outcs__outc : circle.

Ltac Circle := auto with circle.

Section Circle_2.


Context `{TE:Tarski_2D}.

(** If A and B are two points inside the circle (A,B) then all points on the segment AB are also
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
      apply (cong_preserves_le A P A B); Cong.
    destruct HLt as [HLe HNCong].
    apply HNCong; Cong.
  - destruct (eq_dec_points P U); try (subst; Between).
    exfalso.
    assert (HLt : Lt U A V A).
      apply (bet_le__lt P); trivial.
      apply (cong_preserves_le A P A B); Cong.
    destruct HLt as [HLe HNCong].
    apply HNCong; Cong.
Qed.

(** Given two points U and V on a circle, if P does not belong to segment UV then P is outside the circle. *)

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
      apply (cong_preserves_le A P A B); Cong.
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

Lemma outcS_exists : forall O P, exists Q, OutCircleS Q O P.
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

(** Given a circle of center O, and a ray OX there is a point on the ray which is also on strictly outside circle. *)

Lemma outcS_exists1 : forall O P X, X <> O -> exists Q, Out O X Q /\ OutCircleS Q O P.
Proof.
intros.
assert(HH:= le_cases O X O P).
induction HH.
assert(HH:=segment_construction O X O P).
ex_and HH Q.
exists Q.
split.
unfold Out.
repeat split.
auto.
intro.
subst Q.
apply between_identity in H1.
subst X.
tauto.
left.
auto.
unfold OutCircleS.

assert(HH:=segment_construction O P O X).
ex_and HH P'.
assert(Cong O Q O P').
apply cong_right_commutativity.
apply(l2_11 O X Q P' P O); Between; eCong.
unfold Lt.
split.

apply(l5_6 O P O P' O P O Q); Cong.
unfold Le.
exists P.
split; Cong.
intro.
assert(Cong O P O P').
eCong.
assert(HH:=between_cong O P' P H3 H7).
subst P'.
treat_equalities; tauto.

assert(HH:=segment_construction O X O P).
ex_and HH Q.
exists Q.
split.
unfold Out.
repeat split; auto.
intro.
subst Q.
apply between_identity in H1.
subst X.
tauto.
unfold OutCircleS.
unfold Lt.
split.

assert(HH:=segment_construction O P O X).
ex_and HH P'.
assert(Le O P O P').
unfold Le.
exists P.
split; Cong.

apply(l5_6 X Q O P' O P O Q).
unfold Le.
exists P.
split; Cong.
Cong.

apply cong_left_commutativity.

apply(l2_11 P' P O O X Q); Between; Cong.
intro.
assert(Cong O Q X Q); eCong.
apply H.

apply (between_cong Q); Between; eCong.
Qed.

(** Given a circle there is a point which is strictly inside. *)

Lemma incS_exists : forall O P, O <> P -> exists Q, InCircleS Q O P.
Proof.
intros.
exists O.
apply lt1123;auto.
Qed.

(** Given a circle of center O, and a ray OX there is a point on the ray which is also on strictly inside circle. *)

Lemma incs_exists1 : forall O P X, X <> O -> P <> O -> exists Q, Out O X Q /\ InCircleS Q O P.
Proof.
intros.
assert(HH:=midpoint_existence O P).
ex_and HH M.
unfold Midpoint in *.
spliter.
assert(HH:=segment_construction_2 X O O M H).
ex_and HH Q.
exists Q.
induction H3.

split.
unfold Out.
repeat split; auto.
intro.
treat_equalities;intuition.

unfold InCircleS.
unfold Lt.
split.
unfold Le.
exists M.
split; auto.
intro.
assert(Cong O M O P); eCong.
assert(M = P) by (apply (between_cong O); Between; Cong).
treat_equalities; tauto.

split.
unfold Out.
repeat split; auto.
intro.
treat_equalities; tauto.

unfold InCircleS.
unfold Lt.
split.

assert(Le O M O P).
unfold Le.
exists M.
split; Cong.

apply(l5_6 O M O P O Q O P); Cong.
intro.

assert(Cong O M O P); eCong.
assert(M = P).
apply (between_cong O); Between; Cong.
treat_equalities; tauto.
Qed.

(** Given a circle of center O, and a ray OX there is a point on the ray which is also on the circle. *)

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

Lemma diam_points : forall O P X, X <> O -> O <> P -> exists Q1, 
                           exists Q2, Q1 <> Q2 /\ Col O X Q1 /\ Col O X Q2 
                                               /\ OnCircle Q1 O P /\ OnCircle Q2 O P.
Proof.
intros.
assert(HH:= onc_exists O P X H H0).
ex_and HH Q1.
assert(HH:=symmetric_point_construction Q1 O).
ex_and HH Q2.
assert_diffs.
exists Q1;exists Q2.
repeat split; Col.
ColR.
unfold OnCircle in *.
unfold Midpoint in *; spliter.
eCong.
Qed.

(** The symmetric of a point on a circle relative to the center is also on the circle. *)

Lemma symmetric_oncircle : forall X Y O P, 
 Midpoint O X Y -> OnCircle X O P -> OnCircle Y O P.
Proof.
intros.
unfold Midpoint in *.
unfold OnCircle in *.
spliter.
eCong.
Qed.


Lemma onc2_mid__per : forall O P U V X,
 OnCircle U O P -> OnCircle V O P -> Midpoint X U V -> Per O X U.
Proof.
intros.
unfold Per.
exists V.
unfold OnCircle in *.
split; eCong.
Qed.

(** The line from the center of a circle to the midpoint of a chord, is perpendicular to the chord. *)

Lemma onc2_mid__perp : forall O P U V X, 
 U <> V -> ~ Col O U V -> OnCircle U O P -> OnCircle V O P -> Midpoint X U V -> Perp O X U V.
Proof.
intros.
assert(Per O X U).
apply (onc2_mid__per O P U V X); auto.
unfold Midpoint in *.
spliter.

apply per_perp_in in H4.
apply perp_in_perp in H4.
apply perp_sym.

eapply (perp_col _ X); Perp.
Col.
intro.
subst X.
apply H0; Col.
intro.
subst X.
treat_equalities; tauto.
Qed.

(** The midpoint of a chord is strictly inside the circle. *)

Lemma onc2_mid__incS : forall O P U V M, 
 U <> V -> OnCircle U O P -> OnCircle V O P -> Midpoint M U V ->
 InCircleS M O P.
Proof.
intros.
induction(Col_dec O U V).
assert(Cong O U O V).
unfold OnCircle in *.
eCong.
assert(U = V \/ Midpoint O U V).
apply(l7_20 O U V); Col.
induction H5.
contradiction.
assert(InCircle O O P).
apply inc112.
assert(M = O).
apply (l7_17 U V); auto.
subst M.
unfold InCircleS.
unfold Lt.
split.
apply le_trivial.
intro.
treat_equalities.
unfold OnCircle in *.
treat_equalities; tauto.

assert(M <> U).
intro.
subst M.
apply is_midpoint_id in H2.
contradiction.


assert(~Col O M U).
intro.
unfold Midpoint in *.
spliter.
apply H3.
ColR.

assert(HH:=onc2_mid__per O P U V M  H0 H1 H2).

assert(Per O M U \/ Obtuse O M U).
left; auto.

assert(HP:= (l11_46 O M U H5 H6)).
unfold OnCircle in *.

spliter.
unfold InCircleS.
apply (cong2_lt__lt O M O U O M O P); Cong.
apply lt_left_comm; auto.
Qed.


Lemma bet_mid_onc2__incS_aux : forall O P U V M X, 
 X <> U -> Bet M X U -> Midpoint M U V ->
 OnCircle U O P -> OnCircle V O P -> InCircleS X O P.
Proof.
intros.
assert(Cong O U O V).
unfold OnCircle in *.
eCong.

(** diametre case **)

induction(Col_dec O U V).
unfold InCircleS.
unfold Lt.
split.


assert(U = V \/ Midpoint O U V).

apply(l7_20 O U V); Col.
induction H6.
subst V.
apply l7_3 in H1.
subst M.
treat_equalities.
tauto.
assert(O = M).
apply (l7_17 U V); auto.
subst M.

apply(l5_6 O X O U O X O P); Cong.
unfold Le.
exists X.
split; Cong.
intro.

assert(U = V \/ Midpoint O U V).
apply(l7_20 O U V); Col.
induction H7.
subst V.
treat_equalities; tauto.

assert(M = O).
apply (l7_17 U V); auto.
subst M.

apply H.
unfold OnCircle in *.
apply (between_cong O );eCong.

(** general case **)

assert(HP := onc2_mid__per O P U V M H2 H3 H1).
assert(Per O M X).
apply (per_col O M U X); Col.
intro.
subst M.
treat_equalities.
apply H5; Col.

induction(eq_dec_points X M).
subst X.
apply(onc2_mid__incS O P U V M); auto.
intro.
subst V.
apply H5;Col.

assert(LtA M U O M X O /\ Lt X O U O).
apply(l11_53 U X M O); Between.
intro.
subst M.
unfold Midpoint in H1.
spliter.
apply H5.
Col.
spliter.
unfold InCircleS.

apply(cong2_lt__lt O X O U O X O P); Cong.
apply lt_comm.
assumption.
Qed.

(** If a point is strictly inside a chord, it is strictly inside the circle. *)

Lemma bet_onc2__incS : forall O P U V X,
 X <> U -> X <> V -> Bet U X V ->
 OnCircle U O P -> OnCircle V O P ->
 InCircleS X O P.
Proof.
intros.
assert(HM:=midpoint_existence U V).
ex_and HM M.
assert(Bet U M V).
unfold Midpoint in *; tauto.
assert(HH:= l5_3 U M X V H5 H1).
induction HH.
apply(bet_mid_onc2__incS_aux O P V U M X); Between.
apply(between_exchange3 U M  X V); auto.
apply l7_2; auto.
apply(bet_mid_onc2__incS_aux O P U V M X); Between.
Qed.


Lemma onc2_out__outcS_aux : forall O P U V X, 
 U <> V -> X <> V ->
 Bet U V X ->
 OnCircle U O P ->
 OnCircle V O P ->
 OutCircleS X O P.
Proof.
intros.

assert(HH:= midpoint_existence U V).
ex_and HH M.


induction(Col_dec O U V).

(** diameter case **)

assert(Cong O U O V).
unfold OnCircle in *; eCong.
unfold OutCircleS.
apply(cong2_lt__lt O V O X O P O X); Cong.
assert(U = V \/ Midpoint O U V).
apply l7_20; Col.
induction H7.
subst V.
tauto.

assert(M=O).
apply(l7_17 U V); auto.
subst M.
unfold Midpoint in *.
spliter.

assert(Bet O V X).
apply (between_exchange3 U O V X); auto.

unfold Lt.
split.
unfold Le.
exists V.
split; Cong.
intro.
apply H0.
apply sym_equal.
apply (between_cong O X V); auto.

(** general case **)

assert(Per O M V).
apply(onc2_mid__per O P V U M H3 H2).
Midpoint.

assert(LtA M X O M V O /\ Lt V O X O).
apply((l11_53 X V M O H6)).
intro.
subst M.
unfold Midpoint in *.
spliter.
apply bet_col in H4.
apply H5.
Col.
intro.
subst X.
treat_equalities;tauto.
intro.
subst M.
apply H.
apply sym_equal.
apply(is_midpoint_id V U); Midpoint.
apply between_symmetry.
apply (between_exchange3 U M V X); auto.
unfold Midpoint in *.
spliter.
auto.
spliter.
unfold OutCircleS.
assert(Cong V O O P).
unfold OnCircle in *.
eCong.
apply(cong2_lt__lt V O X O  O P O X); Cong.
Qed.

(** A circle does not cut a line at more than two points. *)

Lemma line_circle_two_points : forall O P U V W,
  U <> V -> Col U V W ->
  OnCircle U O P -> OnCircle V O P -> OnCircle W O P -> 
  W = U \/ W = V.
Proof.
intros.
induction(eq_dec_points W U).
left; auto.
induction(eq_dec_points W V).
right;auto.
unfold Col in H0.
apply False_ind.
unfold OnCircle in H3.
induction H0.
assert(OutCircleS W O P).

apply(onc2_out__outcS_aux O P U V W); auto.
unfold OutCircleS in *.
unfold Lt in *.
spliter.
apply H7; Cong.
induction H0.
assert(InCircleS W O P).
apply (bet_onc2__incS O P U V W); Between.
unfold InCircleS in H6.
unfold Lt in H6.
spliter.
apply H7; Cong.

assert(OutCircleS W O P).
apply(onc2_out__outcS_aux O P V U W); Between.
unfold OutCircleS in *.
unfold Lt in *.
spliter.
apply H7; Cong.
Qed.

(** A point is either strictly inside, on or strictly outside a circle. *)

Lemma circle_cases : forall O P X,
  OnCircle X O P \/ InCircleS X O P \/ OutCircleS X O P.
Proof.
intros.

assert (HC:= (le_cases O P O X)).
induction HC.
unfold Le in *.
ex_and H M.
induction(Cong_dec O M O X).
left.
unfold OnCircle.
eCong.
right; right.
unfold OutCircleS.
unfold Lt.
split.
unfold Le.
exists M.
split; eCong.
intro.
apply H1; eCong.

unfold Le in *.
ex_and H M.
induction(Cong_dec O  P O X).
left.
unfold OnCircle.
eCong.
right; left.
unfold InCircleS.
unfold Lt.
split.
unfold Le.
exists M.
split; eCong.
intro.
apply H1; eCong.
Qed.

End Circle_2.