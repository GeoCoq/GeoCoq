Require Import GeoCoq.Tarski_dev.Ch12_parallel.
Require Import GeoCoq.Axioms.euclidean_axioms.
Require Export GeoCoq.Axioms.continuity_axioms.
Require Export GeoCoq.Meta_theory.Continuity.elementary_continuity_props.
Require Export GeoCoq.Meta_theory.Parallel_postulates.parallel_postulates.

Section Tarski_neutral_to_Euclid_neutral.

Context `{TE:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Definition Tcircle : Type := Tpoint*Tpoint*Tpoint %type.

Definition OnCirc P (C:Tcircle) := 
  match C with 
  (X,A,B) => tarski_axioms.Cong X P A B
  end.

Definition CI (J:Tcircle) A C D := J=(A,C,D).

Definition InCirc P (J:Tcircle) :=
   match J with
  (C,A,B) => 
   exists X Y, Definitions.BetS X C Y /\ tarski_axioms.Cong C Y A B /\
               tarski_axioms.Cong C X A B /\ Definitions.BetS X P Y
  end.

Definition OutCirc P (J:Tcircle) :=
   match J with
  (C,A,B) => 
      exists X, Definitions.BetS C X P /\ tarski_axioms.Cong C X A B
 end.

Lemma on : 
 forall A B C D J, CI J A C D /\ OnCirc B J <->
                   CI J A C D /\ tarski_axioms.Cong A B C D.
Proof.
intros.
unfold CI,OnCirc.
destruct J.
destruct p.
split;intros;spliter;
split;congruence.
Qed.

Lemma inside : forall A B C J P,
  CI J C A B /\ InCirc P J <-> 
  exists X Y, CI J C A B /\ 
   Definitions.BetS X C Y /\ 
   tarski_axioms.Cong C Y A B /\ 
   tarski_axioms.Cong C X A B /\ 
   Definitions.BetS X P Y.
Proof.
intros.
unfold InCirc, CI.
destruct J;destruct p.
split.
intros;spliter.
decompose [ex and] H0;clear H0.
exists x. exists x0.
inversion H; subst; auto.
intros.
decompose [ex and] H;clear H.
inversion H0; subst;split; auto.
exists x; exists x0;auto.
Qed.


Lemma outside : forall A B C J P,
  CI J C A B /\ OutCirc P J <->
  exists X, CI J C A B /\ Definitions.BetS C X P /\
   tarski_axioms.Cong C X A B.
Proof.
intros.
unfold OutCirc, CI.
destruct J;destruct p.
split.
intros;spliter.
decompose [ex and] H0;clear H0.
exists x.
inversion H; subst; auto.
intros.
decompose [ex and] H;clear H.
inversion H1; subst;split; auto.
exists x;auto.
Qed.



End Tarski_neutral_to_Euclid_neutral.

Section circle_continuity.

Context `{T2D : Tarski_2D_euclidean}.

Lemma bet_cases : forall B C D1 D2,
 C<>B ->
 Definitions.BetS D1 B D2 ->
 Definitions.BetS D1 C D2 ->
 Definitions.BetS D1 B C \/ Definitions.BetS C B D2.
Proof.
intros.
assert (T:Bet D1 C B \/ Bet D1 B C).
  apply (l5_3 D1 C B D2);unfold Definitions.BetS in *;spliter;finish.
 destruct T.
 right.
 unfold Definitions.BetS in *;spliter.
 assert (Bet C B D2)
  by (eBetween).
 unfold Definitions.BetS.
 repeat split;auto.
 left.
 unfold Definitions.BetS.
 unfold Definitions.BetS in *;spliter;repeat split;auto.
Qed.

Lemma circle_line :
 circle_circle ->
 forall A B C K P Q,
    CI K C P Q -> InCirc B K ->  A <> B ->
    exists X Y, Definitions.Col A B X /\ Definitions.Col A B Y /\
  OnCirc X K /\ OnCirc Y K /\ Definitions.BetS X B Y.
Proof.
intros.
apply circle_circle__circle_circle_bis in H.
apply circle_circle_bis__one_point_line_circle in H.
apply one_point_line_circle__two_points_line_circle in H.
unfold CI in *.
destruct K.
destruct p.
injection H0.
intros;subst.
unfold InCirc in *.
unfold two_points_line_circle in H.

destruct H1 as [D1 [D2 [HBetS [HCongA [HCongB HBetSB]]]]].
destruct (eq_dec_points B C).
subst.
assert (HColD: Definitions.Col A C C)
   by (unfold Definitions.Col;Between).
assert (HBet: Bet C C D2) by Between.
destruct (H C D2 A C C HColD H2 HBet) as [Z1 [Z2 HZ]].
spliter.
exists Z1. exists Z2.
repeat split;try assumption.
unfold OnCircle, OnCirc in *;eCong.
unfold OnCircle, OnCirc in *;eCong.
assert (C<>D2)
 by (unfold Definitions.BetS in *;spliter;auto).
assert (Z1<>Z2) by auto.
unfold OnCircle in *.
intro;treat_equalities;intuition.
unfold OnCircle in *.
intro;treat_equalities.
unfold Definitions.BetS in *;intuition.
assert (TwoCases:Definitions.BetS D1 B C \/ Definitions.BetS C B D2)
 by (apply bet_cases;auto).
destruct TwoCases.
- assert (HColD: Definitions.Col A B B)
   by (unfold Definitions.Col;Between).
assert (HBet:Bet C B D1)
 by (unfold Definitions.BetS in *;spliter;finish).
destruct (H C D1 A B B HColD H2 HBet)
 as [Z1 [Z2 HZ]].
exists Z1.
exists Z2.
spliter.
assert (B<>D1)
 by (unfold Definitions.BetS in *;spliter;auto).
assert (Z1<>Z2) by auto.
assert (Z1<>B).
{
 intro. subst.
 unfold OnCircle in *.
 assert (B=D1) by (apply between_cong with C;finish).
 subst. intuition.
}
assert_diffs.
assert (B<>Z2).
{
 intro. subst.
 assert (Bet C Z2 D1) 
  by (unfold BetS in *;spliter;finish).
 unfold OnCircle in *.
 assert (Z2=D1)
  by (apply between_cong with C;finish).
 intuition.
}
assert (Definitions.BetS Z1 B Z2)
 by (unfold Definitions.BetS;auto).
unfold OnCirc;simpl.
unfold OnCircle in *.
repeat split; eCong.
- assert (HColD: Definitions.Col A B B)
   by (unfold Definitions.Col;Between).
assert (HBet:Bet C B D2)
 by (unfold Definitions.BetS in *;spliter;finish).
destruct (H C D2 A B B HColD H2 HBet)
 as [Z1 [Z2 HZ]].
exists Z1.
exists Z2.
spliter.
assert (B<>D2)
 by (unfold Definitions.BetS in *;spliter;auto).
assert (Z1<>Z2) by auto.
assert (Z1<>B).
{
 intro. subst.
 unfold OnCircle in *.
 assert (B=D2) by (apply between_cong with C;finish).
 subst. intuition.
}
assert_diffs.
assert (B<>Z2).
{
 intro. subst.
 assert (Bet C Z2 D2) 
  by (unfold BetS in *;spliter;finish).
 unfold OnCircle in *.
 assert (Z2=D2)
  by (apply between_cong with C;finish).
 intuition.
}
assert (Definitions.BetS Z1 B Z2)
 by (unfold Definitions.BetS;auto).
unfold OnCirc;simpl.
unfold OnCircle in *.
repeat split; eCong.
Qed.

Lemma circle_circle:
 circle_circle ->
 forall C D F G J K P Q R S,
    CI J C R S -> InCirc P J ->
    OutCirc Q J -> CI K D F G ->
    OnCirc P K -> OnCirc Q K ->
    exists X, OnCirc X J /\ OnCirc X K.
Proof.
intros.
unfold circle_circle in H.
destruct J.
destruct p.
destruct K.
destruct p.
unfold CI in *.
injection H0;intros;subst.
injection H3;intros;subst.
clear H0 H3.
unfold OnCirc in *.
unfold InCirc in *.
destruct H1 as [D1 [D2 HD]].
spliter.
unfold OutCirc in *.
destruct H2 as [X HX].
spliter.
assert (OnCircle P D Q)
 by (unfold OnCircle;eCong).
assert (OnCircle Q D Q)
 by (unfold OnCircle;eCong).
assert (InCircle P C D1).
{
 unfold InCircle.
 destruct (eq_dec_points C P).
 subst. apply le_trivial.
 assert (TwoCases:Definitions.BetS D1 P C \/ Definitions.BetS C P D2)
  by (apply bet_cases;auto).
 destruct TwoCases.
 exists P.
 split; unfold Definitions.BetS in *;spliter; finish.
 apply l5_6 with C P C D2.
 exists P.
 split; unfold Definitions.BetS in *;spliter; finish.
 finish.
 eCong.
}
assert (OutCircle Q C D1).
{
 unfold OutCircle.
 exists X.
 split; unfold Definitions.BetS in *;spliter; eCong.
}
assert (Hex: exists Z : Tpoint, OnCircle Z C D1 /\ OnCircle Z D Q) by eauto.
destruct Hex as [Z HZ].
exists Z.
unfold OnCircle in *;spliter;split;eCong.
Qed.

End circle_continuity.

Section Neutral.

Context `{TE:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Instance Euclid_neutral_follows_from_Tarski_neutral : euclidean_neutral.
Proof.
eapply (Build_euclidean_neutral Tpoint Tcircle tarski_axioms.Cong Tarski_dev.Definitions.BetS InCirc OnCirc OutCirc tarski_axioms.PA tarski_axioms.PB tarski_axioms.PC CI).
- intros;congruence.
- intros;apply cong_transitivity with P Q;finish.
- intro;reflexivity.
- intro;finish.
- intro;finish.
- intros. elim (eq_dec_points A B);intuition.
- intros;subst;assumption.
- intros;exists (C,A,B);reflexivity.
- intros; apply inside.
- intros; apply outside.
- intros. apply on.
- assert (T:=lower_dim).
  split.
  intro H;rewrite H in *;apply T;Between.
  split.
  intro H;rewrite H in *;apply T;Between.
  split.
  intro H;rewrite H in *;apply T;Between.
  split.
  unfold Definitions.BetS in *;intuition.
  unfold Definitions.BetS in *;intuition.
- intros; unfold Definitions.BetS;
intro;spliter;treat_equalities;intuition.
- intros;unfold Definitions.BetS in *;
intros;spliter;finish.
- intros;unfold Definitions.BetS in *;
intros;spliter;try assumption;eBetween.
- intros;unfold Definitions.BetS in *;
intros;spliter .
assert (Bet A B C \/ Bet A C B) by (apply l5_3 with D;auto).
assert (~ (Bet A C B /\ A <> C /\ B <> C)) by intuition.
assert (T3:=eq_dec_points A B).
assert (T4:=eq_dec_points A C).
assert (T5:=eq_dec_points B C).
tauto.
- intros;treat_equalities;finish.
- intros;finish.
- intros.
assert (tarski_axioms.Cong C D c d)
 by (apply (five_segment A a B b C c D d);
unfold Definitions.BetS in *;spliter;auto).
finish.
- intros.
 destruct (segment_construction A B C D) as [X [HXa HXb]].
 exists X; split;unfold Definitions.BetS;assert_diffs;auto.
- intros.
 destruct (segment_construction A B C D) as [X [HXa HXb]].
 exists X;unfold Definitions.BetS;intuition.
- intros;unfold Definitions.BetS in *;spliter.
  destruct (inner_pasch A B C P Q H H0) as [X [HXa HXb]]. 
  exists X.
  assert_diffs.
  assert (~ Bet A C B) by tauto.
  assert (B<>C) by auto.
  assert (~ Bet A B C) by tauto.
  assert (C<>A) by auto.
  assert (~ Bet C A B) by tauto.
  assert (~ Bet B C A) by Between.
  repeat split;Between.

 all:intro;treat_equalities;assert_cols;
 assert (HCol:Definitions.Col A B C) by ColR;
 unfold Definitions.Col in HCol;
 tauto.
- intros;unfold Definitions.BetS in *;spliter.
  assert (~ Bet B Q A) by tauto.
  assert (A<>Q) by auto.
  assert (~ Bet B A Q) by tauto.
  assert (B<>A) by auto.
  assert (Q<>B) by auto.
  assert (~ Bet Q B A) by tauto.
 assert (~ Bet A Q B) by finish.
  assert (Bet Q C B) by finish.
  destruct (outer_pasch Q A C B P H18 H) as [X [HXa HXb]].
  exists X.
   assert_diffs.
  repeat split;Between.
  intro;treat_equalities;assert_cols;
 assert (HCol:Definitions.Col B A Q) by ColR;
 unfold Definitions.Col in HCol;tauto.
  intro;treat_equalities;assert_cols;
 assert (HCol:Definitions.Col B A X) by ColR;
 unfold Definitions.Col in HCol;tauto.
  intro;treat_equalities;assert_cols;
  assert (HCol:Definitions.Col A Q B) by ColR;
  unfold Definitions.Col in HCol;tauto.
  intro;treat_equalities;assert_cols;
  assert (HCol:Definitions.Col A Q B) by ColR;
  unfold Definitions.Col in HCol;tauto.
Defined.

End Neutral.


Section RulerAndCompass.

Context `{T2D : Tarski_2D_euclidean}.

Instance En :euclidean_neutral.
Proof.
apply Euclid_neutral_follows_from_Tarski_neutral.
Defined.

Lemma BetS_BetS : forall A B C,
 Definitions.BetS A B C <-> BetS A B C.
Proof.
intros.
unfold BetS;simpl.
intuition.
Qed.

Lemma Col_Col : forall A B C,
 Definitions.Col A B C <-> Col A B C.
Proof.
intros.
unfold Definitions.Col, Col, BetS.
simpl.
unfold Definitions.BetS,eq.
split.
intros.
destruct (eq_dec_points A B).
left;auto.
destruct (eq_dec_points A C).
right;left;auto.
destruct (eq_dec_points B C).
right;right;left;auto.
decompose [or] H.
right;right;right;right;left;auto.
right;right;right;right;right;finish.
right;right;right;left;finish.
intros.
decompose [or] H;subst;spliter;finish.
Qed.

Lemma nCol_not_Col : forall A B C,
 nCol A B C -> ~ Col A B C.
Proof.
unfold nCol.
unfold Col.
intuition.
Qed.

Lemma Euclid5 :
   forall a p q r s t,
    BetS r t s -> BetS p t q -> BetS r a q ->
    Cong p t q t -> Cong t r t s -> nCol p q s ->
    exists X, BetS p a X /\ BetS s q X.
Proof.
intros.
assert (T:tarski_s_parallel_postulate -> 
        euclid_5).
{
 assert (T:=equivalent_postulates_without_decidability_of_intersection_of_lines_bis).
 unfold all_equiv.all_equiv in *.
 apply T;simpl;auto 10.
}
assert (T2:euclid_5).
apply T.
unfold tarski_s_parallel_postulate.
apply euclid.
unfold euclid_5 in *.
assert (T3:exists I : Tpoint, Definitions.BetS s q I /\ Definitions.BetS p a I).
apply (T2 p q r s t a);
auto using BetS_BetS.
unfold BetS in *;simpl in *;
unfold Definitions.BetS in *;spliter;finish.
intro HnCol.
apply Col_Col in HnCol.
apply nCol_not_Col in H4;intuition.
finish.
destruct T3 as [X HX].
exists X;spliter;auto.
Qed.


Lemma Euclid_neutral_ruler_compass_follows_from_Tarski_2D :
 continuity_axioms.circle_circle ->
  (euclidean_neutral_ruler_compass En).
Proof.
intros.
split.
-simpl.
intros.
destruct (circle_line H A B C K P Q H0 H1 H2)
as [X [Y HXY]].
spliter.
exists X.
exists Y.
split.
apply (Col_Col A B X);auto.
split.
apply (Col_Col A B Y);auto.
auto.
- simpl.
eauto using circle_circle.
Qed.

Lemma Euclid_follows_from_Tarski_2D :
 forall (H:continuity_axioms.circle_circle), 
 euclidean_euclidean (Euclid_neutral_ruler_compass_follows_from_Tarski_2D H) .
Proof.
intros.
split.
apply Euclid5.
Qed.

End RulerAndCompass.








