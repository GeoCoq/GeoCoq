Require Import GeoCoq.Algebraic.Counter_models.nD.independent_version.
Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Main.Meta_theory.Models.gupta_inspired_to_tarski.
Require Export GeoCoq.Main.Tarski_dev.Ch12_parallel_inter_dec.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Section Gupta_inspired_variant_of_Tarski_neutral_dimensionless_to_independent_Tarski_neutral_dimensionless.

Context `{GTnEQD : Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet__col : forall A B C, BetG A B C -> Col A B C.
Proof. intros A B C HABC; left; auto. Qed.

Ltac not_exist_hyp_perm_col A B C :=
  not_exist_hyp (Col A B C); not_exist_hyp (Col A C B);
  not_exist_hyp (Col B A C); not_exist_hyp (Col B C A);
  not_exist_hyp (Col C A B); not_exist_hyp (Col C B A).

Ltac assert_cols :=
  repeat
    match goal with
    | H:BetG ?X1 ?X2 ?X3 |- _ =>
      not_exist_hyp_perm_col X1 X2 X3;
      assert (Col X1 X2 X3) by (apply bet_col;apply H)
    end.

Global Instance GI_to_IT : independent_Tarski_neutral_dimensionless TpointG.
Proof.
apply (Build_independent_Tarski_neutral_dimensionless
         TpointG BetG CongG
         cong_pseudo_reflexivityG cong_inner_transitivityG cong_identityG);
[|exact five_segmentG| |exact bet_symmetryG|exact bet_inner_transitivityG].

  {
  intros A B C D HAB; destruct (segment_constructionG A B C D) as [E []].
  exists E; auto.
  }

  {
  intros A B C P Q HAPC HBQC HAP HPC HBQ HQC H.
  assert (HNC : ~ Col A B C) by (unfold Col, independence.Col in *; tauto).
  clear H.
  assert (HAC : A <> C) by (intro; treat_equalities; Col).
  assert (HBC : B <> C) by (intro; treat_equalities; Col).
  assert (HPQ : P <> Q).
    {
    intro; treat_equalities; apply HNC; assert_cols;
    apply col_permutation_3, col_transitivity_1 with P; Col.
    }
  destruct (inner_paschG A B C P Q) as [X []]; auto; exists X; split; auto.
  }
Defined.

End Gupta_inspired_variant_of_Tarski_neutral_dimensionless_to_independent_Tarski_neutral_dimensionless.

Section Gupta_inspired_variant_of_Tarski_euclidean_to_Tarski_euclidean.

Context `{GTE : Gupta_inspired_variant_of_Tarski_euclidean}.

Global Instance GI_euclidean_to_IT_euclidean :
  independent_Tarski_euclidean GI_to_IT.
Proof.
assert (HC : forall A B C,
           independence.Col Tpoint Bet A B C <-> @Col GI_to_T A B C).
  {
  intros A B C; split; [|intros [HF|[HF|HF]]; intros [HB1 [HB2 HB3]]; tauto].
  intros HC; elim (col_dec A B C); [auto|intro HF; exfalso].
  apply HC. split; [intro HB|split; intro HB]; apply HF; [left|right..]; auto.
  }
split; assert (HP : @triangle_circumscription_principle GI_to_T).
  {
  assert (tarski_s_parallel_postulate);
  [unfold tarski_s_parallel_postulate; apply euclidT|revert H].
  apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
  simpl; tauto.
  }
intros A B C HNC.
destruct (HP A B C) as [X [HC1 [HC2 HCop]]]; [intro HF; apply HNC, HC, HF|].
exists X; split; [|split; [|apply Cop__Coplanar in HCop]]; auto.
clear HNC; destruct HCop as [E [F [G HCop]]]; exists E, F, G.
destruct HCop as [HNC [HCopA [HCopB [HCopC HCopD]]]].
split; [intro HF; apply HNC, HC; auto|].
cut (forall P X Y Z,
        InPlane P X Y Z -> independence.InP TpointG Bet P X Y Z);
[intro H; repeat split; apply H; auto|clear - GTE HC; intros P X Y Z].
intros [Q []]; exists Q; split; apply HC; auto.
Defined.

End Gupta_inspired_variant_of_Tarski_euclidean_to_Tarski_euclidean.

Require Import Description.

Section Gupta_inspired_variant_of_Tarski_2D_to_independent_Tarski_2D.

Context `{GT2D : Gupta_inspired_variant_of_Tarski_2D}.

Lemma segment_constructionG_f : forall A B C D,
  A <> B -> {X | BetG A B X /\ CongG B X C D}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply segment_constructionG; auto|].
intros X Y [HBX HCX] [HBY HCY]; apply between_cong_3 with A B; auto.
apply cong_inner_transitivityG with C D; auto.
Qed.

Lemma exists_cong_per_f : forall (A B C D E : TpointG),
  A <> B -> C <> D -> ~ Col A B E ->
  {X : TpointG | Per A B X /\ CongG B X C D /\ OS A B E X}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence;
split; [destruct (@ex_per_cong GI_to_T GI_to_T_PED A B B E C D) as [X [HP []]];
        Col; exists X; split; [apply l8_2; auto|split; [apply g2_3|]; Side]|].
intros X Y [HPX [HCX HOX]] [HPY [HCY HOY]].
elim (@cong_cop_per2_1  GI_to_T GI_to_T_PED A B X Y);
auto; [|apply cong_inner_transitivityG with C D; auto|
       apply coplanar_trans_1 with E; Col; Cop].
intros [HF _]; exfalso; apply l9_9 with A B X Y;
[apply invert_two_sides, bet__ts|apply one_side_transitivity with E; Side];
[intro; treat_equalities; apply g2_5 in HCY; tauto| |auto].
apply not_col_permutation_4, per_not_col; auto.
intro; treat_equalities; apply g2_5 in HCX; tauto.
Qed.

Lemma basisG :
  {b : 2.-tuple TpointG |
   Bet GPB GPA (tnth b (inord 0)) /\ Cong GPA (tnth b (inord 0)) GPA GPB /\
   Cong GPA (tnth b (inord 1)) GPA GPB /\
   Cong (tnth b (inord 0)) (tnth b (inord 1)) GPB (tnth b (inord 1))}.
Proof.
assert (HNC := lower_dimG).
assert (HAB : GPA <> GPB)
  by (intro; apply HNC; rewrite H; left; apply bet_symmetryG, between_trivialT).
destruct (segment_constructionG_f GPB GPA GPA GPB) as [U1 [HB HC1]]; [auto|].
destruct (exists_cong_per_f U1 GPA GPA GPB GPC) as [U2 [HP [HC2 _]]]; auto;
[intro H; rewrite H in HC1; apply g2_5 in HC1; tauto| |].

  {
  intro HF; apply HNC; cut (Col GPA GPB GPC); auto.
  assert (GPA <> U1) by (intro; treat_equalities; apply g2_5 in HC1; tauto).
  apply col_transitivity_1 with U1; Col.
  }

  {
  exists (cons_tuple U1 (cons_tuple U2 (nil_tuple TpointG))).
  unfold tnth; rewrite 2?inordK //=.
  split; [auto|split; [auto|split; [auto|]]].
  apply l8_2 in HP; destruct HP as [GPB' [HM HC]].
  cut (GPB = GPB'); [intro; subst; apply g2_4, g2_3; auto|].
  apply (@symmetric_point_uniqueness GI_to_T GI_to_T_PED) with U1 GPA; auto.
  split; [apply bet_symmetryG|apply g2_3]; auto.
  }
Qed.

Global Instance GI2D_to_T2D : independent_Tarski_nD 2 GI_to_IT.
Proof.
destruct basisG as [b Hb].
apply (Build_independent_Tarski_nD 2 TpointG GI_to_IT GPA GPB b).

  {
  assert (HNC := lower_dimG); split.

    {
    intro HR1; assert (HR2 : GPB = GPA).
      {
      destruct Hb as [HB _]; rewrite -HR1 in HB; apply between_identityT, HB.
      }
    apply HNC; rewrite HR2; right; right; apply between_trivialT.
    }

    {
    move: Hb; case/tupleP: b => U1 b; case/tupleP: b => U2 b.
    have: (b = nil_tuple TpointG)=> [|-> /=]; first by rewrite tuple0 //.
    rewrite 2?big_ltn // big_geq // 2?big_ltn // big_geq // big_ltn //.
    rewrite 2?big_geq //; unfold tnth; rewrite 2?inordK //=.
    move=> [HB [HC1 [HC2 HC3]]]; apply g2_2 in HC1; apply g2_2 in HC2; tauto.
    }
  }

  {
  move => P; rewrite /= 2?big_ltn // big_geq // 2?big_ltn // big_geq // => _.
  rewrite 2?big_ltn // big_geq // 2?big_ltn // big_geq //.
  rewrite big_ltn // 2?big_geq //; destruct b as [b bP].
  move: bP Hb; case b => {b} //= U1 b; case b => {b} //= U2 b.
  case b => //= bP Hb; rewrite /belast_tuple /rot_tuple /tnth /seq.nth /seq.rot.
  rewrite !inordK //= => [[HNE1 [HBet1 [[_ [HC4 _]] [[HC5 _] _]]]] HNE2].
  move: Hb; rewrite /tnth !inordK //=; move => [_ [HC1 [HC2 HC3]]].
  have HP1 : @Per GI_to_T U2 GPA U1 by exists GPB; split; [split|]; finish.
  have HP2 : @Per GI_to_T P  GPA U1 by exists GPB; split; [split|]; finish.
  have {bP} HCol : @Col GI_to_T P U2 GPA.
  - apply (@per2__col GI_to_T GI_to_T_PED GI2D_to_T2D _ _ U1); finish.
    intro; apply HNE1; treat_equalities.
    apply (@cong_reverse_identity GI_to_T GPA); Cong.
  have HC6 : (@Cong GI_to_T GPA P GPA U2) by eCong.
  elim (@l7_20 GI_to_T GI_to_T_PED GPA P U2); finish.
  - by intro; treat_equalities; tauto.
  - by move => [HBet2 _]; apply (@between_symmetry GI_to_T); auto.
  }
Defined.

End Gupta_inspired_variant_of_Tarski_2D_to_independent_Tarski_2D.
