Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Meta_theory.Models.beeson_to_tarski.
Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_2.
Require Import GeoCoq.Tarski_dev.Ch05_bet_le.
Require Export GeoCoq.Meta_theory.Parallel_postulates.parallel_postulates.
Require Import GeoCoq.Meta_theory.Counter_models.coplanarity.
Require Import GeoCoq.Meta_theory.Counter_models.nD.independence.
Require Import GeoCoq.Meta_theory.Counter_models.nD.independent_version.
Require Import GeoCoq.Meta_theory.Counter_models.nD.bet_identity.
Require Import GeoCoq.Meta_theory.Counter_models.nD.stability_properties.
Require Import GeoCoq.Meta_theory.Counter_models.nD.stronger_pasch.
Require Import GeoCoq.Meta_theory.Counter_models.nD.independent_version_to_beeson.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq tuple fintype bigop order.

Section altITn_to_Tn.

Variable n : nat.
Variable Tpoint : Type.

Context {ITn : independent_Tarski_neutral_dimensionless(Tpoint)}.
Context {ED : Eq_decidability(ITn)}.
Context {ITnD : independent_Tarski_nD(n.+2)(ITn)}.

Instance Estability : Eq_stability(ITn).
Proof.
split; intros A B HAB; elim (point_equality_decidability A B); tauto.
Defined.

Lemma bet_axx : forall A B, Bet A B B.
Proof.
assert (HOI := two_points n.+1).
intros A B; elim (point_equality_decidability A B); intro HAB;
[subst; destruct (another_point O I B HOI) as [A HAB]|apply g2_6_1; auto].
apply bet_inner_transitivity with A; apply bet_symmetry, g2_6_1; auto.
Qed.

Instance altIT_to_T : Tarski_neutral_dimensionless.
Proof.
apply (@IT_to_T (@altIT_to_IT n Tpoint ITn Estability ITnD)).
Defined.

Instance altIT_to_T_PED :
  Tarski_neutral_dimensionless_with_decidable_point_equality altIT_to_T.
Proof. split; apply point_equality_decidability. Defined.

End altITn_to_Tn.

Section altIT2D_to_T2D.

Variable Tpoint : Type.

Context {ITn : independent_Tarski_neutral_dimensionless(Tpoint)}.
Context {ED : Eq_decidability(ITn)}.
Context {IT2D : independent_Tarski_nD(2)(ITn)}.

Definition Col := independence.Col Tpoint Bet.

Instance altIT2D_to_T2D : Tarski_2D (@altIT_to_T_PED 0 Tpoint ITn ED IT2D).
Proof.
split; cut (@upper_dim_axiom (altIT_to_T 0 Tpoint)).
- by intros UPD A B C P Q HPQ HC1 HC2 HC3; destruct (UPD A B C P Q); auto.
apply (@all_coplanar_implies_upper_dim _ (altIT_to_T_PED 0 Tpoint)).
pose IPA := @O _ _ _ IT2D; pose IPB := (tnth (@basis _ _ _ IT2D) (inord 0)).
pose IPC := (tnth (@basis _ _ _ IT2D) (inord 1)).
assert (HNC : ~ @Definitions.Col (altIT_to_T 0 Tpoint) IPA IPB IPC).
- assert (HNC := @ITlower_dim _ _ _ IT2D).
  assert (HIPA : independent_version_to_beeson.IPA 0 = IPA) by auto.
  rewrite HIPA in HNC; clear HIPA.
  assert (HIPB : independent_version_to_beeson.IPB 0 = IPB) by auto.
  rewrite HIPB in HNC; clear HIPB.
  assert (HIPC : independent_version_to_beeson.IPC 0 = IPC) by auto.
  rewrite HIPC in HNC; clear HIPC.
  cut (forall A B C, @tarski_axioms.Bet (altIT_to_T 0 Tpoint) A B C ->
                     IT A B C).
  + intro HBIT; destruct HNC as [HNB1 [HNB2 HNB3]].
    intros [HB1|[HB2|HB3]]; [apply HNB3| |apply HNB1]; try apply HBIT; auto.
    by apply HNB2, HBIT, between_symmetry; auto.
  clear IPA IPB IPC HNC; intros A B C.
  by unfold tarski_axioms.Bet; simpl; unfold BetT, IT; intuition.
cut (forall P, @Definitions.Coplanar (altIT_to_T 0 Tpoint) IPA IPB IPC P).
- cut (~ @Definitions.Col (altIT_to_T 0 Tpoint) IPA IPB IPC); auto.
  by intros ? ? A B C D;
     apply (@coplanar_pseudo_trans _ (altIT_to_T_PED 0 Tpoint)
                                   _ _ _ _ IPA IPB IPC); Col.
intro P; elim (@cop_dec _ (altIT_to_T_PED 0 Tpoint) IPA IPB IPC P); auto.
intro HNCop; assert (HE := @ex_per_cong  _ (altIT_to_T_PED 0 Tpoint)).
assert (HNE : IPA <> IPB) by (intro H; apply HNC; rewrite H; Col).
assert (HP : ~ @Definitions.Col (altIT_to_T 0 Tpoint) IPA IPB P)
  by (intro; apply HNCop; Cop).
exfalso; destruct (HE IPB IPA IPA P IPA IPB) as [IPC' [Per [Cong OS]]]; Col.
clear HE; cut (@Definitions.Col (altIT_to_T 0 Tpoint) IPC O IPC').
- assert (HNC' : ~ @Definitions.Col (altIT_to_T 0 Tpoint) IPB IPA IPC')
    by (apply (one_side_not_col123 _ _ _ P); auto).
  intro HC; apply HNCop.
  apply (@coplanar_pseudo_trans _ (altIT_to_T_PED 0 Tpoint)
                                _ _ _ _ IPB IPA IPC'); Cop.
  by apply (@os__coplanar _ (altIT_to_T_PED 0 Tpoint)); auto.
cut (Bet IPC O IPC').
- unfold Definitions.Col, tarski_axioms.Bet; simpl.
  by unfold BetT, beeson_s_axioms.IBet; simpl; unfold BetS; tauto.
assert (H := upper_dim IPC'); revert H; unfold upper_dimP; clear HNE.
assert (HNE : IPC <> IPC').
- elim (point_equality_decidability IPC IPC'); auto.
  intro HE; exfalso; apply HNCop; subst.
  cut (@Definitions.Coplanar (altIT_to_T 0 Tpoint) IPB IPA IPC P); Cop.
  by apply (@os__coplanar _ (altIT_to_T_PED 0 Tpoint)); auto.
pose new_basis := rot_tuple 1 (belast_tuple IPC' (@basis _ _ _ IT2D)).
have basisP : basis = cons_tuple IPB (cons_tuple IPC (nil_tuple Tpoint)).
- apply eq_from_tnth => i; suff: (i == inord 0) || (i == inord 1)
    by move => /orP[/eqP->|/eqP->]; rewrite -?/IPB -?/IPC /tnth inordK.
  rewrite /inord /ord0; case i => [] [|[|//]] p /=.
  + suff /eqP-> : Ordinal (n:=2) (m:=0) p =
                  insubd (Ordinal (n:=2) (m:=0) (ltn0Sn 1)) 0 by rewrite orTb.
    by apply: val_inj; rewrite val_insubd p.
  + suff /eqP-> : Ordinal (n:=2) (m:=1) p =
                   insubd (Ordinal (n:=2) (m:=0) (ltn0Sn 1)) 1 by rewrite orbT.
    by apply: val_inj; rewrite val_insubd p.
cut (orthonormal_basis tarski_axioms.Tpoint Bet independent_version.Cong 2 O I
                                            new_basis);
first by move => nbP udP; apply udP; destruct lower_dim as [LD1 LD2].
rewrite /orthonormal_basis /new_basis 2?big_ltn // big_geq // 2?big_ltn //.
rewrite big_geq // big_ltn // !big_geq //; clear new_basis OS.
have [-> ->] : tnth (rot_tuple 1 (belast_tuple IPC' basis)) (inord 0) = IPB /\
               tnth (rot_tuple 1 (belast_tuple IPC' basis)) (inord 1) = IPC'.
- rewrite !(tnth_nth IPA) /belast_tuple /rot_tuple /rot /= basisP.
  by rewrite /belast /nth !inordK.
destruct lower_dim as [HF [HB2 [HBC1 HBC2]]].
move: HBC1; rewrite 2?big_ltn // big_geq //; move => [HC1 [HC2 _]].
move: HBC2; rewrite 2?big_ltn // big_geq // big_ltn // !big_geq //.
move => [[HC3 _] _]; split; auto; split; auto; split.
- split; [rewrite /IPB //|split; auto].
  apply (ITcong_inner_transitivity IPA IPB); apply g2_2 => //.
  by apply g2_3.
split; auto; split; auto.
cut (@tarski_axioms.Cong (altIT_to_T 0 Tpoint) IPB IPC' I IPC');
first by rewrite /tarski_axioms.Cong /=.
destruct Per as [I' [HI' HC5]]; assert (HI : I = I'); [|by rewrite HI; Cong].
apply (@symmetric_point_uniqueness _ (altIT_to_T_PED 0 Tpoint) IPB IPA); auto.
split; Cong; apply between_symmetry; unfold IPA, IPB, tarski_axioms.Bet.
by simpl; unfold BetT, beeson_s_axioms.IBet; simpl; unfold BetS; tauto.
Qed.

End altIT2D_to_T2D.

Section altITE_to_TE.

Variable n : nat.
Variable Tpoint : Type.

Context {ITn : independent_Tarski_neutral_dimensionless(Tpoint)}.
Context {ED : Eq_decidability(ITn)}.
Context {ITnD : independent_Tarski_nD(n.+2)(ITn)}.
Context {TE : independent_Tarski_euclidean(ITn)}.

Lemma Col_TCol : forall A B C,
  Col Tpoint A B C <->
  @Definitions.Col (altIT_to_T n Tpoint) A B C.
Proof.
intros A B C; split; [intro HC|].

  {
  elim (@col_dec (altIT_to_T n Tpoint) (altIT_to_T_PED n Tpoint) A B C); auto.
  intro HNC; exfalso; apply HC; clear HC; split; [|split]; intro HB;
  apply HNC; [left|right; left|right; right]; simpl; left; split; try split;
  try solve [intro; subst; Col]; auto.
  }

  {
  intros [HB|[HB|HB]]; intros [HB1 [HB2 HB3]];
  [apply HB1|apply HB2|apply HB3];
  simpl in HB; unfold BetT in HB;
  destruct HB as [[_ [_ HB]]|[HE|HE]]; auto; subst;
  try apply (bet_axx n); auto; apply bet_symmetry, (bet_axx n); auto.
  }
Qed.

Lemma NCol_TNCol : forall A B C,
  ~ Col Tpoint A B C <-> ~ @Definitions.Col (altIT_to_T n Tpoint) A B C.
Proof. intros A B C; split; intros HNC1 HNC2; apply HNC1, Col_TCol, HNC2. Qed.

Lemma Col_dec : forall A B C, Col Tpoint A B C \/ ~ Col Tpoint A B C.
Proof.
intros A B C; elim (@col_dec (altIT_to_T n Tpoint)
                             (@altIT_to_T_PED n Tpoint ITn ED ITnD) A B C);
intro HC; [left; apply Col_TCol|right; apply NCol_TNCol]; auto.
Qed.

Lemma Cop_TCop : forall A B C D,
  Coplanar Tpoint Bet A B C D <->
  @Definitions.Coplanar (altIT_to_T n Tpoint) A B C D.
Proof.
assert (HX : forall (P A B C : Tpoint),
           InP Tpoint Bet P A B C <-> @InPlane (altIT_to_T n Tpoint) P A B C).
  {
  intros P A B C; split; intros [Q []]; exists Q; split; apply Col_TCol; auto.
  }
intros A B C D; split; intro HCop;
[apply (@Cop__Coplanar (altIT_to_T n Tpoint)
                       (@altIT_to_T_PED n Tpoint ITn ED ITnD))|
 apply (@Cop__Coplanar (altIT_to_T n Tpoint)
                       (@altIT_to_T_PED n Tpoint ITn ED ITnD)) in HCop];
destruct HCop as [E [F [G HCop]]]; exists E, F, G;
split; [spliter; apply NCol_TNCol; auto| |spliter; apply NCol_TNCol; auto|];
spliter; repeat split; apply HX; auto.
Qed.

Lemma Coplanar_dec : forall A B C D,
  Coplanar Tpoint Bet A B C D \/ ~ Coplanar Tpoint Bet A B C D.
Proof.
intros A B C D; elim (Col_dec A B C); intro HC1;
[left; apply Cop_TCop, col__coplanar, Col_TCol; auto|].
elim (Col_dec A B D); intro HC2;
[left; apply Cop_TCop, coplanar_perm_1, col__coplanar, Col_TCol; auto|].
elim (@two_sides_dec (altIT_to_T n Tpoint)
                     (@altIT_to_T_PED n Tpoint ITn ED ITnD)
                     A B C D); intro HTS;
[left; apply Cop_TCop, ts__coplanar; auto|].
elim (@one_side_dec (altIT_to_T n Tpoint)
                    (@altIT_to_T_PED n Tpoint ITn ED ITnD)
                    A B C D); intro HOS;
[left; apply Cop_TCop|
 right; intro HC; apply HOS;
 apply (@cop_nts__os (altIT_to_T n Tpoint)
                     (@altIT_to_T_PED n Tpoint ITn ED ITnD)); auto];
[|apply Cop_TCop|cut (~ @Definitions.Col (altIT_to_T n Tpoint) A B C); Col|
 cut (~ @Definitions.Col (altIT_to_T n Tpoint) A B D); Col]; auto;
[|apply NCol_TNCol; auto..].
apply (@os__coplanar (altIT_to_T n Tpoint)
                     (@altIT_to_T_PED n Tpoint ITn ED ITnD)); auto.
Qed.

Instance altIT_euclidean_to_T_euclidean :
  Tarski_euclidean (@altIT_to_T_PED n Tpoint ITn ED ITnD).
Proof.
split; cut (@tarski_s_parallel_postulate (altIT_to_T n Tpoint));
[rewrite /tarski_s_parallel_postulate //|].
cut (@triangle_circumscription_principle (altIT_to_T n Tpoint));
[apply (@equivalent_postulates_without_decidability_of_intersection_of_lines_bis
          (altIT_to_T n Tpoint) (@altIT_to_T_PED n Tpoint ITn ED ITnD));
 simpl; tauto|intros A B C HNC].
elim (point_equality_decidability A B); elim (point_equality_decidability A C);
elim (point_equality_decidability B C); intros; [subst; exfalso; apply HNC..|];
Col; destruct (euclid A B C) as [X [HC1 [HC2 HCop]]]; [apply NCol_TNCol|]; Col.
exists X; repeat split; [..|apply Cop_TCop]; auto.
Defined.

End altITE_to_TE.
