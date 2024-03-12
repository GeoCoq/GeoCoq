Require Import GeoCoq.Meta_theory.Counter_models.nD.independence.
Require Import GeoCoq.Meta_theory.Counter_models.nD.independent_version.
Require Import GeoCoq.Meta_theory.Counter_models.nD.bet_identity.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Section Stability_properties.

Variable n : nat.

Context `{ITnD : independent_Tarski_nD(n.+1)}.

Definition BetS A B C := A <> B /\ B <> C /\ Bet A B C.

Definition Bstability := forall A B C,
  ~ ~ BetS A B C -> BetS A B C.

Definition Cstability := forall A B C D, ~ ~ Cong A B C D -> Cong A B C D.

Definition Estability := forall (A B : Tpoint),
  ~ ~ A = B -> A = B.

Lemma cong_stability__point_equality_stability :
  Cstability -> Estability.
Proof.
intros CS A B HAB; apply cong_identity with A.
apply CS; intro HF; apply HAB; intro HEq; subst.
apply HF, cong_pseudo_reflexivity.
Qed.

(* We could use I <> (tnth basis (inord 0)) but,
for convenience, let us prove that O <> I. *)

Lemma two_points : O <> I.
Proof.
pose I1aux := (tnth basis (inord 0)); pose I1 := I1aux n Tpoint H ITnD.
intro HE; destruct lower_dim as [HF [HB [HBC1 _]]].
assert (HC : Cong O I O I1)
  by (rewrite big_ltn in HBC1; [destruct HBC1 as [HC _]|]; auto).
apply HF; rewrite HE in HC; apply cong_identity with I, g2_2, HC.
Qed.

Lemma point_equality_stability__cong_stability :
  Estability -> Cstability.
Proof.
intros ES A B C D HC.
destruct (segment_construction O I A B two_points) as [E [HB1 HC1]].
destruct (segment_construction O I C D two_points) as [F [HB2 HC2]].
assert (HEF : E = F).
  {
  apply ES; intro HEF; apply HC; clear HC; intro HC; apply HEF.
  apply g2_8 with O I; auto; [|apply two_points].
  apply cong_inner_transitivity with A B; [auto|].
  apply cong_inner_transitivity with C D; auto.
  }
subst; apply cong_inner_transitivity with I F; apply g2_2; auto.
Qed.

Lemma point_equality_stability__betS_stability :
  Estability -> Bstability.
Proof.
intros ES A B C HB1.
assert (HAB : A <> B) by (intro; subst; apply HB1; intros [HF _]; auto).
assert (HBC : B <> C) by (intro; subst; apply HB1; intros [_ [HF _]]; auto).
destruct (segment_construction A B B C HAB) as [D [HB HC]].
assert (HB2 : BetS A B D).
  {
  split; [auto| split; [|auto]].
  intro; subst; apply HBC, cong_identity with D, g2_2, HC.
  }
cut (C = D); [move->=> //|].
apply ES=> HCD; apply HB1; clear HB1; intros [_ [_ HB1]].
apply HCD, g2_8 with A B=> //; apply g2_2, HC.
Qed.

End Stability_properties.
