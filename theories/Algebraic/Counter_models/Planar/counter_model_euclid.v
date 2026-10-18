From mathcomp Require Import ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra algC.
From mathcomp
Require Import zmodp ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.counter_model_euclid.
Require Import GeoCoq.Algebraic.POF_to_Tarski.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Main.Meta_theory.Models.tarski_to_gupta_inspired.
Require Export GeoCoq.Main.Meta_theory.Parallel_postulates.parallel_postulates.
Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

Section rcfTarski2D.

Variable R : rcfType.
Notation "#" := proj1_sig.

Definition Point := counter_model_euclid.Point' R 2.

Definition bet' := @counter_model_euclid.bet' R 2.

Definition cong' := @counter_model_euclid.cong' R 2.

Lemma point_equality_decidability : point_equality_decidabilityP Point.
Proof. by move => a b; case: (a =P b); tauto. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof. by apply counter_model_euclid.bet_inner_transitivity. Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point cong'.
Proof. by apply counter_model_euclid.cong_pseudo_reflexivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. by apply counter_model_euclid.cong_identity. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point cong'.
Proof. by apply counter_model_euclid.cong_inner_transitivity. Qed.

Lemma inner_paschP : inner_paschP Point bet'.
Proof. by move => a b c p q; apply counter_model_euclid.pasch. Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof. by apply counter_model_euclid.bet_symmetry. Qed.

Lemma five_segment : five_segmentP Point bet' cong'.
Proof. by apply counter_model_euclid.five_segment. Qed.

Lemma segment_construction : segment_constructionP Point bet' cong'.
Proof.
by move => a b c d; apply counter_model_euclid.segment_construction_holds.
Qed.

Definition a : Point := counter_model_euclid.a R.
Definition b : Point := counter_model_euclid.b R.
Definition c : Point := counter_model_euclid.c R.

Lemma lower_dim : lower_dimP Point bet' a b c.
Proof. exact: abc_ncol. Qed.

Lemma det2_eq0 (u0 u1 v0 v1 e0 e1 : R) :
  u0 * e0 + u1 * e1 = 0 -> v0 * e0 + v1 * e1 = 0 -> (e0 != 0) || (e1 != 0) ->
  u0 * v1 == u1 * v0.
Proof.
move=> Hu Hv e_neq0; rewrite -subr_eq0.
have E0 : e0 * (u0 * v1 - u1 * v0) =
          v1 * (u0 * e0 + u1 * e1) - u1 * (v0 * e0 + v1 * e1) by ring.
have E1 : e1 * (u0 * v1 - u1 * v0) =
          u0 * (v0 * e0 + v1 * e1) - v0 * (u0 * e0 + u1 * e1) by ring.
rewrite Hu Hv !mulr0 subrr in E0 E1.
by case/orP: e_neq0 => e_neq0; [move/eqP: E0|move/eqP: E1];
   rewrite mulf_eq0 (negPf e_neq0).
Qed.

Lemma cong'_line (x p q : Point)
  (sp := Num.sqrt (omd p p)) (sq := Num.sqrt (omd q q)) :
  cong' x p x q -> dotp (#x) (sq *: #p - sp *: #q) = sq - sp.
Proof.
rewrite /cong' /counter_model_euclid.cong' /cong_v -!/(omd _ _).
rewrite eqr_div ?mulf_neq0 ?omd_neq0 // => E.
have : (sq * omd x p) ^+ 2 = (sp * omd x q) ^+ 2.
  rewrite !exprMn !sqr_sqrtr ?omd_ge0 //; apply: (mulIf (omd_neq0 x x)).
  transitivity (omd x p ^+ 2 * (omd x x * omd q q)); first by ring.
  by rewrite (eqP E); ring.
move/eqP; rewrite eqrXn2 ?mulr_ge0 ?sqrtr_ge0 ?omd_ge0 // => /eqP E'.
rewrite dotpDr dotpNr !dotpZr !dot_omd.
transitivity (sq - sp - (sq * omd x p - sp * omd x q)); first by ring.
by rewrite E' subrr subr0.
Qed.

Lemma upper_dim : upper_dimP Point bet' cong'.
Proof.
move=> a b c p q pq_neq _ _ _ Ha Hb Hc; apply: col_2D.
set sp := Num.sqrt (omd p p); set sq := Num.sqrt (omd q q).
set e := sq *: #p - sp *: #q.
have Ea : dotp (#a) e = sq - sp := cong'_line Ha.
have Eb : dotp (#b) e = sq - sp := cong'_line Hb.
have Ec : dotp (#c) e = sq - sp := cong'_line Hc.
have e_neq0 : e != 0.
  apply/eqP => e0; apply: pq_neq; apply: val_inj.
  have sqp : sq = sp.
    move: Ea; rewrite e0 /dotp trmx0 mulmx0 mxE => /eqP.
    by rewrite eq_sym subr_eq0 => /eqP.
  move: e0; rewrite /e sqp -scalerBr => /eqP; rewrite scaler_eq0 subr_eq0.
  by case/orP => [|/eqP //]; rewrite sqrtr_eq0 leNgt omd_gt0.
move: Ea Eb Ec e_neq0; rewrite /dotp !dot2 vector2_neq0 => Ea Eb Ec.
apply: det2_eq0.
- by rewrite !mulrBl addrACA -opprD Ea Eb subrr.
- by rewrite !mulrBl addrACA -opprD Eb Ec subrr.
Qed.

Global Instance Rcf_to_GI_PED' :
  Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality.
Proof.
exact
(Build_Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality
  Point bet' cong' point_equality_decidability
  cong_pseudo_reflexivity cong_inner_transitivity
  cong_identity
  segment_construction five_segment
  bet_symmetry bet_inner_transitivity
  (@counter_model_euclid.pasch R 0)
  a b c
  lower_dim).
Defined.

Lemma euclid : ~ euclidP Point bet'.
Proof.
move=> HP; apply (@counter_model_euclid.euclid_fails R 0).
cut (tarski_s_parallel_postulate).
- rewrite /tarski_s_parallel_postulate; move=> HT A B C D T H1 H2 HBD HDC HNCol.
  apply HT with D; auto; intro; subst; apply HNCol; right; right.
  apply bet_symmetry, H2.
cut (proclus_postulate); [|rewrite /proclus_postulate].
- apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
  simpl; try tauto.
intros A B C D P Q HPar HC HNC HCop; apply HP with A B;
[clear HC HNC HCop|intuition..].
destruct HPar as [[HCop HNI]|HParC]; [left|right; intuition].
split; [intro; treat_equalities; apply HNI; exists C; Col|].
split; [intro; treat_equalities; apply HNI; exists A; Col|].
split; [intuition|intros [X [? ?]]; apply HNI; exists X; Col].
Qed.

End rcfTarski2D.