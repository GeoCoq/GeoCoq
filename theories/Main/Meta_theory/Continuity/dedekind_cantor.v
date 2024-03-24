Require Export GeoCoq.Axioms.continuity_axioms.
Require Export GeoCoq.Main.Tarski_dev.Ch07_midpoint.
Require Import Arith.

Section Dedekind_cantor.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma nested__diff0 : forall A B,
  Nested A B -> forall n An Bn, A n An -> B n Bn -> An <> Bn.
Proof.
  intros A B [Hex HAB].
  destruct n.
    intros A0 B0 HA0 HB0.
    destruct (Hex 1) as [A1 [B1 []]].
    destruct (HAB O A0 A1 B1 B0) as [HBet1 [HBet2 Hdiff]]; trivial.
    assert (Bet A0 A1 B0) by eBetween.
    assert_diffs; auto.
  intros Am Bm HAm HBm.
  destruct (Hex n) as [An [Bn []]].
  destruct (HAB n An Am Bm Bn) as [HBet1 [HBet2 Hdiff]]; trivial.
Qed.

Lemma nested_sym : forall A B, Nested A B -> Nested B A.
Proof.
  intros A B [Hex HAB].
  split; intro n.
    destruct (Hex n) as [An [Bn []]]; exists Bn, An; split; assumption.
  intros Bn Bm Am An HBn HBm HAm HAn.
  destruct (HAB n An Am Bm Bn HAn HAm HBm HBn) as [HBet1 [HBet2 Hd]].
  repeat split; Between.
Qed.

Lemma nested__ex_left : forall A B n, Nested A B -> exists An, A n An.
Proof.
  intros A B n [Hex _].
  destruct (Hex n) as [An [_ [HAn _]]].
  exists An.
  apply HAn.
Qed.

Lemma nested__ex_right : forall A B n, Nested A B -> exists Bn, B n Bn.
Proof.
  intros A B n HAB; apply nested__ex_left with A; apply nested_sym, HAB.
Qed.

Lemma nested_aux1 : forall A B n m An Am Bm,
   Nested A B -> n < m -> A n An -> A m Am -> B m Bm -> Bet An Am Bm.
Proof.
  intros A B n m An Am Bm [Hex HAB] Hcomp.
  destruct (Hex n) as [_ [Bn [_ HBn]]].
  revert Am Bm.
  induction Hcomp.
    intros Am Bm HAn HAm HBm.
    destruct (HAB n An Am Bm Bn); auto.
  intros Am' Bm' HAn HAm' HBm'.
  destruct (Hex m) as [Am [Bm []]].
  assert (HBet : Bet An Am Bm) by (apply IHHcomp; trivial).
  destruct (HAB m Am Am' Bm' Bm) as [HBet1 [HBet2 Hd]]; trivial.
  assert (Bet An Am Bm') by eBetween.
  clear HBet HBet2; eBetween.
Qed.

Lemma nested_aux2 : forall A B n m An Am Bn,
  Nested A B -> n < m -> A n An -> A m Am -> B n Bn -> Bet An Am Bn.
Proof.
  intros A B n m An Am Bn HAB Hcomp HAn HAm HBn.
  destruct (nested__ex_right A B m HAB) as [Bm].
  apply outer_transitivity_between with Bm.
    apply (nested_aux1 A B n m); assumption.
    apply between_symmetry, (nested_aux1 B A n m); auto using nested_sym.
    eapply nested__diff0; eassumption.
Qed.

Lemma nested__bet : forall A B n n1 m An An1 Bm,
  Nested A B -> n < n1 -> A n An -> A n1 An1 -> B m Bm -> Bet An An1 Bm.
Proof.
  intros A B n n1 m An An1 Bm HAB Hlt HAn HAn1 HBm.
  assert (HBA := nested_sym A B HAB).
  destruct (Nat.eq_dec n1 m).
    subst n1; apply (nested_aux1 A B n m); assumption.
  destruct (nested__ex_right A B n1 HAB) as [Bn1].
  assert (Bet An An1 Bn1) by (apply (nested_aux1 A B n n1); assumption).
  destruct (Nat.lt_gt_cases n1 m) as [[Hlt1|Hlt1] _]; auto.
  - apply between_inner_transitivity with Bn1; trivial.
    apply between_symmetry, (nested_aux2 B A n1 m); assumption.
  - apply outer_transitivity_between with Bn1; trivial.
      apply between_symmetry, (nested_aux1 B A m n1); assumption.
      apply (nested__diff0 A B HAB n1); assumption.
Qed.

Lemma nested__diff : forall A B n m An Bm, Nested A B -> A n An -> B m Bm -> An <> Bm.
Proof.
  intros A B n m An Bm HAB HAn HBm.
  destruct (Nat.lt_trichotomy n m) as [Hlt|[Heq|Hlt]].
  - destruct (nested__ex_left A B m HAB) as [Am].
    apply bet_neq23__neq with Am.
      apply (nested__bet A B n m m); eassumption.
      eapply nested__diff0; eassumption.
  - subst; eapply nested__diff0; eassumption.
  - destruct (nested__ex_right A B n HAB) as [Bn].
    apply nested_sym in HAB.
    apply not_eq_sym, bet_neq23__neq with Bn.
      apply (nested__bet B A m n n); assumption.
      eapply nested__diff0; eassumption.
Qed.

Lemma dedekind__cantor : dedekind_s_axiom -> cantor_s_axiom.
Proof.
  intros dedekind A B HAB.
  assert (HX : exists X, forall An Bm, (exists n, 0 < n /\ A n An) -> (exists m, B m Bm) -> Bet An X Bm).
  - apply dedekind.
    destruct (nested__ex_left A B 0 HAB) as [A0].
    exists A0.
    intros An Bm [n [Hn HAn]] [m HBm].
    apply (nested__bet A B 0 n m); assumption.
  - destruct HX as [X HX].
    exists X.
    intros n An Bn HAn HBn.
    destruct (Nat.eq_0_gt_0_cases n); [|apply HX; exists n; auto].
    subst.
    destruct (nested__ex_left A B 1 HAB) as [A1].
    apply between_exchange2 with A1.
      apply (nested_aux2 A B 0 1); auto.
      apply HX; [exists 1; split| exists 0]; auto.
Qed.

End Dedekind_cantor.
