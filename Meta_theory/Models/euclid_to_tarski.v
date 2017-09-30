Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Elements.OriginalProofs.proposition_01.
Require Import GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Import Classical. 

Section Euclid_to_Tarski.

Context `{Ax:euclidean_neutral_ruler_compass}.

Definition Bet A B C := BetS A B C \/ A=B \/ B=C.

Lemma Bet_sym : forall A B C,
  Bet A B C -> Bet C B A.
Proof.
intros.
unfold Bet in *.
decompose [or] H.
left.
eauto using axiom_betweennesssymmetry.
right;right;auto.
right;left;auto.
Qed.

Instance Tarski_follows_Euclid: Tarski_neutral_dimensionless.
Proof.
eapply (Build_Tarski_neutral_dimensionless Point Bet Cong) with (PA:=PA) (PB:=PB) (PC:=PC).
- apply cn_equalityreverse.
- intros;apply cn_congruencetransitive with A B;auto.
- apply axiom_nullsegment1.
- intros.
  elim (classic (A=B));intro.
  subst.
  elim (classic (B=C));intro.
  subst.
  exists D.
  split.
  unfold Bet;right;auto.
  apply cn_congruencereflexive.
  destruct (postulate_extension2 C B C D) as [X [HXA HXB]].
  unfold neq;auto.
  exists X.
  unfold Bet;auto.
  destruct (postulate_extension2 A B C D H).
  spliter.
  unfold TE in *.
  exists x.
  unfold neq in *.
  unfold Bet.
  tauto.
- intros.
  elim (classic (B=C));intro.
  subst.
  assert (B'=C').
  apply axiom_nullsegment1 with C.
  apply lemma_congruencesymmetric;auto. 
  subst.
  assumption.
  assert (B'<>C').
  {
  intro;subst.
  apply H6.
  apply axiom_nullsegment1 with C'.
  assumption.
  }
  assert (A'<>B').
  {
  intro;subst.
  apply H5.
  apply axiom_nullsegment1 with B'.
  assumption.
  }
 assert (Cong D C D' C').
 apply (axiom_5_line A B C D A' B' C' D' H0 H1 H2);try assumption.
 unfold Bet in *.
 intuition.
 unfold Bet in *.
 intuition.
 apply (lemma_congruenceflip) in H9;spliter;auto.
- intros.
  unfold Bet in *.
  destruct H.
  exfalso.
  apply (axiom_betweennessidentity A B);auto.
  intuition.
- intros A B C P Q H H0.
  destruct H.
  destruct H0.
  elim (classic (Col A B C));intro.
  unfold Col in *.
  decompose [or] H1;clear H1;
  unfold eq in *;subst.
  exists B;split;unfold Bet;auto.
  exfalso;apply lemma_betweennotequal in H.
  unfold neq in *;intuition.
  exfalso;apply lemma_betweennotequal in H0.
  unfold neq in *;intuition.
  exists A.
  split.
  unfold Bet;left. 
  eauto using lemma_3_6a, axiom_betweennesssymmetry.
  unfold Bet;auto.
  exists B.
  split.
  unfold Bet;auto.
  unfold Bet;left.
  eauto using lemma_3_6a, axiom_betweennesssymmetry.
  exists C.
  split.
  unfold Bet;left.
  eauto using lemma_3_6a, axiom_betweennesssymmetry.
  unfold Bet;left.
  eauto using lemma_3_6a, axiom_betweennesssymmetry.
  assert (T:exists X : Point, BetS A X Q /\ BetS B X P).
   apply  (postulate_Pasch_inner A B C P Q H H0).
   unfold nCol,neq.
   unfold Col in *.
  assert (BetS B A C <-> BetS C A B)
     by (split;intro;apply axiom_betweennesssymmetry;auto).
  assert (eq C B <-> eq B C) by (split;unfold eq;intro;auto).
  tauto.
  destruct T as [X [HXA HXB]].
  exists X.
  split;unfold Bet;left;auto using axiom_betweennesssymmetry.
  destruct H0.
  subst.
  exists Q;unfold Bet;auto.
  subst.
  exists P.
  unfold Bet;auto using axiom_betweennesssymmetry.
  destruct H.
  subst;exists P; unfold Bet;auto.
  subst;exists Q;split.
  auto using Bet_sym.
  unfold Bet;auto.
- 
assert (T:=axiom_lower_dim).
unfold nCol,Bet,neq in *.
intro;spliter.
decompose [or] H;try
 solve [auto using  axiom_betweennesssymmetry].
subst;intuition.
subst;intuition.
Qed.

End Euclid_to_Tarski.


