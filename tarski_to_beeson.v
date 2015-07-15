Require Export Ch08_orthogonality.

(** In this file we formalize the connection between Beeson's axiom system
    and Tarski's axiom system. 
    We also have a proof that stability of equality follows from stability of Cong.
   
*)

Section Tarski_to_intuitionistic_Tarski.

Context `{M:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma cong_stability : forall A B C D, ~ ~ Cong A B C D -> Cong A B C D.
Proof.
intros.
elim (Cong_dec A B C D); intro HCong.

  apply HCong.

  contradiction.
Qed.

Definition BetH A B C : Prop := Bet A B C /\ A <> B /\ B <> C.

Lemma bet_stability : forall A B C, ~ ~ BetH A B C -> BetH A B C.
Proof.
intros A B C HNNBet.
unfold BetH in *.
elim (Bet_dec A B C); intro HBet; elim (eq_dec_points A B); intro HAB; elim (eq_dec_points B C); intro HBC.

  subst.
  exfalso.
  apply HNNBet.
  intro.
  spliter.
  intuition.

  subst.
  exfalso.
  apply HNNBet.
  intro.
  spliter.
  intuition.

  subst.
  exfalso.
  apply HNNBet.
  intro.
  spliter.
  intuition.

  repeat split; assumption.

  exfalso.
  apply HNNBet.
  intro.
  spliter.
  contradiction.

  exfalso.
  apply HNNBet.
  intro.
  spliter.
  contradiction.

  exfalso.
  apply HNNBet.
  intro.
  spliter.
  contradiction.

  exfalso.
  apply HNNBet.
  intro.
  spliter.
  contradiction.
Qed.

Definition T A B C : Prop := ~ (A<>B /\ B<>C /\ ~ BetH A B C).

Definition ColB A B C := ~ (~ T C A B /\ ~ T A C B /\ ~ T A B C).

Lemma between_identity_B : forall A B, ~ BetH A B A.
Proof.
intros A B HNBet.
unfold BetH in *.
destruct HNBet as [HBet [HAB HBA]].
apply between_identity in HBet.
subst.
intuition.
Qed.

Lemma Bet_T : forall A B C, Bet A B C -> T A B C.
Proof.
intros A B C HBet.
unfold T.
intro HT.
destruct HT as [HAB [HBC HNBet]].
apply HNBet.
unfold BetH.
intuition.
Qed.

Lemma BetH_Bet : forall A B C, BetH A B C -> Bet A B C.
Proof.
unfold BetH.
intuition.
Qed.

Lemma T_Bet : forall A B C, T A B C -> Bet A B C.
Proof.
intros A B C HT.
unfold T in HT.
elim (Bet_dec A B C); intro HBet.

  assumption.

  exfalso.
  apply HT.
  split.

    intro; subst; apply HBet; apply between_trivial2.

    split.

      intro; subst; apply HBet; apply between_trivial.

      intro HBetH; apply HBet; apply BetH_Bet in HBetH; assumption.
Qed.

Lemma NT_NBet : forall A B C, ~ T A B C -> ~ Bet A B C.
Proof.
intros A B C HNT.
intro HNBet.
apply HNT.
apply Bet_T.
assumption.
Qed.

Lemma T_dec : forall A B C, T A B C \/ ~ T A B C.
Proof.
intros A B C.
elim (Bet_dec A B C); intro HBet.

  left; apply Bet_T; assumption.

  right; intro HT; apply HBet; apply T_Bet in HT; assumption.
Qed.

Lemma between_inner_transitivity_B : forall A B C D : Tpoint, BetH A B D -> BetH B C D -> BetH A B C.
Proof.
intros A B C D HBet1 HBet2.
unfold BetH.
repeat split.

  apply BetH_Bet in HBet1.
  apply BetH_Bet in HBet2.
  apply between_inner_transitivity with D; assumption.

  unfold BetH in HBet1.
  spliter; assumption.

  unfold BetH in HBet2.
  spliter; assumption.
Qed.

Lemma ColB_Col : forall A B C, ColB A B C -> Col A B C.
Proof.
intros A B C HCol.
unfold ColB in HCol.
unfold Col.
elim (T_dec A B C); intro HT1;
elim (T_dec A C B); intro HT2;
elim (T_dec C A B); intro HT3.

  apply T_Bet in HT1; intuition.

  apply T_Bet in HT1; intuition.

  apply T_Bet in HT1; intuition.

  apply T_Bet in HT1; intuition.

  apply T_Bet in HT2; intuition.

  apply T_Bet in HT2; intuition.

  apply T_Bet in HT3; intuition.

  exfalso; apply HCol; intuition.
Qed.

Lemma Diff_Col_ColB : forall A B C, Col A B C -> ColB A B C.
Proof.
intros A B C H.
unfold Col in H.
unfold ColB.
intro HColB.
destruct HColB as [HNT1 [HNT2 HNT3]].
apply NT_NBet in HNT1.
apply NT_NBet in HNT2.
apply NT_NBet in HNT3.
elim H.

  intro HBet; contradiction.

  intro HColAux; elim HColAux; intro HBet; clear HColAux.

    apply between_symmetry in HBet.
    contradiction.

    contradiction.
Qed.

Lemma NColB_NDiffCol : forall A B C, ~ ColB A B C -> ~ Col A B C.
Proof.
intros A B C HNCB.
intro HNC.
apply HNCB.
apply Diff_Col_ColB.
assumption.
Qed.

Lemma NColB_NColOrEq : forall A B C, ~ ColB A B C -> ~ Col A B C.
Proof.
intros A B C HNCB.
apply NColB_NDiffCol in HNCB.
assumption.
Qed.

Lemma inner_pasch_B : forall A B C P Q,
  BetH A P C -> BetH B Q C -> ~ ColB A B C ->
  exists x, BetH P x B /\ BetH Q x A.
Proof.
intros A B C P Q HBetH1 HBetH2 HNC.
unfold BetH in HBetH1.
destruct HBetH1 as [HBet1 [HAP HPC]].
unfold BetH in HBetH2.
destruct HBetH2 as [HBet2 [HBQ HQC]].
apply NColB_NColOrEq in HNC.
assert (HIP := inner_pasch A B C P Q HBet1 HBet2).
destruct HIP as [x [HBet3 HBet4]].
exists x.
split.

  split; try assumption.
  split.

    intro.
    subst.
    apply HNC.
    assert_cols.
    ColR.

    intro.
    subst.
    apply HNC.
    assert_cols.
    ColR.

  split; try assumption.
  split.

    intro.
    subst.
    apply HNC.
    assert_cols.
    ColR.

    intro.
    subst.
    apply HNC.
    assert_cols.
    ColR.
Qed.

Lemma between_symmetry_B : forall A B C, BetH A B C -> BetH C B A.
Proof.
unfold BetH.
intros A B C HBet.
repeat split; intuition.
Qed.

Lemma five_segments_B : forall A A' B B' C C' D D' : Tpoint,
    Cong A B A' B' ->
    Cong B C B' C' ->
    Cong A D A' D' ->
    Cong B D B' D' ->
    ~ (A <> B /\ B <> C /\ ~ BetH A B C) ->
    ~ (A' <> B' /\ B' <> C' /\ ~ BetH A' B' C') ->
    A <> B -> Cong C D C' D'.
Proof.
intros.
assert (HBet1 : T A B C) by (unfold T; assumption).
assert (HBet2 : T A' B' C') by (unfold T; assumption).
apply T_Bet in H3.
apply T_Bet in H4.
apply five_segments with A A' B B'; assumption.
Qed.

Lemma segment_construction_B : forall A B C D, A<>B -> exists E, T A B E /\ Cong B E C D.
Proof.
intros A B C D HDiff.
assert (T := segment_construction A B C D).
destruct T as [E [HBet HCong]].
apply Bet_T in HBet.
exists E; intuition.
Qed.

Lemma lower_dim_B : exists A, exists B, exists C, ~ T C A B /\ ~ T A C B /\ ~ T A B C.
Proof.
assert (HLD := lower_dim).
destruct HLD as [A [B [C HNBet]]].
exists A; exists B; exists C.
elim (T_dec C A B); intro HT1; elim (T_dec A C B); intro HT2; elim (T_dec A B C); intro HT3.

  exfalso; apply HNBet; left; apply T_Bet; assumption.

  exfalso; apply HNBet; right; right; apply T_Bet; assumption.

  exfalso; apply HNBet; left; apply T_Bet; assumption.

  exfalso; apply HNBet; right; right; apply T_Bet; assumption.

  exfalso; apply HNBet; left; apply T_Bet; assumption.

  exfalso; apply HNBet; right; left; apply between_symmetry; apply T_Bet; assumption.

  exfalso; apply HNBet; left; apply T_Bet; assumption.

  tauto.
Qed.

Instance Beeson_follows_from_Tarski : intuitionistic_Tarski_neutral_dimensionless.
Proof.
exact (Build_intuitionistic_Tarski_neutral_dimensionless 
 Tpoint BetH Cong
 cong_stability
 bet_stability
 between_identity_B
 cong_identity
 cong_pseudo_reflexivity
 cong_inner_transitivity
 inner_pasch_B
 between_symmetry_B
 between_inner_transitivity_B
 five_segments_B
 segment_construction_B
 lower_dim_B).
Qed.

End Tarski_to_intuitionistic_Tarski.

Section Proof_of_eq_stability_in_IT.

Context `{MIT:intuitionistic_Tarski_neutral_dimensionless}.

Lemma cong_stability_eq_stability : forall A B : ITpoint, ~ A <> B -> A = B.
Proof.
intros A B HAB.
apply Icong_identity with A.
apply Cong_stability.
intro HNCong.
apply HAB.
intro HEq.
subst.
apply HNCong.
apply Icong_pseudo_reflexivity.
Qed.

End Proof_of_eq_stability_in_IT.

Require Import Classical.

Section Intuitionistic_Tarski_to_Tarski.

Context `{MIT:intuitionistic_Tarski_neutral_dimensionless}.

Lemma Col_dec : forall A B C, ICol A B C \/ ~ ICol A B C.
Proof.
intros.
tauto.
Qed.

Lemma eq_dec : forall A B :ITpoint, A=B \/ A<>B.
Proof.
intros.
tauto.
Qed.

Definition BetT A B C := IBet A B C \/ A=B \/ B=C.

Lemma bet_id : forall A B : ITpoint, BetT A B A -> A = B.
Proof.
intros.
unfold BetT in H.
decompose [or] H.
apply Ibetween_identity in H0.
elim H0.
assumption.
intuition.
Qed.

Lemma IT_chara : forall A B C, 
 IT A B C <-> A=B \/ B=C \/ IBet A B C.
Proof.
intros.
unfold IT.
tauto. (* classical *)
Qed.

Lemma BetT_symmetry : forall A B C, BetT A B C -> BetT C B A.
Proof.
intros.
unfold BetT in *.
intuition.
left.
apply Ibetween_symmetry.
assumption.
Qed.

Lemma BetT_id : forall A B, BetT A B A -> A=B.
Proof.
intros.
unfold BetT in *.
intuition.
apply Ibetween_identity in H0.
elim H0.
Qed.

(* Lemma 4.1 page 22 *)

Lemma pasch_col_case : forall A B C P Q : ITpoint,
        BetT A P C ->
        BetT B Q C -> ICol A B C -> exists x : ITpoint, BetT P x B /\ BetT Q x A.
Proof.
intros.
elim (eq_dec A B);intro.
 subst.
 exists B.
 unfold BetT;auto.
elim (eq_dec A C);intro.
 subst.
 apply BetT_id in H.
 subst.
 exists P.
 unfold BetT;auto.
elim (eq_dec B C);intro.
 subst.
 apply BetT_id in H0.
 subst.
 exists Q.
 unfold BetT;auto.
elim (eq_dec B Q);intro.
 subst.
 exists Q.
 unfold BetT;auto.
elim (eq_dec C Q);intro.
 subst.
 exists P.
 split.
 unfold BetT;auto.
 apply BetT_symmetry.
 auto.
elim (eq_dec A P);intro.
 subst.
 exists P.
 unfold BetT;auto.
elim (eq_dec C P);intro.
 subst.
 exists Q.
 split.
 apply BetT_symmetry.
 auto.
 unfold BetT;auto.

unfold ICol in H1.
spliter.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
unfold IT in *.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.
exists A.
split.
apply Ibetween_symmetry in H1.
induction H.
assert (T:=Ibetween_inner_transitivity B A P C H1 H).
unfold BetT.
left.
apply Ibetween_symmetry;auto.
induction H;subst.
unfold BetT;auto.
left.
apply Ibetween_symmetry;auto.
unfold BetT;auto.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
unfold IT in H1.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.

exists C.

unfold BetT in H.
induction H;induction H0.
split.
apply BetT_symmetry.
left.

apply Ibetween_inner_transitivity with A.
apply Ibetween_symmetry;auto.
apply Ibetween_symmetry;auto.
apply BetT_symmetry.
left.
apply Ibetween_inner_transitivity with B.
assumption.
apply Ibetween_symmetry;auto.
induction H0;subst;intuition.
induction H;subst;intuition.
induction H;subst;intuition.

apply NNPP in H1.
induction H;induction H0.

exists B.
split.
unfold BetT;auto.

left.
apply Ibetween_symmetry.
apply Ibetween_inner_transitivity with C.
unfold IT in H1.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.
assumption.
assumption.

induction H0;subst;intuition.
induction H;subst;intuition.
induction H;subst;intuition.
Qed.

Lemma pasch : forall A B C P Q : ITpoint,
        BetT A P C ->
        BetT B Q C -> exists x : ITpoint, BetT P x B /\ BetT Q x A.
Proof.
intros.
induction (Col_dec A B C).
eapply pasch_col_case;eauto.

unfold BetT in *.
decompose [or] H;clear H.
decompose [or] H0;clear H0.

elim (Iinner_pasch A B C P Q H2 H H1).
intros.
spliter.
exists x.
split.
tauto.
tauto.

subst.
exists Q;auto.
subst.
exists P.
split.
auto.
left.
apply Ibetween_symmetry.
auto.
subst.
exists P;auto.
subst.
decompose [or] H0;clear H0.
exists Q.
split.
left.
apply Ibetween_symmetry.
auto.
auto.
subst.
exists Q;auto.
subst.
exists C;auto.
Qed.

Lemma five_segments:
 forall A A' B B' C C' D D' : ITpoint,
        ICong A B A' B' ->
        ICong B C B' C' ->
        ICong A D A' D' ->
        ICong B D B' D' ->
        BetT A B C -> BetT A' B' C' -> A <> B -> ICong C D C' D'.
Proof.
intros.
apply Ifive_segments with A A' B B' ;try assumption.
unfold IT.
intro.
spliter.
unfold BetT in *.
intuition.
unfold BetT in *.
unfold IT.
intro.
intuition.
Qed.

Lemma IT_trivial : forall A B, IT A A B.
Proof.
intros.
unfold IT.
intro.
spliter.
intuition.
Qed.

Lemma another_point : forall A, exists B:ITpoint, A<>B.
Proof.
intros.
assert (T:=Ilower_dim).
decompose [ex] T.
elim (eq_dec A x);intro.
subst.
elim (eq_dec x x0);intro.
subst.
exfalso.
apply H.
apply IT_trivial.
exists x0.
assumption.
exists x.
assumption.
Qed.

Lemma segment_construction :
 forall A B C D : ITpoint,
        exists E : ITpoint, BetT A B E /\ ICong B E C D.
Proof.
intros.
induction (eq_dec A B).
subst.
elim (another_point B);intros.
elim (Isegment_construction x B C D);intros.
exists x0.
split.
unfold BetT.
intuition.
intuition.
intuition.
elim (Isegment_construction A B C D H).
intros.
exists x.
spliter.
split;try assumption.
unfold IT in *.
unfold BetT.
tauto.
Qed.

Lemma lower_dim :
 exists A B C : ITpoint, ~ (BetT A B C \/ BetT B C A \/ BetT C A B).
Proof.
assert (T:=Ilower_dim).
decompose [ex] T;clear T.
exists x.
exists x0.
exists x1.

unfold BetT in *.
unfold ICol in  *.
unfold IT in *.
firstorder using Ibetween_symmetry.
Qed.
 
Instance IT_to_T : Tarski_neutral_dimensionless.
exact 
(Build_Tarski_neutral_dimensionless ITpoint BetT ICong
  bet_id Icong_pseudo_reflexivity Icong_identity Icong_inner_transitivity
  pasch five_segments segment_construction lower_dim).
Qed.

End Intuitionistic_Tarski_to_Tarski.