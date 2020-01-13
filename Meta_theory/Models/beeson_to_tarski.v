Require Import GeoCoq.Axioms.beeson_s_axioms.
Require Import GeoCoq.Axioms.tarski_axioms.

Section Proof_of_eq_stability_in_IT.

Context `{BTn:intuitionistic_Tarski_neutral_dimensionless}.

Lemma cong_stability_eq_stability : forall A B : ITpoint, ~ A <> B -> A = B.
Proof.
intros A B HAB; apply Icong_identity with A, Cong_stability.
intro HNC; apply HAB; intro; subst; apply HNC, Icong_pseudo_reflexivity.
Qed.

End Proof_of_eq_stability_in_IT.

Section Intuitionistic_Tarski_to_Tarski.

Context `{BTn:intuitionistic_Tarski_neutral_dimensionless}.

Variable ED : forall A B : ITpoint, A = B \/ A <> B.

Lemma IT_dec : forall A B C, IT A B C \/ ~ IT A B C.
Proof.
intros A B C; elim (ED A B); intro HAB; elim (ED B C); intro HBC;
[left..|]; [intros [HF _]; auto..|intros [_ [HF _]]; auto|].
destruct (Isegment_construction A B B C HAB) as [D [HB HC]].
elim (ED C D); intro HCD; [left; subst; auto|].
right; intro HF; apply HB; clear HB; split; [auto|split; intro HB1].

  {
  apply HCD, Icong_identity with B; subst.
  apply Icong_inner_transitivity with D C; [apply Icong_pseudo_reflexivity|].
  apply Icong_inner_transitivity with D D; [auto|].
  apply Icong_pseudo_reflexivity.
  }

  {
  apply HF; split; [auto|split; [auto|intro HB2]].
  cut (ICong C C C D); [intro; apply HCD; apply Icong_identity with C;
                        apply Icong_inner_transitivity with C C;
                        [auto|apply Icong_pseudo_reflexivity]|].
  assert (H : forall A B, ICong A B A B).
    {
    intros E F; apply Icong_inner_transitivity with F E;
    apply Icong_pseudo_reflexivity.
    }
  apply Ifive_segment with A A B B; auto;
  [|apply Icong_inner_transitivity with B D; auto].
  apply Icong_inner_transitivity with D A; [|apply Icong_pseudo_reflexivity].
  apply Icong_inner_transitivity with C A; [|apply Icong_pseudo_reflexivity].
  apply Ifive_segment with A A B B; auto; [|intros [_ [_ HNB]]; auto].
  apply Icong_inner_transitivity with B D; auto.
  }
Qed.

Lemma ICol_dec : forall A B C, ICol A B C \/ ~ ICol A B C.
Proof.
intros A B C; elim (IT_dec A B C); intro HB1;
elim (IT_dec A C B); intro HB2; elim (IT_dec C A B); intro HB3;
[left..|]; [intros [HNB1 [HNB2 HNB3]]; auto..|].
right; intro HC; apply HC; split; [auto|split; auto].
Qed.

Definition BetT A B C := IBet A B C \/ A = B \/ B = C.

Lemma bet_id : forall A B : ITpoint, BetT A B A -> A = B.
Proof.
intros A B [|[|]]; auto; exfalso; apply (Ibetween_identity A B); auto.
Qed.

Lemma IT_chara : forall A B C, IT A B C <-> A = B \/ B = C \/ IBet A B C.
Proof.
intros A B C; split; [|intros [H|[H|H]]; intros [HAB [HBC HB]]; auto].
intro HB; elim (ED A B); [auto|intro HAB]; elim (ED B C); [auto|intro HBC].
right; right; apply Bet_stability; intro HNB; apply HB; auto.
Qed.

Lemma BetT_dec : forall A B C, BetT A B C \/ ~ BetT A B C.
Proof.
intros A B C; elim (IT_dec A B C); intro HB; [left|right].

  {
  unfold BetT; apply IT_chara in HB; tauto.
  }

  {
  intros [|[|]]; apply HB, IT_chara; auto.
  }
Qed.

Lemma ICol_chara : forall A B C,
  ICol A B C <-> IT A B C \/ IT B C A \/ IT C A B.
Proof.
intros A B C; split.

  {
  intro HC; elim (IT_dec A B C); intro HB1; [auto|].
  elim (IT_dec B C A); intro HB2; [auto|].
  elim (IT_dec C A B); intro HB3; [auto|].
  exfalso; apply HC; split; [auto|split; [|auto]].
  intro HNB; apply HB2; intros [HNE1 [HN2 HB]].
  apply HNB; split; [auto|split; [auto|]].
  intro; apply HB, Ibetween_symmetry; auto.
  }

  {
  intros [|[|]]; intros [HB1 [HB2 HB3]]; auto.
  apply HB2. intros [HE1 [HE2 HNB]]; apply H; split; [auto|split; [auto|]].
  intro; apply HNB, Ibetween_symmetry; auto.
  }
Qed.

Lemma BetT_symmetry : forall A B C, BetT A B C -> BetT C B A.
Proof. intros A B C [|[|]]; [left; apply Ibetween_symmetry|right..]; auto. Qed.

(* Lemma 5.1 page 28 *)

Lemma pasch_col_case : forall A B C P Q : ITpoint,
  BetT A P C -> BetT B Q C -> ICol A B C ->
  exists x, BetT P x B /\ BetT Q x A.
Proof.
intros A B C P Q HB1 HB2 HC.
elim (ED A B); intro HAB; [subst; exists B; unfold BetT; auto|].
elim (ED A C); intro HAC; [subst; apply bet_id in HB1; subst;
                           exists P; unfold BetT; auto|].
elim (ED B C); intro HBC; [subst; apply bet_id in HB2; subst;
                           exists Q; unfold BetT; auto|].
elim (ED A P); intro HAP; [subst; exists P; unfold BetT; auto|].
elim (ED P C); intro HPC; [subst; exists Q; split;
                           [apply BetT_symmetry|unfold BetT]; auto|].
elim (ED B Q); intro HBQ; [subst; exists Q; unfold BetT; auto|].
elim (ED Q C); intro HQC; [subst; exists P; split;
                           [unfold BetT|apply BetT_symmetry]; auto|].
destruct HB1 as [HB1|[|]]; [|tauto..].
destruct HB2 as [HB2|[|]]; [|tauto..].
elim (BetT_dec A C B).

  {
  intros [HB3|[|]]; [exists C|subst; tauto..].
  split; apply BetT_symmetry; left.

    {
    apply Ibetween_inner_transitivity with A; apply Ibetween_symmetry; auto.
    }

    {
    apply Ibetween_inner_transitivity with B; [|apply Ibetween_symmetry]; auto.
    }
  }
intro HNB1.
cut (forall A B P Q, A <> B -> B <> C ->
                     BetT A B C -> IBet A P C -> IBet B Q C ->
                     exists x : ITpoint, BetT P x B /\ BetT Q x A).

  {
  intro HE.
  elim (BetT_dec A B C); [intro; destruct (HE A B P Q) as [x []]; auto|].
  intro HNB2.
  elim (BetT_dec B A C); [intro; destruct (HE B A Q P) as [x []]; auto|];
  [exists x; auto|intro HNB3].
  exfalso; apply HC; split; [|split]; intro HIT;
  [apply HNB3|apply HNB1|apply HNB2]; left; apply Bet_stability; intro HNIT;
  apply HIT; split; auto; split; auto.
  intro; apply HNIT, Ibetween_symmetry; auto.
  }

  {
  clear dependent A; clear dependent B; clear dependent P; clear dependent Q.
  intros A B P Q HAB HBC HB1 HB2 HB3.
  destruct HB1 as [HB1|[|]]; [|subst; tauto..]; clear HAB HBC.
  exists B; split; [unfold BetT; auto|].
  apply BetT_symmetry; left; apply Ibetween_inner_transitivity with C; auto.
  }
Qed.

Lemma pasch : forall A B C P Q : ITpoint,
  BetT A P C -> BetT B Q C ->
  exists x, BetT P x B /\ BetT Q x A.
Proof.
intros A B C P Q HB1 HB2.
elim (ICol_dec A B C); [apply pasch_col_case; auto|intro HNC].
destruct HB1 as [HB1|[|]]; subst; [|exists P; unfold BetT; auto|];
[|exists Q; split; [apply BetT_symmetry|unfold BetT]; auto].
destruct HB2 as [HB2|[|]]; subst; [|exists Q; unfold BetT; auto|];
[|exists P; split; [unfold BetT|apply BetT_symmetry; left]; auto].
destruct (Iinner_pasch A B C P Q) as [x [HB3 HB4]];
[..|exists x; split; left]; auto.
Qed.

Lemma five_segment: forall A A' B B' C C' D D',
  ICong A B A' B' -> ICong B C B' C' -> ICong A D A' D' -> ICong B D B' D' ->
  BetT A B C -> BetT A' B' C' -> A <> B ->
  ICong C D C' D'.
Proof.
intros; apply Ifive_segment with A A' B B'; auto;
intros [HNE1 [HNE2 HB]]; unfold BetT in *; intuition.
Qed.

Lemma another_point : forall A, exists B : ITpoint, A <> B.
Proof.
intro A; assert (T := Ilower_dim).
elim (ED A beeson_s_axioms.PA); intro HPA; [|exists beeson_s_axioms.PA; auto].
elim (ED A beeson_s_axioms.PB); intro HPB; [|exists beeson_s_axioms.PB; auto].
exfalso; destruct T as [_ [_ T]]; apply T; subst; intros [HF _]; auto.
Qed.

Lemma segment_construction : forall A B C D : ITpoint,
  exists E : ITpoint, BetT A B E /\ ICong B E C D.
Proof.
intros A B C D; elim (ED A B); intro HAB.

  {
  subst; destruct (another_point B) as [A HAB].
  destruct (Isegment_construction A B C D) as [E [HB HC]]; [auto|].
  exists E; split; auto; apply IT_chara in HB; unfold BetT; tauto.
  }

  {
  destruct (Isegment_construction A B C D HAB) as [E [HB HC]].
  exists E; split; auto; apply IT_chara in HB; unfold BetT; tauto.
  }
Qed.

Lemma lower_dim :
  ~ (BetT beeson_s_axioms.PA beeson_s_axioms.PB beeson_s_axioms.PC \/
     BetT beeson_s_axioms.PB beeson_s_axioms.PC beeson_s_axioms.PA \/
     BetT beeson_s_axioms.PC beeson_s_axioms.PA beeson_s_axioms.PB).
Proof.
assert (T:=Ilower_dim); unfold BetT, ICol, IT in *.
firstorder using Ibetween_symmetry.
Qed.

Instance IT_to_T : Tarski_neutral_dimensionless.
exact (Build_Tarski_neutral_dimensionless
         ITpoint BetT ICong
         Icong_pseudo_reflexivity Icong_inner_transitivity Icong_identity
         segment_construction five_segment bet_id pasch
         beeson_s_axioms.PA beeson_s_axioms.PB beeson_s_axioms.PC lower_dim).
Defined.

Instance IT_to_T_PED :
  Tarski_neutral_dimensionless_with_decidable_point_equality IT_to_T.
Proof. split; apply ED. Defined.

End Intuitionistic_Tarski_to_Tarski.