Require Import GeoCoq.Tactics.Coinc.tactics_axioms.
Require Import GeoCoq.Tarski_dev.Annexes.inscribed_angle.

Section Tarski_is_a_Coinc_theory_for_concyclic.

Context `{TE:Tarski_euclidean}.

Definition not_col : arity Tpoint 3 := fun A B C : Tpoint => ~ Col A B C.

Lemma not_col_perm_1 : forall A X, app_1_n not_col A X -> app_n_1 not_col X A.
Proof. unfold not_col; simpl; Col. Qed.

Lemma not_col_perm_2 : forall A B (X : cartesianPower Tpoint 1),
  app_2_n not_col A B X -> app_2_n not_col B A X.
Proof. unfold not_col, app_2_n; simpl; Col. Qed.

Definition concy : arity Tpoint 4 := Concyclic_gen.

Lemma concy_perm_1 : forall (A : Tpoint) (X : cartesianPower Tpoint 3),
app_1_n concy A X -> app_n_1 concy X A.
Proof. unfold concy; simpl. intros; apply concyclic_gen_perm_1; auto. Qed.

Lemma concy_perm_2 : forall (A B : Tpoint) (X : cartesianPower Tpoint 2),
app_2_n concy A B X -> app_2_n concy B A X.
Proof.
unfold app_2_n, concy; simpl; intros; apply concyclic_gen_perm_2; auto.
Qed.

Lemma concyclic_gen_1123 : forall A B C, Concyclic_gen A A B C.
Proof.
unfold Concyclic_gen; simpl; intros A B C.
elim (col_dec A B C); intro; [right; repeat split; Col|].
left.
split; Cop.
destruct (triangle_circumscription A B C H) as [O]; spliter.
exists O, A; unfold OnCircle; repeat split; Cong.
Qed.

Lemma concy_bd : forall (A : Tpoint) (X : cartesianPower Tpoint 2),
app_2_n concy A A X.
Proof. unfold app_2_n, concy; simpl; intros; apply concyclic_gen_1123. Qed.

Lemma concy_3 :
  forall (CONCY : cartesianPower Tpoint 4) (NOT_COL : cartesianPower Tpoint 3),
  pred_conj concy CONCY NOT_COL -> app not_col NOT_COL -> app concy CONCY.
Proof.
unfold pred_conj, app_2_n, concy; simpl.
intros CONCY NOT_COL HConcy HNot_Col.
destruct HConcy as [HConcy1 [HConcy2 [HConcy3 HConcy4]]].
apply concyclic_gen_pseudo_trans with (fst NOT_COL) (fst (snd NOT_COL)) (snd (snd NOT_COL)); try apply concyclic_gen_perm_1; auto.
Qed.

Global Instance Tarski_is_a_Arity_for_concy : Arity.
Proof. exact (Build_Arity Tpoint 1). Defined.

Global Instance Tarski_is_a_Coinc_predicates_for_concy :
  (Coinc_predicates Tarski_is_a_Arity_for_concy).
Proof.
exact (Build_Coinc_predicates Tarski_is_a_Arity_for_concy not_col concy).
Defined.

Global Instance Tarski_is_a_Coinc_theory_for_concy : (Coinc_theory Tarski_is_a_Arity_for_concy Tarski_is_a_Coinc_predicates_for_concy).
Proof.
exact (Build_Coinc_theory Tarski_is_a_Arity_for_concy Tarski_is_a_Coinc_predicates_for_concy not_col_perm_1 not_col_perm_2 concy_perm_1 concy_perm_2 concy_bd concy_3).
Qed.

End Tarski_is_a_Coinc_theory_for_concyclic.
