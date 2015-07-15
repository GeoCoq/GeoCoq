Require Export Coplanar_trans.
Require Import tactics_axioms.

(* In this file we prove that Col in Tarski neutral dimensionless is a Coapp_theory *)

Section Tarski_is_a_Coapp_theory_for_cop.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Definition not_col : arity Tpoint 3 := fun A B C : Tpoint => ~ Col A B C.

Lemma not_col_perm_1 : forall A X, app_1_n not_col A X -> app_n_1 not_col X A.
Proof.
unfold not_col.
simpl.
Col.
Qed.

Lemma not_col_perm_2 : forall A B (X : cartesianPower Tpoint 1),
  app_2_n not_col A B X -> app_2_n not_col B A X.
Proof.
unfold not_col.
unfold app_2_n.
simpl.
Col.
Qed.

Definition cop : arity Tpoint 4 := coplanar.

Lemma cop_perm_1 : forall A (X : cartesianPower Tpoint 3), app_1_n cop A X -> app_n_1 cop X A.
Proof.
unfold cop.
simpl.
Cop.
Qed.

Lemma cop_perm_2 : forall A B (X : cartesianPower Tpoint 2), app_2_n cop A B X -> app_2_n cop B A X.
Proof.
unfold cop.
unfold app_2_n.
simpl.
Cop.
Qed.

Lemma cop_bd : forall A (X : cartesianPower Tpoint 2), app_2_n cop A A X.
Proof.
unfold cop.
unfold app_2_n.
simpl.
Cop.
Qed.

Lemma cop_3 : forall (COP : cartesianPower Tpoint 4) (NOT_COL : cartesianPower Tpoint 3),
  pred_conj cop COP NOT_COL -> app not_col NOT_COL -> app cop COP.
Proof.
unfold pred_conj.
unfold cop.
unfold not_col.
simpl in *.
intros COP NOT_COL HCop HNot_Col.
destruct HCop as [HCop1 [HCop2 [HCop3 HCop4]]].
apply coplanar_pseudo_trans with (fst NOT_COL) (fst (snd NOT_COL)) (snd (snd NOT_COL)); Cop.
Qed.

Global Instance Tarski_is_a_Coapp_theory : (Coapp_theory (Build_Arity Tpoint 1) (Build_Coapp_predicates (Build_Arity Tpoint 1) not_col cop)).
Proof.
exact (Build_Coapp_theory (Build_Arity Tpoint 1) (Build_Coapp_predicates (Build_Arity Tpoint 1) not_col cop) not_col_perm_1 not_col_perm_2 cop_perm_1 cop_perm_2 cop_bd cop_3).
Qed.

End Tarski_is_a_Coapp_theory_for_cop.