Require Export GeoCoq.Main.Tarski_dev.Ch02_cong.
Require Import GeoCoq.Coinc.tactics_axioms.

(** In this file we prove that Tarski neutral dimensionless is a Cong_theory. *)

Section Tarski_is_a_Cong_theory.

Context `{Tn:Tarski_neutral_dimensionless}.

Global Instance Tarski_is_a_Cong_theory : (Cong_theory Tpoint Cong).
Proof.
exact (Build_Cong_theory Tpoint Cong cong_reflexivity cong_left_commutativity cong_symmetry cong_transitivity).
Defined.

End Tarski_is_a_Cong_theory.
