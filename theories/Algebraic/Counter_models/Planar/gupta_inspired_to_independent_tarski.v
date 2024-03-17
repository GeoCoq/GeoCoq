Require Import GeoCoq.Algebraic.Counter_models.Planar.independent_version.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Main.Meta_theory.Models.gupta_inspired_to_tarski.
Require Export GeoCoq.Main.Tarski_dev.Ch12_parallel_inter_dec.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Section Neutral_dimensionless.

Context `{GTnEQD : Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality}.

Global Instance GI_to_IT : independent_Tarski_neutral_dimensionless TpointG.
Proof.
exact (Build_independent_Tarski_neutral_dimensionless
         TpointG BetG CongG
         cong_pseudo_reflexivityG cong_inner_transitivityG cong_identityG
         segment_constructionG five_segmentG inner_paschG
         bet_symmetryG bet_inner_transitivityG).
Defined.

End Neutral_dimensionless.

Section Euclidean.

Context `{GTE : Gupta_inspired_variant_of_Tarski_euclidean}.

Global Instance GI_euclidean_to_IT_euclidean :
  independent_Tarski_euclidean GI_to_IT.
Proof.
assert (HP : @proclus_postulate GI_to_T).
  {
  assert (tarski_s_parallel_postulate);
  [unfold tarski_s_parallel_postulate; apply euclidT|revert H].
  apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
  simpl; tauto.
  }
split; intros A B C D P Q HPar HC HNC HCop.
destruct (HP A B C D P Q) as [Y [HC1 HC2]];
[clear HC HNC HCop|intuition..|exists Y; intuition].
destruct HPar as [HParS|HSL]; [left|right; intuition].
destruct HParS as [HCop HNI]; split; [intuition|clear HCop].
intros [X [HC1 HC2]]; apply HNI; exists X; intuition.
Defined.

End Euclidean.

Section Planar.

Context `{GT2D : Gupta_inspired_variant_of_Tarski_2D}.

Global Instance GI2D_to_IT2D : independent_Tarski_2D GI_to_IT.
Proof.
apply (Build_independent_Tarski_2D TpointG GI_to_IT GPA GPB GPC lower_dimG).
intros A B C P Q HPQ HAB HAC HBC; apply upper_dimG; auto.
Defined.

End Planar.
