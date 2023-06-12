Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Meta_theory.Models.gupta_inspired_to_tarski.
Require Import GeoCoq.Meta_theory.Parallel_postulates.parallel_postulates.
Require Import GeoCoq.Meta_theory.Counter_models.Planar.independent_version.

Section Neutral_2D.

Variable Tpoint : Type.

Context `{IT : independent_Tarski_neutral_dimensionless(Tpoint)}.
Context {ED : Eq_decidability(IT)}.
Context {IT2D : independent_Tarski_2D(IT)}.

Global Instance IT_to_GI : Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality.
Proof.
exact (Build_Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality
         Tpoint Bet Cong
         point_equality_decidability
         cong_pseudo_reflexivity cong_inner_transitivity cong_identity
         segment_construction five_segment
         bet_symmetry bet_inner_transitivity inner_pasch
         PA PB PC lower_dim).
Defined.

Global Instance IT2D_to_GI2D : Gupta_inspired_variant_of_Tarski_2D IT_to_GI.
Proof.
split; intros A B C P Q HPQ HAB HAC HBC HC1 HC2 HC3.
apply (upper_dim A B C P Q); auto.
Defined.

End Neutral_2D.

Section Euclidean.

Variable Tpoint : Type.

Context `{IT : independent_Tarski_neutral_dimensionless(Tpoint)}.
Context {ED : Eq_decidability(IT)}.
Context {IT2D : independent_Tarski_2D(IT)}.
Context {ITE : independent_Tarski_euclidean(IT)}.

Global Instance IT_euclidean_to_GI_euclidean :
  Gupta_inspired_variant_of_Tarski_euclidean (@IT_to_GI Tpoint IT ED IT2D).
Proof.
assert (HP : @tarski_s_parallel_postulate (@GI_to_T (@IT_to_GI Tpoint IT ED IT2D))).
  {
  assert (H : @proclus_postulate (@GI_to_T (@IT_to_GI Tpoint IT ED IT2D))).
    {
    intros A B C D P Q HPar HC HNC HCop.
    destruct (euclid A B C D P Q) as [Y [HC1 HC2]];
    [clear HC HNC HCop|intuition..|exists Y; intuition].
    destruct HPar as [HParS|HSL]; [left|right; intuition].
    destruct HParS as [HCop HNI]; split;
    [intro; subst; apply HNI; exists C; intuition|].
    split; [intro; subst; apply HNI; exists A; intuition|].
    split; [intuition|clear HCop].
    intros [X [HC1 HC2]]; apply HNI; exists X; intuition.
    }
  revert H; apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
  simpl; tauto.
  }
split; intros A B C D T HBet1 HBet2 HBD HDC HNC.
destruct (HP A B C D T) as [X [Y [HBet3 HBet4]]];
[intuition..| |exists X, Y; intuition].
intro; subst; apply HNC; right; right; apply bet_symmetry; auto.
Defined.

End Euclidean.
