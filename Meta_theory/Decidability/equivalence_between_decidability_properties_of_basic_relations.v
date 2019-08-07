Require Export GeoCoq.Tarski_dev.Ch05_bet_le.
Require Import GeoCoq.Utils.all_equiv.

Section Equivalence_between_decidability_properties_of_basic_relations.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_dec_eq_dec :
  (forall A B C D, Cong A B C D \/ ~ Cong A B C D) ->
  (forall A B:Tpoint, A=B \/ A<>B).
Proof.
    intros H A B.
    elim (H A B A A); intro HCong.
      left; apply cong_identity with A; assumption.
    right; intro; subst; apply HCong.
    apply cong_pseudo_reflexivity.
Qed.

Lemma eq_dec_cong_dec :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  (forall A B C D, Cong A B C D \/ ~ Cong A B C D).
Proof.
intro eq_dec.
apply (@cong_dec Tn (Build_Tarski_neutral_dimensionless_with_decidable_point_equality Tn eq_dec)).
Qed.

Lemma bet_dec_eq_dec :
  (forall A B C, Bet A B C \/ ~ Bet A B C) ->
  (forall A B:Tpoint, A=B \/ A<>B).
Proof.
intros.
induction (H A B A).
left; apply between_identity; assumption.
right; intro; subst; apply H0;  apply between_trivial.
Qed.

Lemma eq_dec_bet_dec :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  (forall A B C, Bet A B C \/ ~ Bet A B C).
Proof.
intro eq_dec.
apply (@bet_dec Tn (Build_Tarski_neutral_dimensionless_with_decidable_point_equality Tn eq_dec)).
Qed.

Definition decidability_of_equality_of_points := forall A B:Tpoint, A=B \/ A<>B.

Definition decidability_of_congruence_of_points := forall A B C D:Tpoint,
  Cong A B C D \/ ~ Cong A B C D.

Definition decidability_of_betweenness_of_points := forall A B C:Tpoint,
  Bet A B C \/ ~ Bet A B C.

Theorem equivalence_between_decidability_properties_of_basic_relations :
  all_equiv  (decidability_of_equality_of_points::
              decidability_of_congruence_of_points::
              decidability_of_betweenness_of_points::nil).
Proof.
apply all_equiv__equiv.
simpl.
unfold decidability_of_equality_of_points, decidability_of_congruence_of_points,
        decidability_of_betweenness_of_points.
assert (P:=cong_dec_eq_dec).
assert (Q:=eq_dec_cong_dec).
assert (R:=bet_dec_eq_dec).
assert (S:=eq_dec_bet_dec).
repeat split; auto.
Qed.

End Equivalence_between_decidability_properties_of_basic_relations.
