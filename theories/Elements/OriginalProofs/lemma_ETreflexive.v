Require Export GeoCoq.Axioms.euclidean_area_axioms.
Require Export GeoCoq.Elements.euclid_to_area.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TCreflexive.

Section Euclid.

Context `{Ax : euclidean_euclidean}.

Existing Instance area_follows_Euclid.

Lemma lemma_ETreflexive :
   forall A B C,
   Triangle A B C ->
   ET A B C A B C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (Cong_3 A B C A B C) by (conclude lemma_TCreflexive).
assert (ET A B C A B C) by (conclude axiom_congruentequal).
close.
Qed.

End Euclid.