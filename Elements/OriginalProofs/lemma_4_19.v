Require Export GeoCoq.Elements.OriginalProofs.lemma_interior5.

Section Euclid.

Context `{Ax:euclidean_neutral}.


Lemma lemma_4_19 : 
   forall A B C D, 
   BetS A D B -> Cong A C A D -> Cong B D B C ->
   eq C D.
Proof.
intros.
assert (Cong A D A D) by (conclude cn_congruencereflexive).
assert (Cong D B D B) by (conclude cn_congruencereflexive).
assert (Cong B C B D) by (conclude lemma_congruencesymmetric).
assert (Cong D C D D) by (conclude lemma_interior5).
assert (eq D C) by (conclude axiom_nullsegment1).
assert (eq C D) by (conclude lemma_equalitysymmetric).
close.
Qed.

End Euclid.


