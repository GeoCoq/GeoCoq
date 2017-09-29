Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencesymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_extensionunique : 
   forall A B E F, 
   BetS A B E -> BetS A B F -> Cong B E B F ->
   eq E F.
Proof.
intros.
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (Cong B E B E) by (conclude cn_congruencereflexive).
assert (Cong B F B E) by (conclude lemma_congruencesymmetric).
assert (Cong A E A E) by (conclude cn_congruencereflexive).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (Cong B E B F) by (conclude lemma_congruencesymmetric).
assert (Cong E E E F) by (conclude axiom_5_line).
assert (Cong E F E E) by (conclude lemma_congruencesymmetric).
assert (eq E F) by (conclude axiom_nullsegment1).
close.
Qed.

End Euclid.


