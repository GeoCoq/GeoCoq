Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.
Require Export GeoCoq.Elements.OriginalProofs.lemma_nullsegment3.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencesymmetric.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_betweennesspreserved : 
   forall A B C a b c, 
   Cong A B a b -> Cong A C a c -> Cong B C b c -> BetS A B C ->
   BetS a b c.
Proof.
intros.
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq a b) by (conclude lemma_nullsegment3).
assert (neq B C) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists d, (BetS a b d /\ Cong b d B C)) by (conclude postulate_extension);destruct Tf as [d];spliter.
assert (Cong B C b d) by (conclude lemma_congruencesymmetric).
assert (Cong C C c d) by (conclude axiom_5_line).
assert (Cong c d C C) by (conclude lemma_congruencesymmetric).
assert (eq c d) by (conclude axiom_nullsegment1).
assert (BetS a b c) by (conclude cn_equalitysub).
close.
Qed.

End Euclid.


