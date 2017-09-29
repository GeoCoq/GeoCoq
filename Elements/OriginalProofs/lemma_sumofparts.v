Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencetransitive.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_sumofparts : 
   forall A B C a b c, 
   Cong A B a b -> Cong B C b c -> BetS A B C -> BetS a b c ->
   Cong A C a c.
Proof.
intros.
assert (Cong A A a a) by (conclude axiom_nullsegment2).
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert (Cong a b b a) by (conclude cn_equalityreverse).
assert (Cong B A a b) by (conclude lemma_congruencetransitive).
assert (Cong B A b a) by (conclude lemma_congruencetransitive).
assert (Cong A C a c).
by cases on (neq A B \/ eq A B).
{
 assert (Cong A C a c) by (conclude axiom_5_line).
 close.
 }
{
 assert (Cong a b A B) by (conclude lemma_congruencesymmetric).
 assert (Cong a b A A) by (conclude cn_equalitysub).
 assert (eq a b) by (conclude axiom_nullsegment1).
 assert (Cong A C A C) by (conclude cn_congruencereflexive).
 assert (Cong B C A C) by (conclude cn_equalitysub).
 assert (Cong a c a c) by (conclude cn_congruencereflexive).
 assert (Cong b c a c) by (conclude cn_equalitysub).
 assert (Cong A C B C) by (conclude lemma_congruencesymmetric).
 assert (Cong A C b c) by (conclude lemma_congruencetransitive).
 assert (Cong A C a c) by (conclude lemma_congruencetransitive).
 close.
 }
(* cases *)
close.
Qed.

End Euclid.


