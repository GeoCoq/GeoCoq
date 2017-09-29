Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencetransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennesspreserved.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_collinearitypreserved : 
   forall A B C a b c, 
   Col A B C -> Cong A B a b -> Cong A C a c -> Cong B C b c ->
   Col a b c.
Proof.
intros.
assert (Cong C B B C) by (conclude cn_equalityreverse).
assert (Cong c b b c) by (conclude cn_equalityreverse).
assert (Cong C B b c) by (conclude lemma_congruencetransitive).
assert (Cong b c c b) by (conclude cn_equalityreverse).
assert (Cong C B c b) by (conclude lemma_congruencetransitive).
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert (Cong a b b a) by (conclude cn_equalityreverse).
assert (Cong A B b a) by (conclude lemma_congruencetransitive).
assert (Cong A B B A) by (conclude cn_equalityreverse).
assert (Cong B A A B) by (conclude lemma_congruencesymmetric).
assert (Cong B A b a) by (conclude lemma_congruencetransitive).
assert ((eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B)) by (conclude_def Col ).
assert (Col a b c).
by cases on (eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B).
{
 assert (Cong A A a b) by (conclude cn_equalitysub).
 assert (Cong a b A A) by (conclude lemma_congruencesymmetric).
 assert (eq a b) by (conclude axiom_nullsegment1).
 assert (Col a b c) by (conclude_def Col ).
 close.
 }
{
 assert (Cong A A a c) by (conclude cn_equalitysub).
 assert (Cong a c A A) by (conclude lemma_congruencesymmetric).
 assert (eq a c) by (conclude axiom_nullsegment1).
 assert (Col a b c) by (conclude_def Col ).
 close.
 }
{
 assert (Cong B B b c) by (conclude cn_equalitysub).
 assert (Cong b c B B) by (conclude lemma_congruencesymmetric).
 assert (eq b c) by (conclude axiom_nullsegment1).
 assert (Col a b c) by (conclude_def Col ).
 close.
 }
{
 assert (Cong_3 B A C b a c) by (conclude_def Cong_3 ).
 assert (BetS b a c) by (conclude lemma_betweennesspreserved).
 assert (Col a b c) by (conclude_def Col ).
 close.
 }
{
 assert (BetS a b c) by (conclude lemma_betweennesspreserved).
 assert (Col a b c) by (conclude_def Col ).
 close.
 }
{
 assert (Cong_3 A C B a c b) by (conclude_def Cong_3 ).
 assert (BetS a c b) by (conclude lemma_betweennesspreserved).
 assert (Col a b c) by (conclude_def Col ).
 close.
 }
(* cases *)
close.
Qed.

End Euclid.


