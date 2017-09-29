Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_05 : 
   forall A B C, 
   isosceles A B C ->
   CongA A B C A C B.
Proof.
intros.
assert ((Triangle A B C /\ Cong A B A C)) by (conclude_def isosceles ).
assert (Cong A C A B) by (conclude lemma_congruencesymmetric).
assert (Cong B C C B) by (conclude cn_equalityreverse).
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ Col C A B).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle C A B) by (conclude_def Triangle ).
assert (~ Col B A C).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle B A C) by (conclude_def Triangle ).
assert (CongA C A B B A C) by (conclude lemma_ABCequalsCBA).
assert ((Cong C B B C /\ CongA A C B A B C /\ CongA A B C A C B)) by (conclude proposition_04).
close.
Qed.

End Euclid.


