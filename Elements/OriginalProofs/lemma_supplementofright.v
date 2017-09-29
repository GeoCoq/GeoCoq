Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearright.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_supplementofright : 
   forall A B C D F, 
   Supp A B C D F -> Per A B C ->
   Per F B D /\ Per D B F.
Proof.
intros.
assert ((Out B C D /\ BetS A B F)) by (conclude_def Supp ).
assert (Per C B A) by (conclude lemma_8_2).
assert (Col A B F) by (conclude_def Col ).
assert (nCol A B C) by (conclude lemma_rightangleNC).
assert (neq A F) by (forward_using lemma_betweennotequal).
assert (neq F A) by (conclude lemma_inequalitysymmetric).
assert (neq B F) by (forward_using lemma_betweennotequal).
assert (neq F B) by (conclude lemma_inequalitysymmetric).
assert (Per F B C) by (conclude lemma_collinearright).
assert (Per F B D) by (conclude lemma_8_3).
assert (Per D B F) by (conclude lemma_8_2).
close.
Qed.

End Euclid.


