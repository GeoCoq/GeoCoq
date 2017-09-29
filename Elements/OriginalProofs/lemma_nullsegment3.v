Require Export GeoCoq.Elements.OriginalProofs.euclidean_tactics.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_nullsegment3 : 
   forall A B C D, 
   neq A B -> Cong A B C D ->
   neq C D.
Proof.
intros.
assert (~ eq C D).
 {
 intro.
 assert (Cong A B C C) by (conclude cn_equalitysub).
 assert (eq A B) by (conclude axiom_nullsegment1).
 contradict.
 }
close.
Qed.

End Euclid.
