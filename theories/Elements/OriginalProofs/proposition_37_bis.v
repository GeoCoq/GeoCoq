Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_35helper.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29C.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ETreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrotate.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trapezoiddiagonals.
Require Export GeoCoq.Elements.OriginalProofs.lemma_EFreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelPasch.
Require Export GeoCoq.Elements.OriginalProofs.lemma_triangletoparallelogram.

Section Euclid.

Context `{Ax : euclidean_euclidean}.

Existing Instance area_follows_Euclid.

Lemma proposition_37_bis :
   forall A B C D,
   Par A D B C ->
   ET A B C D B C.
Proof.
intros A B C D.
intros.
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (ET B C A B C D) by (conclude lemma_5_12).
assert (ET B C D B C A) by (conclude axiom_ETsymmetric).
assert (ET B C D A B C) by (forward_using axiom_ETpermutation).
assert (ET A B C B C D) by (conclude axiom_ETsymmetric).
assert (ET A B C D B C) by (forward_using axiom_ETpermutation).
close.
Qed.

End Euclid.