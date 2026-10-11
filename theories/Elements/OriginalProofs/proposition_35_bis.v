Require Export GeoCoq.Elements.OriginalProofs.proposition_34.
Require Export GeoCoq.Elements.OriginalProofs.proposition_37_bis.
Require Export GeoCoq.Elements.OriginalProofs.lemma_diagonalsmeet.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ETreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrotate.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.

Section Euclid.

Context `{Ax : euclidean_euclidean}.

Existing Instance area_follows_Euclid.

Lemma proposition_35_bis :
   forall A B C D E F,
   PG A B C D -> PG E B C F -> Col A D E -> Col A D F ->
   EF A B C D E B C F.
Proof.
intros A B C D E F.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert ((Par E B C F /\ Par E F B C)) by (conclude_def PG ).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (ET A B C F B C).
by cases on (eq A F \/ neq A F).
{
 assert (Triangle A B C) by (conclude_def Triangle ).
 assert (ET A B C A B C) by (conclude lemma_ETreflexive).
 assert (ET A B C F B C) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Par B C A D) by (conclude lemma_parallelsymmetric).
 assert (Col A D A) by (conclude_def Col ).
 assert (Par B C A F) by (conclude lemma_collinearparallel2).
 assert (Par A F B C) by (conclude lemma_parallelsymmetric).
 assert (ET A B C F B C) by (conclude proposition_37_bis).
 close.
 }
assert (PG B C D A) by (conclude lemma_PGrotate).
assert (Cong_3 C B A A D C) by (forward_using proposition_34).
assert (Cong_3 B E F F C B) by (forward_using proposition_34).
assert (nCol C B A) by (forward_using lemma_NCorder).
assert (Triangle C B A) by (conclude_def Triangle ).
assert (ET C B A A D C) by (conclude axiom_congruentequal).
assert (nCol E B F) by (forward_using lemma_parallelNC).
assert (nCol B E F) by (forward_using lemma_NCorder).
assert (Triangle B E F) by (conclude_def Triangle ).
assert (ET B E F F C B) by (conclude axiom_congruentequal).
assert (ET A D C C B A) by (conclude axiom_ETsymmetric).
assert (ET A D C A B C) by (forward_using axiom_ETpermutation).
assert (ET A D C F B C) by (conclude axiom_ETtransitive).
assert (ET F B C A D C) by (conclude axiom_ETsymmetric).
assert (ET F B C A C D) by (forward_using axiom_ETpermutation).
assert (ET A C D F B C) by (conclude axiom_ETsymmetric).
assert (ET B E F F B C) by (forward_using axiom_ETpermutation).
assert (ET F B C B E F) by (conclude axiom_ETsymmetric).
assert (ET F B C B F E) by (forward_using axiom_ETpermutation).
assert (ET A C D B F E) by (conclude axiom_ETtransitive).
assert (ET A B C B F C) by (forward_using axiom_ETpermutation).
assert (ET B F C A B C) by (conclude axiom_ETsymmetric).
assert (ET B F C A C B) by (forward_using axiom_ETpermutation).
assert (ET A C B B F C) by (conclude axiom_ETsymmetric).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
let Tf:=fresh in
assert (Tf:exists m, (BetS E m C /\ BetS B m F)) by (conclude lemma_diagonalsmeet);destruct Tf as [m];spliter.
assert (BetS C m E) by (conclude axiom_betweennesssymmetry).
assert (EF A B C D B C F E) by (conclude axiom_paste3).
assert (EF A B C D E B C F) by (forward_using axiom_EFpermutation).
close.
Qed.

End Euclid.