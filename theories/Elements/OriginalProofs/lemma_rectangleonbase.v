Require Export GeoCoq.Elements.OriginalProofs.proposition_12.
Require Export GeoCoq.Elements.OriginalProofs.lemma_triangletoparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrectangle.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearright.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear5.

Section Euclid.

Context `{Ax : euclidean_euclidean}.

Lemma lemma_rectangleonbase :
   forall B C P Q,
   Par P Q B C ->
   exists X Y, RE X Y C B /\ Col P Q X /\ Col P Q Y.
Proof.
intros.
assert (nCol P Q B) by (forward_using lemma_parallelNC).
let Tf:=fresh in
assert (Tf:exists X, Perp_at B X P Q X) by (conclude proposition_12);destruct Tf as [X];spliter.
let Tf:=fresh in
assert (Tf:exists W, (Col B X X /\ Col P Q X /\ Col P Q W /\ Per W X B)) by (conclude_def Perp_at );destruct Tf as [W];spliter.
assert (Par B C P Q) by (conclude lemma_parallelsymmetric).
let Tf:=fresh in
assert (Tf:exists Y, (PG X Y C B /\ Col P Q Y)) by (conclude lemma_triangletoparallelogram);destruct Tf as [Y];spliter.
assert (Par X Y C B) by (conclude_def PG ).
assert (neq X Y) by (conclude_def Par ).
assert (neq Y X) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists U, (BetS W X U /\ Cong W X U X /\ Cong W B U B /\ neq X B)) by (conclude_def Per );destruct Tf as [U];spliter.
assert (neq W X) by (forward_using lemma_betweennotequal).
assert (neq P Q) by (forward_using lemma_NCdistinct).
assert (Col W X Y) by (conclude lemma_collinear5).
assert (Per Y X B) by (conclude lemma_collinearright).
assert (Per B X Y) by (conclude lemma_8_2).
assert (RE X Y C B) by (conclude lemma_PGrectangle).
close.
Qed.

End Euclid.