Require Export GeoCoq.Elements.OriginalProofs.lemma_paralleldef2B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelcollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidetransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidereflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_erectedperpendicularunique.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear5.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rayimpliescollinear.

Section Euclid.

Context `{Ax : euclidean_euclidean}.

Lemma lemma_intersectionunique :
   forall A B C D X Y,
   neq A B -> neq C D -> Col A B X -> Col A B Y -> Col C D X -> Col C D Y -> nCol A B C ->
   eq X Y.
Proof.
intros.
assert (~ neq X Y).
 {
 intro.
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (Col A B A) by (conclude_def Col ).
 assert (Col A B B) by (conclude_def Col ).
 assert (Col C D C) by (conclude_def Col ).
 assert (Col X Y A) by (conclude lemma_collinear5).
 assert (Col X Y B) by (conclude lemma_collinear5).
 assert (Col X Y C) by (conclude lemma_collinear5).
 assert (Col A B C) by (conclude lemma_collinear5).
 contradict.
 }
close.
Qed.

Lemma lemma_samesidepar :
   forall B C P Q X Y,
   Par P Q B C -> Col P Q X -> Col P Q Y ->
   OS X Y B C.
Proof.
intros.
assert (Par B C P Q) by (conclude lemma_parallelsymmetric).
assert (TP B C P Q) by (conclude lemma_paralleldef2B).
assert (OS P Q B C) by (conclude_def TP ).
assert (nCol P Q B) by (forward_using lemma_parallelNC).
assert (nCol P Q C) by (forward_using lemma_parallelNC).
assert (neq P Q) by (forward_using lemma_NCdistinct).
assert (nCol B C X).
 {
 assert (Par P Q B C) by (conclude lemma_parallelsymmetric).
 assert (~ Col B C X).
  {
  intro.
  assert (neq B C) by (conclude_def Par ).
  assert (Meet P Q B C) by (conclude_def Meet ).
  assert (~ Meet P Q B C) by (conclude_def Par ).
  contradict.
  }
 close.
 }
assert (OS X Q B C).
by cases on (eq X Q \/ neq X Q).
{
 assert (OS Q Q B C).
  {
  assert (nCol B C Q) by (conclude cn_equalitysub).
  conclude lemma_samesidereflexive.
  }
 assert (OS X Q B C) by (conclude cn_equalitysub).
 close.
 }
{
 assert (TP B C X Q) by (conclude lemma_parallelcollinear).
 assert (OS X Q B C) by (conclude_def TP ).
 close.
 }
assert (nCol B C Y).
 {
 assert (~ Col B C Y).
  {
  intro.
  assert (neq B C) by (conclude_def Par ).
  assert (Meet P Q B C) by (conclude_def Meet ).
  assert (~ Meet P Q B C) by (conclude_def Par ).
  contradict.
  }
 close.
 }
assert (OS Y Q B C).
by cases on (eq Y Q \/ neq Y Q).
{
 assert (OS Q Q B C).
  {
  assert (nCol B C Q) by (conclude cn_equalitysub).
  conclude lemma_samesidereflexive.
  }
 assert (OS Y Q B C) by (conclude cn_equalitysub).
 close.
 }
{
 assert (TP B C Y Q) by (conclude lemma_parallelcollinear).
 assert (OS Y Q B C) by (conclude_def TP ).
 close.
 }
assert (OS Q Y B C) by (forward_using lemma_samesidesymmetric).
assert (OS X Y B C) by (conclude lemma_samesidetransitive).
close.
Qed.

Lemma lemma_perpunique :
   forall B C P Q X Y,
   Per B C X -> Per B C Y -> Par P Q B C -> Col P Q X -> Col P Q Y ->
   eq X Y.
Proof.
intros.
assert (OS X Y B C) by (conclude lemma_samesidepar).
assert (Out C X Y) by (conclude lemma_erectedperpendicularunique).
assert (nCol P Q C) by (forward_using lemma_parallelNC).
assert (neq P Q) by (forward_using lemma_NCdistinct).
assert (~ neq X Y).
 {
 intro.
 assert (Col C X Y) by (conclude lemma_rayimpliescollinear).
 assert (Col X Y C) by (forward_using lemma_collinearorder).
 assert (Col P Q C).
  {
  assert (eq P P) by (conclude cn_equalityreflexive).
  assert (eq Q Q) by (conclude cn_equalityreflexive).
  assert (Col P Q P) by (conclude_def Col ).
  assert (Col P Q Q) by (conclude_def Col ).
  assert (Col X Y P) by (conclude lemma_collinear5).
  assert (Col X Y Q) by (conclude lemma_collinear5).
  conclude lemma_collinear5.
  }
 contradict.
 }
close.
Qed.

End Euclid.