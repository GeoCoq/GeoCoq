Require Export GeoCoq.Elements.OriginalProofs.lemma_30helper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crossimpliesopposite.
Require Export GeoCoq.Elements.OriginalProofs.proposition_30B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.
Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax : euclidean_euclidean}.

Lemma lemma_TSchoice :
   forall A G H E b f,
   Par A b E f -> BetS A G b -> BetS E H f ->
   TS A G H f \/ TS b G H f.
Proof.
intros.
assert (Col A G b) by (conclude_def Col ).
assert (Col A b G) by (forward_using lemma_collinearorder).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A b A) by (conclude_def Col ).
assert (neq A G) by (forward_using lemma_betweennotequal).
assert (Col E H f) by (conclude_def Col ).
assert (Col E f H) by (forward_using lemma_collinearorder).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (eq f f) by (conclude cn_equalityreflexive).
assert (Col E f E) by (conclude_def Col ).
assert (Col E f f) by (conclude_def Col ).
assert (neq E H) by (forward_using lemma_betweennotequal).
assert (neq H f) by (forward_using lemma_betweennotequal).
assert (neq f H) by (conclude lemma_inequalitysymmetric).
assert (Par E f A b) by (conclude lemma_parallelsymmetric).
assert (Par E f A G) by (conclude lemma_collinearparallel2).
assert (Par A G E f) by (conclude lemma_parallelsymmetric).
assert (Par A G E H) by (conclude lemma_collinearparallel2).
assert (Par A G f H) by (conclude lemma_collinearparallel2).
assert (nCol A G H) by (forward_using lemma_parallelNC).
assert (nCol G f H) by (forward_using lemma_parallelNC).
assert (nCol G H f) by (forward_using lemma_NCorder).
assert (nCol G H A) by (forward_using lemma_NCorder).
assert (~ ~ (CR A f G H \/ CR A E G H)).
 {
 intro.
 assert (CR A E G H) by (conclude lemma_30helper).
 contradict.
 }
by cases on (CR A f G H \/ CR A E G H).
{
 assert (TS A G H f) by (forward_using lemma_crossimpliesopposite).
 left.
 close.
 }
{
 assert (TS A G H E) by (forward_using lemma_crossimpliesopposite).
 assert (BetS f H E) by (conclude axiom_betweennesssymmetry).
 assert (eq H H) by (conclude cn_equalityreflexive).
 assert (Col G H H) by (conclude_def Col ).
 assert (TS f G H E) by (conclude_def TS ).
 let Tf:=fresh in
 assert (Tf:exists U, (BetS A U E /\ Col G H U /\ nCol G H A)) by (conclude_def TS );destruct Tf as [U];spliter.
 let Tf:=fresh in
 assert (Tf:exists V, (BetS f V E /\ Col G H V /\ nCol G H f)) by (conclude_def TS );destruct Tf as [V];spliter.
 assert (OS A f G H) by (conclude_def OS ).
 assert (OS f A G H) by (forward_using lemma_samesidesymmetric).
 assert (eq G G) by (conclude cn_equalityreflexive).
 assert (Col G H G) by (conclude_def Col ).
 assert (TS A G H b) by (conclude_def TS ).
 assert (TS f G H b) by (conclude lemma_planeseparation).
 assert (TS b G H f) by (conclude lemma_oppositesidesymmetric).
 right.
 close.
 }
Qed.

Lemma lemma_paralleltransitiveouter :
   forall A B C D E F G H K,
   Par A B E F -> Par C D E F -> BetS G K H -> Col A B G -> Col E F H -> Col C D K ->
   neq A G -> neq E H -> neq C K ->
   Par A B C D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists b, (BetS A G b /\ Cong G b A G)) by (conclude lemma_extension);destruct Tf as [b];spliter.
let Tf:=fresh in
assert (Tf:exists f, (BetS E H f /\ Cong H f E H)) by (conclude lemma_extension);destruct Tf as [f];spliter.
let Tf:=fresh in
assert (Tf:exists d, (BetS C K d /\ Cong K d C K)) by (conclude lemma_extension);destruct Tf as [d];spliter.
assert (nCol C D E) by (forward_using lemma_parallelNC).
assert (neq C D) by (forward_using lemma_NCdistinct).
assert (Col A G b) by (conclude_def Col ).
assert (Col G A b) by (forward_using lemma_collinearorder).
assert (Col G A B) by (forward_using lemma_collinearorder).
assert (neq G A) by (conclude lemma_inequalitysymmetric).
assert (Col A b B) by (conclude lemma_collinear4).
assert (Col B A b) by (forward_using lemma_collinearorder).
assert (Par E F A B) by (conclude lemma_parallelsymmetric).
assert (Par E F B A) by (forward_using lemma_parallelflip).
assert (neq A b) by (forward_using lemma_betweennotequal).
assert (neq b A) by (conclude lemma_inequalitysymmetric).
assert (Par E F b A) by (conclude lemma_collinearparallel).
assert (Par E F A b) by (forward_using lemma_parallelflip).
assert (Par A b E F) by (conclude lemma_parallelsymmetric).
assert (Col E H f) by (conclude_def Col ).
assert (Col H E f) by (forward_using lemma_collinearorder).
assert (Col H E F) by (forward_using lemma_collinearorder).
assert (neq H E) by (conclude lemma_inequalitysymmetric).
assert (Col E f F) by (conclude lemma_collinear4).
assert (Col F E f) by (forward_using lemma_collinearorder).
assert (neq E f) by (forward_using lemma_betweennotequal).
assert (neq f E) by (conclude lemma_inequalitysymmetric).
assert (Par A b F E) by (forward_using lemma_parallelflip).
assert (Par A b f E) by (conclude lemma_collinearparallel).
assert (Par A b E f) by (forward_using lemma_parallelflip).
assert (Col C K d) by (conclude_def Col ).
assert (Col K C d) by (forward_using lemma_collinearorder).
assert (Col K C D) by (forward_using lemma_collinearorder).
assert (neq K C) by (conclude lemma_inequalitysymmetric).
assert (Col C d D) by (conclude lemma_collinear4).
assert (Col D C d) by (forward_using lemma_collinearorder).
assert (Par E F C D) by (conclude lemma_parallelsymmetric).
assert (Par E F D C) by (forward_using lemma_parallelflip).
assert (neq C d) by (forward_using lemma_betweennotequal).
assert (neq d C) by (conclude lemma_inequalitysymmetric).
assert (Par E F d C) by (conclude lemma_collinearparallel).
assert (Par E F C d) by (forward_using lemma_parallelflip).
assert (Par C d E F) by (conclude lemma_parallelsymmetric).
assert (Par C d F E) by (forward_using lemma_parallelflip).
assert (Par C d f E) by (conclude lemma_collinearparallel).
assert (Par C d E f) by (forward_using lemma_parallelflip).
assert (Par b A E f) by (forward_using lemma_parallelflip).
assert (Par d C E f) by (forward_using lemma_parallelflip).
assert (BetS b G A) by (conclude axiom_betweennesssymmetry).
assert (BetS d K C) by (conclude axiom_betweennesssymmetry).
assert (TS A G H f \/ TS b G H f) by (conclude lemma_TSchoice).
assert (TS C K H f \/ TS d K H f) by (conclude lemma_TSchoice).
assert (Par A b C d).
by cases on (TS A G H f \/ TS b G H f).
{
 by cases on (TS C K H f \/ TS d K H f).
 {
  assert (Par A b C d) by (conclude proposition_30B).
  close.
  }
 {
  assert (Par A b d C) by (conclude proposition_30B).
  assert (Par A b C d) by (forward_using lemma_parallelflip).
  close.
  }
 }
{
 by cases on (TS C K H f \/ TS d K H f).
 {
  assert (Par b A C d) by (conclude proposition_30B).
  assert (Par A b C d) by (forward_using lemma_parallelflip).
  close.
  }
 {
  assert (Par b A d C) by (conclude proposition_30B).
  assert (Par A b C d) by (forward_using lemma_parallelflip).
  close.
  }
 }
assert (Par A b d C) by (forward_using lemma_parallelflip).
assert (Col d C D) by (forward_using lemma_collinearorder).
assert (neq D C) by (conclude lemma_inequalitysymmetric).
assert (Par A b D C) by (conclude lemma_collinearparallel).
assert (Par A b C D) by (forward_using lemma_parallelflip).
assert (Par C D A b) by (conclude lemma_parallelsymmetric).
assert (Par C D b A) by (forward_using lemma_parallelflip).
assert (Col b A B) by (forward_using lemma_collinearorder).
assert (nCol A B E) by (forward_using lemma_parallelNC).
assert (neq B A) by (forward_using lemma_NCdistinct).
assert (Par C D B A) by (conclude lemma_collinearparallel).
assert (Par C D A B) by (forward_using lemma_parallelflip).
assert (Par A B C D) by (conclude lemma_parallelsymmetric).
close.
Qed.

End Euclid.