Require Export GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.
Require Export GeoCoq.Elements.OriginalProofs.lemma_outerconnectivity.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_trichotomy1 : 
   forall A B C D, 
   ~ Lt A B C D -> ~ Lt C D A B -> neq A B -> neq C D ->
   Cong A B C D.
Proof.
intros.
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists P, (BetS B A P /\ Cong A P A B)) by (conclude postulate_extension);destruct Tf as [P];spliter.
assert (BetS P A B) by (conclude axiom_betweennesssymmetry).
assert (Cong P A A B) by (forward_using lemma_congruenceflip).
assert (neq A P) by (forward_using lemma_betweennotequal).
assert (neq P A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists E, (BetS P A E /\ Cong A E C D)) by (conclude postulate_extension);destruct Tf as [E];spliter.
assert (~ BetS A B E).
 {
 intro.
 assert (Cong A B A B) by (conclude cn_congruencereflexive).
 assert (Lt A B A E) by (conclude_def Lt ).
 assert (Lt A B C D) by (conclude lemma_lessthancongruence).
 contradict.
 }
assert (~ BetS A E B).
 {
 intro.
 assert (Cong C D A E) by (conclude lemma_congruencesymmetric).
 assert (Lt C D A B) by (conclude_def Lt ).
 contradict.
 }
assert (eq E B) by (conclude lemma_outerconnectivity).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (Cong A B A E) by (conclude cn_equalitysub).
assert (Cong A B C D) by (conclude lemma_congruencetransitive).
close.
Qed.

End Euclid.


