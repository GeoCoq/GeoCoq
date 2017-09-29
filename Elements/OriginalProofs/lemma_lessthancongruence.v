Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_sumofparts.
Require Export GeoCoq.Elements.OriginalProofs.lemma_doublereverse.
Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennesspreserved.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_lessthancongruence : 
   forall A B C D E F, 
   Lt A B C D -> Cong C D E F ->
   Lt A B E F.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists G, (BetS C G D /\ Cong C G A B)) by (conclude_def Lt );destruct Tf as [G];spliter.
assert (neq C D) by (forward_using lemma_betweennotequal).
assert (neq E F) by (conclude lemma_nullsegment3).
assert (~ eq F E).
 {
 intro.
 assert (eq E F) by (conclude lemma_equalitysymmetric).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists P, (BetS F E P /\ Cong E P F E)) by (conclude postulate_extension);destruct Tf as [P];spliter.
assert (BetS P E F) by (conclude axiom_betweennesssymmetry).
assert (neq P E) by (forward_using lemma_betweennotequal).
assert (neq C G) by (forward_using lemma_betweennotequal).
assert (neq A B) by (conclude lemma_nullsegment3).
let Tf:=fresh in
rename_H;
assert (Tf:exists H, (BetS P E H /\ Cong E H A B)) by (conclude postulate_extension);destruct Tf as [H];spliter.
assert (~ eq D C).
 {
 intro.
 assert (BetS C G C) by (conclude cn_equalitysub).
 assert (~ BetS C G C) by (conclude axiom_betweennessidentity).
 contradict.
 }
assert (neq P E) by (forward_using lemma_betweennotequal).
assert (neq E P) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists Q, (BetS D C Q /\ Cong C Q E P)) by (conclude postulate_extension);destruct Tf as [Q];spliter.
assert (BetS Q C D) by (conclude axiom_betweennesssymmetry).
assert (Cong Q C C Q) by (conclude cn_equalityreverse).
assert (Cong Q C E P) by (conclude lemma_congruencetransitive).
assert (Cong E P P E) by (conclude cn_equalityreverse).
assert (Cong Q C P E) by (conclude lemma_congruencetransitive).
assert (Cong Q D P F) by (conclude lemma_sumofparts).
assert (Cong A B E H) by (conclude lemma_congruencesymmetric).
assert (Cong C G E H) by (conclude lemma_congruencetransitive).
assert (neq Q C) by (forward_using lemma_betweennotequal).
assert (BetS Q C G) by (conclude axiom_innertransitivity).
assert (Cong P F Q D) by (conclude lemma_congruencesymmetric).
assert (Cong D G F H) by (conclude axiom_5_line).
assert (Cong G D H F) by (forward_using lemma_doublereverse).
assert (BetS E H F) by (conclude lemma_betweennesspreserved).
assert (Lt A B E F) by (conclude_def Lt ).
close.
Qed.

End Euclid.


