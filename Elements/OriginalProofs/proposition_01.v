Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencetransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_nullsegment3.
Require Export GeoCoq.Elements.OriginalProofs.lemma_partnotequalwhole.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma proposition_01 : 
   forall A B, 
   neq A B ->
   exists X, equilateral A B X /\ Triangle A B X.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists J, CI J A A B) by (conclude circle);destruct Tf as [J];spliter.
let Tf:=fresh in
assert (Tf:exists K, CI K B A B) by (conclude circle);destruct Tf as [K];spliter.
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists D, (BetS B A D /\ Cong A D A B)) by (conclude postulate_extension);destruct Tf as [D];spliter.
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert ((CI K B A B /\ OutCirc D K)) by (conclude outside).
let Tf:=fresh in
assert (Tf:exists E, (BetS A B E /\ Cong B E A B)) by (conclude postulate_extension);destruct Tf as [E];spliter.
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert ((CI K B A B /\ InCirc B K)) by (conclude inside).
assert ((CI J A A B /\ OnCirc D J)) by (conclude on).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert ((CI J A A B /\ OnCirc B J)) by (conclude on).
let Tf:=fresh in
assert (Tf:exists C, (OnCirc C K /\ OnCirc C J)) by (conclude postulate_circle_circle);destruct Tf as [C];spliter.
assert (Cong A C A B) by (conclude on).
assert (Cong A B A C) by (conclude lemma_congruencesymmetric).
assert (Cong B C A B) by (conclude on).
assert (Cong B C A C) by (conclude lemma_congruencetransitive).
assert (Cong A B B C) by (conclude lemma_congruencesymmetric).
assert (Cong A C C A) by (conclude cn_equalityreverse).
assert (Cong B C C A) by (conclude lemma_congruencetransitive).

assert (equilateral A B C) by (conclude_def equilateral ).
assert (neq B C) by (conclude lemma_nullsegment3).
assert (neq C A) by (conclude lemma_nullsegment3).
assert (~ BetS A C B).
 {
 intro.
 assert (~ Cong A C A B) by (conclude lemma_partnotequalwhole).
 assert (Cong C A A C) by (conclude cn_equalityreverse).
 assert (Cong C A A B) by (conclude lemma_congruencetransitive).
 assert (Cong A C C A) by (conclude cn_equalityreverse).
 assert (Cong A C A B) by (conclude lemma_congruencetransitive).
 contradict.
 }
assert (~ BetS A B C).
 {
 intro.
 assert (~ Cong A B A C) by (conclude lemma_partnotequalwhole).
 assert (Cong A B C A) by (conclude lemma_congruencetransitive).
 assert (Cong C A A C) by (conclude cn_equalityreverse).
 assert (Cong A B A C) by (conclude lemma_congruencetransitive).
 contradict.
 }
assert (~ BetS B A C).
 {
 intro.
 assert (~ Cong B A B C) by (conclude lemma_partnotequalwhole).
 assert (Cong B A A B) by (conclude cn_equalityreverse).
 assert (Cong B A B C) by (conclude lemma_congruencetransitive).
 contradict.
 }
assert (~ Col A B C).
 {
 intro.
 assert (neq A C) by (conclude lemma_inequalitysymmetric).
 assert ((eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B)) by (conclude_def Col ).
 contradict.
 }
assert (Triangle A B C) by (conclude_def Triangle ).
close.
Qed.

End Euclid.


