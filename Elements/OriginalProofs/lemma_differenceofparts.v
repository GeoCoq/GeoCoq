Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_nullsegment3.
Require Export GeoCoq.Elements.OriginalProofs.lemma_sumofparts.
Require Export GeoCoq.Elements.OriginalProofs.lemma_doublereverse.
Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_differenceofparts : 
   forall A B C a b c, 
   Cong A B a b -> Cong A C a c -> BetS A B C -> BetS a b c ->
   Cong B C b c.
Proof.
intros.
assert (Cong B C b c).
by cases on (eq B A \/ neq B A).
{
 assert (Cong A A a b) by (conclude cn_equalitysub).
 assert (Cong a b A A) by (conclude lemma_congruencesymmetric).
 assert (eq a b) by (conclude axiom_nullsegment1).
 assert (eq b a) by (conclude lemma_equalitysymmetric).
 assert (Cong A C A C) by (conclude cn_congruencereflexive).
 assert (Cong B C A C) by (conclude cn_equalitysub).
 assert (Cong A C B C) by (conclude lemma_congruencesymmetric).
 assert (Cong B C a c) by (conclude lemma_congruencetransitive).
 assert (Cong b c b c) by (conclude cn_congruencereflexive).
 assert (Cong b c a c) by (conclude cn_equalitysub).
 assert (Cong a c b c) by (conclude lemma_congruencesymmetric).
 assert (Cong B C b c) by (conclude lemma_congruencetransitive).
 close.
 }
{
 assert (~ eq C A).
  {
  intro.
  assert (BetS A B A) by (conclude cn_equalitysub).
  assert (~ BetS A B A) by (conclude axiom_betweennessidentity).
  contradict.
  }
 assert (neq A C) by (conclude lemma_inequalitysymmetric).
 let Tf:=fresh in
 assert (Tf:exists E, (BetS C A E /\ Cong A E A C)) by (conclude postulate_extension);destruct Tf as [E];spliter.
 assert (Cong a c A C) by (conclude lemma_congruencesymmetric).
 assert (neq A C) by (conclude lemma_inequalitysymmetric).
 assert (neq a c) by (conclude lemma_nullsegment3).
 assert (~ eq c a).
  {
  intro.
  assert (eq a c) by (conclude lemma_equalitysymmetric).
  contradict.
  }
 assert (neq a c) by (conclude lemma_inequalitysymmetric).
 let Tf:=fresh in
 assert (Tf:exists e, (BetS c a e /\ Cong a e a c)) by (conclude postulate_extension);destruct Tf as [e];spliter.
 assert (Cong A E a c) by (conclude lemma_congruencetransitive).
 assert (Cong a c A E) by (conclude lemma_congruencesymmetric).
 assert (Cong a c a e) by (conclude lemma_congruencesymmetric).
 assert (Cong A E a e) by (conclude cn_congruencetransitive).
 assert (Cong C C c c) by (conclude axiom_nullsegment2).
 assert (Cong E A A E) by (conclude cn_equalityreverse).
 assert (Cong E A A C) by (conclude lemma_congruencetransitive).
 assert (Cong E A a c) by (conclude lemma_congruencetransitive).
 assert (Cong e a a e) by (conclude cn_equalityreverse).
 assert (Cong e a a c) by (conclude lemma_congruencetransitive).
 assert (Cong a c e a) by (conclude lemma_congruencesymmetric).
 assert (Cong a c a e) by (conclude lemma_congruencetransitive).
 assert (Cong E A a c) by (conclude lemma_congruencetransitive).
 assert (Cong E A e a) by (conclude lemma_congruencetransitive).
 assert (BetS E A C) by (conclude axiom_betweennesssymmetry).
 assert (BetS e a c) by (conclude axiom_betweennesssymmetry).
 assert (Cong E C e c) by (conclude lemma_sumofparts).
 assert (Cong b a B A) by (forward_using lemma_doublereverse).
 assert (Cong B A b a) by (conclude lemma_congruencesymmetric).
 assert (Cong A E a e) by (conclude lemma_congruencetransitive).
 assert (Cong E A A E) by (conclude cn_equalityreverse).
 assert (Cong a e e a) by (conclude cn_equalityreverse).
 assert (Cong A E e a) by (conclude lemma_congruencetransitive).
 assert (Cong E A e a) by (conclude lemma_congruencetransitive).
 assert (BetS E A B) by (conclude axiom_innertransitivity).
 assert (BetS e a b) by (conclude axiom_innertransitivity).
 assert (neq E A) by (forward_using lemma_betweennotequal).
 assert (neq e a) by (forward_using lemma_betweennotequal).
 assert (Cong C B c b) by (conclude axiom_5_line).
 assert (Cong b c B C) by (forward_using lemma_doublereverse).
 assert (Cong B C b c) by (conclude lemma_congruencesymmetric).
 close.
 }
(* cases *)
close.
Qed.

End Euclid.


