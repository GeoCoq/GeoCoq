Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence2.
Require Export GeoCoq.Elements.OriginalProofs.proposition_03.
Require Export GeoCoq.Elements.OriginalProofs.proposition_15.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_pointreflectionisometry : 
   forall A B C P Q, 
   Midpoint A B C -> Midpoint P B Q ->
   Cong A P C Q.
Proof.
intros.
assert ((BetS A B C /\ Cong A B B C)) by (conclude_def Midpoint ).
assert ((BetS P B Q /\ Cong P B B Q)) by (conclude_def Midpoint ).
assert (Cong A P C Q).
by cases on (Col A B P \/ nCol A B P).
{
 assert ((eq A B \/ eq A P \/ eq B P \/ BetS B A P \/ BetS A B P \/ BetS A P B)) by (conclude_def Col ).
 assert (Cong A P C Q).
 by cases on (eq A B \/ eq A P \/ eq B P \/ BetS B A P \/ BetS A B P \/ BetS A P B).
 {
  assert (~ ~ Cong A P C Q).
   {
   intro.
   assert (BetS A B C) by (conclude_def Midpoint ).
   assert (neq A B) by (forward_using lemma_betweennotequal).
   contradict.
   }
  close.
  }
 {
  assert (BetS A B Q) by (conclude cn_equalitysub).
  assert (Cong B C A B) by (conclude lemma_congruencesymmetric).
  assert (Cong A B A B) by (conclude cn_congruencereflexive).
  assert (Cong A B P B) by (conclude cn_equalitysub).
  assert (Cong B C P B) by (conclude lemma_congruencetransitive).
  assert (Cong B C B Q) by (conclude lemma_congruencetransitive).
  assert (eq C Q) by (conclude lemma_extensionunique).
  assert (Cong C Q C Q) by (conclude cn_congruencereflexive).
  assert (Cong C Q C C) by (conclude cn_equalitysub).
  assert (Cong C C C Q) by (conclude lemma_congruencesymmetric).
  assert (Cong A P A P) by (conclude cn_congruencereflexive).
  assert (Cong A P A A) by (conclude cn_equalitysub).
  assert (Cong A A C C) by (conclude axiom_nullsegment2).
  assert (Cong A P C C) by (conclude lemma_congruencetransitive).
  assert (Cong A P C Q) by (conclude lemma_congruencetransitive).
  close.
  }
 {
  assert (~ ~ Cong A P C Q).
   {
   intro.
   assert (neq P B) by (forward_using lemma_betweennotequal).
   assert (neq B P) by (conclude lemma_inequalitysymmetric).
   contradict.
   }
  close.
  }
 {
  assert (Cong P B Q B) by (forward_using lemma_congruenceflip).
  assert (Cong A B C B) by (forward_using lemma_congruenceflip).
  assert (Cong B C A B) by (conclude lemma_congruencesymmetric).
  assert (Cong B C B A) by (forward_using lemma_congruenceflip).
  assert (Cong Q B B P) by (forward_using lemma_doublereverse).
  assert (Cong B Q B P) by (forward_using lemma_congruenceflip).
  assert (BetS P A B) by (conclude axiom_betweennesssymmetry).
  assert (Cong C B B A) by (forward_using lemma_congruenceflip).
  assert (Cong B A C B) by (forward_using lemma_doublereverse).
  assert (Lt C B B P) by (conclude_def Lt ).
  assert (Cong B P B Q) by (conclude lemma_congruencesymmetric).
  assert (Lt C B B Q) by (conclude lemma_lessthancongruence).
  assert (Cong C B B C) by (conclude cn_equalityreverse).
  assert (Lt B C B Q) by (conclude lemma_lessthancongruence2).
  assert (Cong B Q B Q) by (conclude cn_congruencereflexive).
  assert (neq B Q) by (forward_using lemma_betweennotequal).
  assert (neq B C) by (forward_using lemma_betweennotequal).
  let Tf:=fresh in
rename_H;
  assert (Tf:exists H, (BetS B H Q /\ Cong B H B C)) by (conclude proposition_03);destruct Tf as [H];spliter.
  assert (Out B Q H) by (conclude lemma_ray4).
  assert (BetS P A B) by (conclude axiom_betweennesssymmetry).
  assert (BetS P B C) by (conclude lemma_3_7a).
  assert (Out B C Q) by (conclude_def Out ).
  assert (Out B Q C) by (conclude lemma_ray5).
  assert (Cong B C B H) by (conclude lemma_congruencesymmetric).
  assert (eq C H) by (conclude lemma_layoffunique).
  assert (BetS B C Q) by (conclude cn_equalitysub).
  assert (BetS B A P) by (conclude axiom_betweennesssymmetry).
  assert (Cong B A B C) by (conclude lemma_congruencesymmetric).
  assert (Cong A P C Q) by (conclude lemma_differenceofparts).
  close.
  }
 {
  assert (~ ~ Cong A P C Q).
   {
   intro.
   assert (~ BetS B P C).
    {
    intro.
    assert (BetS C P B) by (conclude axiom_betweennesssymmetry).
    assert (BetS C B Q) by (conclude lemma_3_7a).
    assert (BetS Q B C) by (conclude axiom_betweennesssymmetry).
    assert (Cong A B C B) by (forward_using lemma_congruenceflip).
    assert (Cong B P Q B) by (forward_using lemma_congruenceflip).
    assert (Cong B P B Q) by (forward_using lemma_congruenceflip).
    assert (Cong A P C Q) by (conclude lemma_sumofparts).
    contradict.
    }
   assert (~ BetS B C P).
    {
    intro.
    assert (BetS A B P) by (conclude lemma_3_7b).
    assert (BetS Q B P) by (conclude axiom_betweennesssymmetry).
    assert (BetS Q B C) by (conclude axiom_innertransitivity).
    assert (BetS C B Q) by (conclude axiom_betweennesssymmetry).
    assert (Cong A B C B) by (forward_using lemma_congruenceflip).
    assert (Cong B P B Q) by (forward_using lemma_congruenceflip).
    assert (Cong A P C Q) by (conclude lemma_sumofparts).
    contradict.
    }
   assert (eq P C) by (conclude lemma_outerconnectivity).
   assert (Cong A B B P) by (conclude cn_equalitysub).
   assert (Cong B P B Q) by (forward_using lemma_congruenceflip).
   assert (Cong A B B Q) by (conclude lemma_congruencetransitive).
   assert (BetS C B A) by (conclude axiom_betweennesssymmetry).
   assert (BetS P B A) by (conclude cn_equalitysub).
   assert (Cong B Q A B) by (conclude lemma_congruencesymmetric).
   assert (Cong B Q B A) by (forward_using lemma_congruenceflip).
   assert (neq B Q) by (forward_using lemma_betweennotequal).
   assert (neq Q B) by (conclude lemma_inequalitysymmetric).
   assert (eq Q A) by (conclude lemma_extensionunique).
   assert (Cong A C C A) by (conclude cn_equalityreverse).
   assert (Cong A P C A) by (conclude cn_equalitysub).
   assert (Cong A P C Q) by (conclude cn_equalitysub).
   contradict.
   }
  close.
  }
 {
  assert (Cong A B C B) by (forward_using lemma_congruenceflip).
  assert (Cong P B Q B) by (forward_using lemma_congruenceflip).
  assert (Cong B Q P B) by (conclude lemma_congruencesymmetric).
  assert (Cong B Q B P) by (forward_using lemma_congruenceflip).
  assert (Cong C B B A) by (forward_using lemma_doublereverse).
  assert (Cong B C B A) by (forward_using lemma_congruenceflip).
  assert (BetS B P A) by (conclude axiom_betweennesssymmetry).
  assert (Cong Q B B P) by (forward_using lemma_congruenceflip).
  assert (Cong B P Q B) by (forward_using lemma_doublereverse).
  assert (Lt Q B B A) by (conclude_def Lt ).
  assert (Cong B A B C) by (conclude lemma_congruencesymmetric).
  assert (Lt Q B B C) by (conclude lemma_lessthancongruence).
  assert (Cong Q B B Q) by (conclude cn_equalityreverse).
  assert (Lt B Q B C) by (conclude lemma_lessthancongruence2).
  assert (Cong B C B C) by (conclude cn_congruencereflexive).
  assert (neq B C) by (forward_using lemma_betweennotequal).
  assert (neq B Q) by (forward_using lemma_betweennotequal).
  let Tf:=fresh in
rename_H;
  assert (Tf:exists H, (BetS B H C /\ Cong B H B Q)) by (conclude proposition_03);destruct Tf as [H];spliter.
  assert (BetS P B C) by (conclude lemma_3_6a).
  assert (Out B C Q) by (conclude_def Out ).
  assert (Out B Q C) by (conclude lemma_ray5).
  assert (Out B C H) by (conclude lemma_ray4).
  assert (Cong B Q B H) by (conclude lemma_congruencesymmetric).
  assert (eq Q H) by (conclude lemma_layoffunique).
  assert (BetS B Q C) by (conclude cn_equalitysub).
  assert (BetS B P A) by (conclude axiom_betweennesssymmetry).
  assert (Cong B P B Q) by (conclude lemma_congruencesymmetric).
  assert (Cong P A Q C) by (conclude lemma_differenceofparts).
  assert (Cong A P C Q) by (forward_using lemma_congruenceflip).
  close.
  }
(* cases *)
 close.
 }
{
 assert (CongA A B P Q B C) by (conclude proposition_15a).
 assert (Triangle A B P) by (conclude_def Triangle ).
 assert (~ Col C B Q).
  {
  intro.
  assert (Col A B C) by (conclude_def Col ).
  assert (Col C B A) by (forward_using lemma_collinearorder).
  assert (neq B C) by (forward_using lemma_betweennotequal).
  assert (neq C B) by (conclude lemma_inequalitysymmetric).
  assert (Col B Q A) by (conclude lemma_collinear4).
  assert (Col P B Q) by (conclude_def Col ).
  assert (Col Q B P) by (forward_using lemma_collinearorder).
  assert (Col Q B A) by (forward_using lemma_collinearorder).
  assert (neq B Q) by (forward_using lemma_betweennotequal).
  assert (neq Q B) by (conclude lemma_inequalitysymmetric).
  assert (Col B P A) by (conclude lemma_collinear4).
  assert (Col A B P) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (~ Col Q B C).
  {
  intro.
  assert (Col C B Q) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA Q B C C B Q) by (conclude lemma_ABCequalsCBA).
 assert (CongA A B P C B Q) by (conclude lemma_equalanglestransitive).
 assert (Triangle C B Q) by (conclude_def Triangle ).
 assert (Cong B A B C) by (forward_using lemma_congruenceflip).
 assert (Cong B P B Q) by (forward_using lemma_congruenceflip).
 assert (Cong A P C Q) by (conclude proposition_04).
 close.
 }
(* cases *)
close.
Qed.

End Euclid.


