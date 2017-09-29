Require Export GeoCoq.Elements.OriginalProofs.lemma_pointreflectionisometry.

Section Euclid.

Context `{Ax:euclidean_neutral}.


Lemma lemma_rightreflection : 
   forall A B C E a b c, 
   Per A B C -> Midpoint A E a -> Midpoint B E b -> Midpoint C E c ->
   Per a b c.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists D, (BetS A B D /\ Cong A B D B /\ Cong A C D C /\ neq B C)) by (conclude_def Per );destruct Tf as [D];spliter.
assert (Cong A B a b) by (conclude lemma_pointreflectionisometry).
assert (Cong A C a c) by (conclude lemma_pointreflectionisometry).
assert (Cong B C b c) by (conclude lemma_pointreflectionisometry).
assert (Per a b c).
by cases on (eq D E \/ neq D E).
{
 assert (Cong B E E b) by (conclude_def Midpoint ).
 assert (Cong B D D b) by (conclude cn_equalitysub).
 assert (Cong B D b D) by (forward_using lemma_congruenceflip).
 assert (Cong C E E c) by (conclude_def Midpoint ).
 assert (Cong C D D c) by (conclude cn_equalitysub).
 assert (Cong D C D c) by (forward_using lemma_congruenceflip).
 assert (Cong A C D c) by (conclude lemma_congruencetransitive).
 assert (Cong a c A C) by (conclude lemma_congruencesymmetric).
 assert (Cong a c D c) by (conclude lemma_congruencetransitive).
 assert (Cong A E E a) by (conclude_def Midpoint ).
 assert (Cong A D D a) by (conclude cn_equalitysub).
 assert (Cong A D a D) by (forward_using lemma_congruenceflip).
 assert (Cong B E E b) by (conclude_def Midpoint ).
 assert (Cong B D D b) by (conclude cn_equalitysub).
 assert (Cong B D b D) by (forward_using lemma_congruenceflip).
 assert (Cong D B D b) by (forward_using lemma_congruenceflip).
 assert (BetS a b D) by (conclude lemma_betweennesspreserved).
 assert (Cong a b A B) by (conclude lemma_congruencesymmetric).
 assert (Cong a b D B) by (conclude lemma_congruencetransitive).
 assert (Cong a b D b) by (conclude lemma_congruencetransitive).
 assert (Cong a c A C) by (conclude lemma_congruencesymmetric).
 assert (Cong a c D C) by (conclude lemma_congruencetransitive).
 assert (Cong C E E c) by (conclude_def Midpoint ).
 assert (Cong C D D c) by (conclude cn_equalitysub).
 assert (Cong D C D c) by (forward_using lemma_congruenceflip).
 assert (Cong a c D c) by (conclude lemma_congruencetransitive).
 assert (neq b c) by (conclude lemma_nullsegment3).
 assert (Per a b c) by (conclude_def Per ).
 close.
 }
{
 let Tf:=fresh in
 assert (Tf:exists d, (BetS D E d /\ Cong E d D E)) by (conclude postulate_extension);destruct Tf as [d];spliter.
 assert (Cong E D d E) by (forward_using lemma_doublereverse).
 assert (Cong D E E d) by (forward_using lemma_congruenceflip).
 assert (Midpoint D E d) by (conclude_def Midpoint ).
 assert (Cong B D b d) by (conclude lemma_pointreflectionisometry).
 assert (Cong D C d c) by (conclude lemma_pointreflectionisometry).
 assert (Cong a c A C) by (conclude lemma_congruencesymmetric).
 assert (Cong a c D C) by (conclude lemma_congruencetransitive).
 assert (Cong a c d c) by (conclude lemma_congruencetransitive).
 assert (neq b c) by (conclude lemma_nullsegment3).
 assert (Cong A D a d) by (conclude lemma_pointreflectionisometry).
 assert (BetS a b d) by (conclude lemma_betweennesspreserved).
 assert (Cong a b A B) by (conclude lemma_congruencesymmetric).
 assert (Cong a b D B) by (conclude lemma_congruencetransitive).
 assert (Cong D B d b) by (conclude lemma_pointreflectionisometry).
 assert (Cong a b d b) by (conclude lemma_congruencetransitive).
 assert (Per a b c) by (conclude_def Per ).
 close.
 }
(* cases *)
close.
Qed.

End Euclid.


