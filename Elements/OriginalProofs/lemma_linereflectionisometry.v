Require Export GeoCoq.Elements.OriginalProofs.proposition_10.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rightreverse.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearright.
Require Export GeoCoq.Elements.OriginalProofs.lemma_pointreflectionisometry.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_linereflectionisometry : 
   forall A B C D E F, 
   Per B A C -> Per A B D -> BetS C A E -> BetS D B F -> Cong A C A E -> Cong B D B F ->
   Cong C D E F.
Proof.
intros.
let Tf:=fresh in
rename_H;
assert (Tf:exists H, (BetS B A H /\ Cong B A H A /\ Cong B C H C /\ neq A C)) by (conclude_def Per );destruct Tf as [H];spliter.
let Tf:=fresh in
assert (Tf:exists G, (BetS A B G /\ Cong A B G B /\ Cong A D G D /\ neq B D)) by (conclude_def Per );destruct Tf as [G];spliter.
assert (neq A B) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M B /\ Cong M A M B)) by (conclude proposition_10);destruct Tf as [M];spliter.
assert (Per D B A) by (conclude lemma_8_2).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (BetS B M A) by (conclude axiom_betweennesssymmetry).
assert (Out B A M) by (conclude lemma_ray4).
assert (Per D B M) by (conclude lemma_8_3).
assert (nCol D B M) by (conclude lemma_rightangleNC).
assert (~ eq D M).
 {
 intro.
 assert (Col D B M) by (conclude_def Col ).
 contradict.
 }
assert (neq M D) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists R, (BetS D M R /\ Cong M R M D)) by (conclude postulate_extension);destruct Tf as [R];spliter.
assert (BetS B M A) by (conclude axiom_betweennesssymmetry).
assert (Cong D B B F) by (forward_using lemma_congruenceflip).
assert (Cong D A F A) by (conclude lemma_rightreverse).
assert (Cong F A D A) by (conclude lemma_congruencesymmetric).
assert (Col D B F) by (conclude_def Col ).
assert (Col B D F) by (forward_using lemma_collinearorder).
assert (neq B F) by (forward_using lemma_betweennotequal).
assert (neq F B) by (conclude lemma_inequalitysymmetric).
assert (Per D B A) by (conclude lemma_8_2).
assert (Per F B A) by (conclude lemma_collinearright).
assert (Per F B M) by (conclude lemma_8_3).
assert (nCol F B M) by (conclude lemma_rightangleNC).
assert (nCol D B M) by (conclude lemma_rightangleNC).
assert (~ eq F M).
 {
 intro.
 assert (Col F B M) by (conclude_def Col ).
 contradict.
 }
assert (neq M F) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists Q, (BetS F M Q /\ Cong M Q M F)) by (conclude postulate_extension);destruct Tf as [Q];spliter.
assert (Cong M D M R) by (conclude lemma_congruencesymmetric).
assert (Cong D M M R) by (forward_using lemma_congruenceflip).
assert (Midpoint D M R) by (conclude_def Midpoint ).
assert (Cong M F M Q) by (conclude lemma_congruencesymmetric).
assert (Cong F M M Q) by (forward_using lemma_congruenceflip).
assert (Midpoint F M Q) by (conclude_def Midpoint ).
assert (Cong M B M A) by (conclude lemma_congruencesymmetric).
assert (Cong B M M A) by (forward_using lemma_congruenceflip).
assert (BetS B M A) by (conclude axiom_betweennesssymmetry).
assert (Midpoint B M A) by (conclude_def Midpoint ).
assert (~ Col D M B).
 {
 intro.
 assert (Col D B M) by (forward_using lemma_collinearorder).
 assert (Col D B F) by (conclude_def Col ).
 assert (neq D B) by (forward_using lemma_betweennotequal).
 assert (Col B M F) by (conclude lemma_collinear4).
 assert (Col F B M) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Cong D B R A) by (conclude lemma_pointreflectionisometry).
assert (~ Col F M B).
 {
 intro.
 assert (Col F B M) by (forward_using lemma_collinearorder).
 assert (Col D B F) by (conclude_def Col ).
 assert (Col F B D) by (forward_using lemma_collinearorder).
 assert (neq B F) by (forward_using lemma_betweennotequal).
 assert (neq F B) by (conclude lemma_inequalitysymmetric).
 assert (Col B M D) by (conclude lemma_collinear4).
 assert (Col D B M) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Cong F B Q A) by (conclude lemma_pointreflectionisometry).
assert (Cong B F F B) by (conclude cn_equalityreverse).
assert (Cong B D F B) by (conclude lemma_congruencetransitive).
assert (Cong B D Q A) by (conclude lemma_congruencetransitive).
assert (Cong R A D B) by (conclude lemma_congruencesymmetric).
assert (Cong R A B D) by (forward_using lemma_congruenceflip).
assert (Cong R A Q A) by (conclude lemma_congruencetransitive).
assert (Per C A B) by (conclude lemma_8_2).
assert (Out A B M) by (conclude lemma_ray4).
assert (Per C A M) by (conclude lemma_8_3).
assert (Cong C A A E) by (forward_using lemma_congruenceflip).
assert (Cong C M E M) by (conclude lemma_rightreverse).
assert (nCol C A M) by (conclude lemma_rightangleNC).
assert (~ eq C M).
 {
 intro.
 assert (Col C A M) by (conclude_def Col ).
 contradict.
 }
assert (BetS Q M F) by (conclude axiom_betweennesssymmetry).
assert (BetS R M D) by (conclude axiom_betweennesssymmetry).
assert (Cong D B B F) by (forward_using lemma_congruenceflip).
assert (Cong D M F M) by (conclude lemma_rightreverse).
assert (Cong F M D M) by (conclude lemma_congruencesymmetric).
assert (Cong F M M Q) by (forward_using lemma_congruenceflip).
assert (Cong M Q F M) by (conclude lemma_congruencesymmetric).
assert (Cong Q M F M) by (forward_using lemma_congruenceflip).
assert (Cong Q M D M) by (conclude lemma_congruencetransitive).
assert (Cong Q M M R) by (conclude lemma_congruencetransitive).
assert (Cong Q M R M) by (forward_using lemma_congruenceflip).
assert (Cong M F M D) by (forward_using lemma_congruenceflip).
assert (Cong C A A E) by (forward_using lemma_congruenceflip).
assert (Cong C M E M) by (conclude lemma_rightreverse).
assert (Cong E M C M) by (conclude lemma_congruencesymmetric).
assert (Cong M E M C) by (forward_using lemma_congruenceflip).
assert (Midpoint C A E) by (conclude_def Midpoint ).
assert (Midpoint D M R) by (conclude_def Midpoint ).
assert (Midpoint F M Q) by (conclude_def Midpoint ).
assert (Cong M B M A) by (conclude lemma_congruencesymmetric).
assert (Cong B M M A) by (forward_using lemma_congruenceflip).
assert (Midpoint B M A) by (conclude_def Midpoint ).
assert (Cong F B Q A) by (conclude lemma_pointreflectionisometry).
assert (Cong D B R A) by (conclude lemma_pointreflectionisometry).
assert (Cong Q A F B) by (conclude lemma_congruencesymmetric).
assert (Cong B F D B) by (conclude lemma_congruencesymmetric).
assert (Cong F B D B) by (forward_using lemma_congruenceflip).
assert (Cong Q A D B) by (conclude lemma_congruencetransitive).
assert (Cong Q A R A) by (conclude lemma_congruencetransitive).
assert (Cong Q A A R) by (forward_using lemma_congruenceflip).
assert (~ Col D M F).
 {
 intro.
 assert (Col D B F) by (conclude_def Col ).
 assert (Col F D B) by (forward_using lemma_collinearorder).
 assert (Col F D M) by (forward_using lemma_collinearorder).
 assert (neq D F) by (forward_using lemma_betweennotequal).
 assert (neq F D) by (conclude lemma_inequalitysymmetric).
 assert (Col D B M) by (conclude lemma_collinear4).
 contradict.
 }
assert (Cong D F R Q) by (conclude lemma_pointreflectionisometry).
assert (Cong F D Q R) by (forward_using lemma_congruenceflip).
assert (BetS F B D) by (conclude axiom_betweennesssymmetry).
assert (Cong B D A R) by (forward_using lemma_congruenceflip).
assert (BetS Q A R) by (conclude lemma_betweennesspreserved).
assert (Midpoint Q A R) by (conclude_def Midpoint ).
assert (Cong E A A C) by (forward_using lemma_doublereverse).
assert (BetS E A C) by (conclude axiom_betweennesssymmetry).
assert (Midpoint E A C) by (conclude_def Midpoint ).
assert (Cong E Q C R) by (conclude lemma_pointreflectionisometry).
assert (Cong Q E R C) by (forward_using lemma_congruenceflip).
assert (neq Q M) by (forward_using lemma_betweennotequal).
assert (Cong E F C D) by (conclude axiom_5_line).
assert (Cong C D E F) by (conclude lemma_congruencesymmetric).
close.
Qed.

End Euclid.


