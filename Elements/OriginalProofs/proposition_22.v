Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthannotequal.
Require Export GeoCoq.Elements.OriginalProofs.lemma_together.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray5.
Require Export GeoCoq.Elements.OriginalProofs.lemma_subtractequals.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray3.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_togethera
     : forall A B C D F G P Q a b c : Point,
       TG A a B b C c ->
       Cong D F A a ->
       Cong F G B b ->
       BetS D F G ->
       Cong P Q C c -> Lt P Q D G.
Proof.
intros.
apply (lemma_together A B C D F G P Q a b c);auto.
Qed.

Lemma proposition_22 : 
   forall A B C E F a b c, 
   TG A a B b C c -> TG A a C c B b -> TG B b C c A a -> neq F E ->
   exists X Y, Cong F X B b /\ Cong F Y A a /\ Cong X Y C c /\ Out F E X /\ Triangle F X Y.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists P, (BetS A a P /\ Cong a P B b /\ Lt C c A P)) by (conclude_def TG );destruct Tf as [P];spliter.
assert (neq A a) by (forward_using lemma_betweennotequal).
assert (neq a P) by (forward_using lemma_betweennotequal).
assert (neq B b) by (conclude lemma_nullsegment3).
assert (neq C c) by (forward_using lemma_lessthannotequal).
let Tf:=fresh in
assert (Tf:exists G, (Out F E G /\ Cong F G B b)) by (conclude lemma_layoff);destruct Tf as [G];spliter.
assert (Cong B b F G) by (conclude lemma_congruencesymmetric).
assert (neq F G) by (conclude lemma_nullsegment3).
assert (neq G F) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
rename_H;
assert (Tf:exists H, (BetS F G H /\ Cong G H C c)) by (conclude postulate_extension);destruct Tf as [H];spliter.
let Tf:=fresh in
assert (Tf:exists D, (BetS G F D /\ Cong F D A a)) by (conclude postulate_extension);destruct Tf as [D];spliter.
assert (Cong D F A a) by (forward_using lemma_congruenceflip).
assert (BetS D F G) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists L, CI L F A a) by (conclude circle);destruct Tf as [L];spliter.
let Tf:=fresh in
assert (Tf:exists R, CI R G C c) by (conclude circle);destruct Tf as [R];spliter.
assert ((CI R G C c /\ OnCirc H R)) by (conclude on).
assert (Lt D F F H) by (conclude lemma_together).
let Tf:=fresh in
assert (Tf:exists M, (BetS F M H /\ Cong F M D F)) by (conclude_def Lt );destruct Tf as [M];spliter.
assert (Cong F M A a) by (conclude lemma_congruencetransitive).
assert ((CI L F A a /\ OutCirc H L)) by (conclude outside).
assert (Cong C c C c) by (conclude cn_congruencereflexive).
assert (Lt C c D G) by (conclude lemma_togethera).
assert (Cong D G G D) by (conclude cn_equalityreverse).
assert (Lt C c G D) by (conclude lemma_lessthancongruence).
let Tf:=fresh in
assert (Tf:exists N, (BetS G N D /\ Cong G N C c)) by (conclude_def Lt );destruct Tf as [N];spliter.
assert ((CI R G C c /\ OnCirc H R)) by (conclude on).
assert (BetS D F H) by (conclude lemma_3_7b).
assert (BetS D F M) by (conclude axiom_innertransitivity).
assert (Cong F D A a) by (forward_using lemma_congruenceflip).
assert (BetS D N G) by (conclude axiom_betweennesssymmetry).
assert (neq F M) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists J, (BetS F M J /\ Cong M J C c)) by (conclude postulate_extension);destruct Tf as [J];spliter.
assert (BetS D F J) by (conclude lemma_3_7b).
assert ((Lt F G F J /\ neq A a /\ neq C c /\ neq B b)) by (conclude lemma_together).
let Tf:=fresh in
assert (Tf:exists Q, (BetS F Q J /\ Cong F Q F G)) by (conclude_def Lt );destruct Tf as [Q];spliter.
assert (neq F J) by (forward_using lemma_betweennotequal).
assert (Out F J Q) by (conclude lemma_ray4).
assert (Out F G J) by (conclude_def Out ).
assert (Out F J G) by (conclude lemma_ray5).
assert (eq Q G) by (conclude lemma_layoffunique).
assert (eq G Q) by (conclude lemma_equalitysymmetric).
assert (BetS F G J) by (conclude cn_equalitysub).
assert (BetS D G J) by (conclude lemma_3_7a).
assert (Cong C c M J) by (conclude lemma_congruencesymmetric).
assert (Cong G N M J) by (conclude lemma_congruencetransitive).
assert (Cong N G M J) by (forward_using lemma_congruenceflip).
assert (BetS D M J) by (conclude lemma_3_7a).
assert (BetS D N J) by (conclude lemma_3_6b).
assert (BetS D N M) by (conclude lemma_subtractequals).
assert (Cong C c G N) by (conclude lemma_congruencesymmetric).
assert (Lt G N D G) by (conclude lemma_lessthancongruence2).
assert (neq N G) by (forward_using lemma_betweennotequal).
assert (neq G N) by (conclude lemma_inequalitysymmetric).
assert (neq F G) by (forward_using lemma_betweennotequal).
assert (neq G F) by (conclude lemma_inequalitysymmetric).
assert (Out G N D) by (conclude lemma_ray4).
assert (Out G F D) by (conclude lemma_ray4).
assert (Out G D N) by (conclude lemma_ray5).
assert (Out G D F) by (conclude lemma_ray5).
assert (Out G F N) by (conclude lemma_ray3).
assert (~ (~ BetS F M G /\ neq M G /\ ~ BetS F G M)).
 {
 intro.
 assert (eq M G) by (conclude axiom_connectivity).
 contradict.
 }
assert (neq F M) by (forward_using lemma_betweennotequal).
assert (Out F G M) by (conclude lemma_ray4).
assert (Out F M G) by (conclude lemma_ray5).
assert (neq D M) by (forward_using lemma_betweennotequal).
assert (neq M D) by (conclude lemma_inequalitysymmetric).
assert ((CI L F A a /\ InCirc N L)) by (conclude inside).
assert ((CI R G C c /\ OnCirc N R)) by (conclude on).
let Tf:=fresh in
assert (Tf:exists K, (OnCirc K L /\ OnCirc K R)) by (conclude postulate_circle_circle);destruct Tf as [K];spliter.
assert (Cong F K A a) by (conclude on).
assert (Cong G K C c) by (conclude on).
assert (~ Col F G K).
 {
 intro.
 assert ((eq F G \/ eq F K \/ eq G K \/ BetS G F K \/ BetS F G K \/ BetS F K G)) by (conclude_def Col ).
 assert (nCol F G K).
 by cases on (eq F G \/ eq F K \/ eq G K \/ BetS G F K \/ BetS F G K \/ BetS F K G).
 {
  assert (~ Col F G K).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (Cong A a F K) by (conclude lemma_congruencesymmetric).
  assert (~ Col F G K).
   {
   intro.
   assert (neq F K) by (conclude lemma_nullsegment3).
   contradict.
   }
  close.
  }
 {
  assert (Cong C c G K) by (conclude lemma_congruencesymmetric).
  assert (neq G K) by (conclude lemma_nullsegment3).
  assert (~ Col F G K).
   {
   intro.
   assert (neq G K) by (conclude lemma_nullsegment3).
   contradict.
   }
  close.
  }
 {
  assert (BetS K F G) by (conclude axiom_betweennesssymmetry).
  assert (Cong K F A a) by (forward_using lemma_congruenceflip).
  let Tf:=fresh in
  assert (Tf:exists S, (BetS A a S /\ Cong a S B b /\ Lt C c A S)) by (conclude_def TG );destruct Tf as [S];spliter.
  assert (Cong A a A a) by (conclude cn_congruencereflexive).
  assert (Cong A a K F) by (conclude lemma_congruencesymmetric).
  assert (Cong a S F G) by (conclude lemma_congruencetransitive).
  assert (Cong A S K G) by (conclude lemma_sumofparts).
  assert (Cong A S G K) by (forward_using lemma_congruenceflip).
  assert (Lt C c G K) by (conclude lemma_lessthancongruence).
  assert (Cong C c G K) by (conclude lemma_congruencesymmetric).
  assert (Lt G K G K) by (conclude lemma_lessthancongruence2).
  assert (~ Col F G K).
   {
   intro.
   assert (~ Lt G K G K) by (conclude lemma_trichotomy2).
   contradict.
   }
  close.
  }
 {
  let Tf:=fresh in
  assert (Tf:exists S, (BetS B b S /\ Cong b S C c /\ Lt A a B S)) by (conclude_def TG );destruct Tf as [S];spliter.
  assert (Cong C c b S) by (conclude lemma_congruencesymmetric).
  assert (Cong G K b S) by (conclude lemma_congruencetransitive).
  assert (Cong F K B S) by (conclude lemma_sumofparts).
  assert (Cong A a F K) by (conclude lemma_congruencesymmetric).
  assert (Lt F K B S) by (conclude lemma_lessthancongruence2).
  assert (Cong B S F K) by (conclude lemma_congruencesymmetric).
  assert (Lt F K F K) by (conclude lemma_lessthancongruence).
  assert (~ Col F G K).
   {
   intro.
   assert (~ Lt F K F K) by (conclude lemma_trichotomy2).
   contradict.
   }
  close.
  }
 {
  let Tf:=fresh in
  assert (Tf:exists S, (BetS A a S /\ Cong a S C c /\ Lt B b A S)) by (conclude_def TG );destruct Tf as [S];spliter.
  assert (Lt F G A S) by (conclude lemma_lessthancongruence2).
  assert (Cong C c a S) by (conclude lemma_congruencesymmetric).
  assert (Cong G K a S) by (conclude lemma_congruencetransitive).
  assert (Cong K G a S) by (forward_using lemma_congruenceflip).
  assert (Cong F G A S) by (conclude lemma_sumofparts).
  assert (Cong A S F G) by (conclude lemma_congruencesymmetric).
  assert (Lt F G F G) by (conclude lemma_lessthancongruence).
  assert (~ Col F G K).
   {
   intro.
   assert (~ Lt F G F G) by (conclude lemma_trichotomy2).
   contradict.
   }
  close.
  }
(* cases *)
 contradict.
 }
assert (Triangle F G K) by (conclude_def Triangle ).
close.
Qed.

End Euclid.


