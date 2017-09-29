Require Export GeoCoq.Elements.OriginalProofs.proposition_23.
Require Export GeoCoq.Elements.OriginalProofs.proposition_11B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_Euclid4.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_9_5.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_23B : 
   forall A B C D E P, 
   neq A B -> nCol D C E -> nCol A B P ->
   exists X Y, Out A B Y /\ CongA X A Y D C E /\ TS X A B P.
Proof.
intros.
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists F G, (Out A B G /\ CongA F A G D C E)) by (conclude proposition_23);destruct Tf as [F[G]];spliter.
assert (neq A G) by (conclude lemma_raystrict).
assert (~ Col A B F).
 {
 intro.
 assert (CongA D C E F A G) by (conclude lemma_equalanglessymmetric).
 assert (nCol F A G) by (conclude lemma_equalanglesNC).
 assert (Col A B G) by (conclude lemma_rayimpliescollinear).
 assert (Col B F G) by (conclude lemma_collinear4).
 assert (Col B F A) by (forward_using lemma_collinearorder).
 assert (~ eq F B).
  {
  intro.
  assert (Out A F G) by (conclude cn_equalitysub).
  assert (Col A F G) by (conclude lemma_rayimpliescollinear).
  assert (Col F A G) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (neq B F) by (conclude lemma_inequalitysymmetric).
 assert (Col F A G) by (conclude lemma_collinear4).
 contradict.
 }
let Tf:=fresh in
rename_H;
assert (Tf:exists H, Perp_at F H A B H) by (conclude proposition_12);destruct Tf as [H];spliter.
let Tf:=fresh in
assert (Tf:exists J, (Col F H H /\ Col A B H /\ Col A B J /\ Per J H F)) by (conclude_def Perp_at );destruct Tf as [J];spliter.
assert (nCol J H F) by (conclude lemma_rightangleNC).
assert (~ eq F H).
 {
 intro.
 assert (Col A B F) by (conclude cn_equalitysub).
 contradict.
 }
assert (Per F H J) by (conclude lemma_8_2).
assert (nCol J H F) by (conclude lemma_rightangleNC).
assert (~ eq J H).
 {
 intro.
 assert (Col J H F) by (conclude_def Col ).
 contradict.
 }
assert (neq H J) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists T, (BetS J H T /\ Cong H T H J)) by (conclude postulate_extension);destruct Tf as [T];spliter.
assert (Col J H T) by (conclude_def Col ).
assert (Col B J H) by (conclude lemma_collinear4).
assert (neq J T) by (forward_using lemma_betweennotequal).
assert (Col H J B) by (forward_using lemma_collinearorder).
assert (Col H J T) by (forward_using lemma_collinearorder).
assert (neq J H) by (forward_using lemma_betweennotequal).
assert (neq H J) by (conclude lemma_inequalitysymmetric).
assert (Col J B T) by (conclude lemma_collinear4).
assert (Col J T B) by (forward_using lemma_collinearorder).
assert (Col B A J) by (forward_using lemma_collinearorder).
assert (Col B A H) by (forward_using lemma_collinearorder).
assert (Col A J H) by (conclude lemma_collinear4).
assert (Col H J A) by (forward_using lemma_collinearorder).
assert (Col J A T) by (conclude lemma_collinear4).
assert (Col J T A) by (forward_using lemma_collinearorder).
assert (~ Col J T P).
 {
 intro.
 assert (Col A B P) by (conclude lemma_collinear5).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists Q, (Per J H Q /\ TS Q J T P)) by (conclude proposition_11B);destruct Tf as [Q];spliter.
assert (nCol J H Q) by (conclude lemma_rightangleNC).
assert (~ eq H Q).
 {
 intro.
 assert (Col J H Q) by (conclude_def Col ).
 contradict.
 }
assert (~ eq H F).
 {
 intro.
 assert (Col J H F) by (conclude_def Col ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists S, (Out H Q S /\ Cong H S H F)) by (conclude lemma_layoff);destruct Tf as [S];spliter.
let Tf:=fresh in
assert (Tf:exists L, (BetS Q L P /\ Col J T L /\ nCol J T Q)) by (conclude_def TS );destruct Tf as [L];spliter.
assert (Col A B L) by (conclude lemma_collinear5).
assert (eq Q Q) by (conclude cn_equalityreflexive).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (eq S S) by (conclude cn_equalityreflexive).
assert (Out A G G) by (conclude lemma_ray4).
assert (neq D C) by (forward_using lemma_angledistinct).
assert (neq C D) by (conclude lemma_inequalitysymmetric).
assert (neq C E) by (forward_using lemma_angledistinct).
assert (Out C D D) by (conclude lemma_ray4).
assert (Out C E E) by (conclude lemma_ray4).
assert (Col J H A) by (forward_using lemma_collinearorder).
assert (Per J H S) by (conclude lemma_8_3).
assert (Per S H J) by (conclude lemma_8_2).
assert (CongA J H F J H S) by (conclude lemma_Euclid4).
assert (Out H F F) by (conclude lemma_ray4).
assert (Supp J H F F T) by (conclude_def Supp ).
assert (eq T T) by (conclude cn_equalityreflexive).
assert (eq S S) by (conclude cn_equalityreflexive).
assert (neq H S) by (forward_using lemma_angledistinct).
assert (Out H S S) by (conclude lemma_ray4).
assert (Supp J H S S T) by (conclude_def Supp ).
assert (CongA F H T S H T) by (conclude lemma_supplements).
assert (Col A H J) by (forward_using lemma_collinearorder).
assert (Supp J H F F T) by (conclude_def Supp ).
assert (Supp J H S S T) by (conclude_def Supp ).
assert (~ Col F A G).
 {
 intro.
 assert (Col A B G) by (conclude lemma_rayimpliescollinear).
 assert (Col G A B) by (forward_using lemma_collinearorder).
 assert (Col G A F) by (forward_using lemma_collinearorder).
 assert (neq G A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B F) by (conclude lemma_collinear4).
 contradict.
 }
assert ((eq A H \/ eq A J \/ eq H J \/ BetS H A J \/ BetS A H J \/ BetS A J H)) by (conclude_def Col ).
assert (CongA F A G S A G).
by cases on (eq A H \/ neq A H).
{
 assert (Per J A F) by (conclude cn_equalitysub).
 assert (Per J A S) by (conclude cn_equalitysub).
 assert (Col A B G) by (conclude lemma_rayimpliescollinear).
 assert (Col J H G) by (conclude lemma_collinear5).
 assert (Col J A G) by (conclude cn_equalitysub).
 assert (neq G A) by (conclude lemma_inequalitysymmetric).
 assert (Per G A F) by (conclude lemma_collinearright).
 assert (Per F A G) by (conclude lemma_8_2).
 assert (Per G A S) by (conclude lemma_collinearright).
 assert (Per S A G) by (conclude lemma_8_2).
 assert (CongA F A G S A G) by (conclude lemma_Euclid4).
 close.
 }
{
 assert (Cong A H A H) by (conclude cn_congruencereflexive).
 assert (Cong F H S H) by (forward_using lemma_doublereverse).
 assert (Per F H J) by (conclude lemma_8_2).
 assert (Per A H F) by (conclude lemma_collinearright).
 assert (Per F H A) by (conclude lemma_8_2).
 assert (Per J H S) by (conclude lemma_8_2).
 assert (Per A H S) by (conclude lemma_collinearright).
 assert (CongA A H F A H S) by (conclude lemma_Euclid4).
 assert (nCol F H A) by (conclude lemma_rightangleNC).
 assert (CongA F H A A H F) by (conclude lemma_ABCequalsCBA).
 assert (CongA F H A A H S) by (conclude lemma_equalanglestransitive).
 assert (nCol A H S) by (conclude lemma_rightangleNC).
 assert (CongA A H S S H A) by (conclude lemma_ABCequalsCBA).
 assert (CongA F H A S H A) by (conclude lemma_equalanglestransitive).
 assert (Cong H F H S) by (forward_using lemma_congruenceflip).
 assert (Cong H A H A) by (conclude cn_congruencereflexive).
 assert (nCol F H A) by (conclude lemma_rightangleNC).
 assert (Triangle F H A) by (conclude_def Triangle ).
 assert (~ Col S H A).
  {
  intro.
  assert (Col A H S) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Triangle S H A) by (conclude_def Triangle ).
 assert ((Cong F A S A /\ CongA H F A H S A /\ CongA H A F H A S)) by (conclude proposition_04).
 assert (~ Col F A H).
  {
  intro.
  assert (Col F H A) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA F A H H A F) by (conclude lemma_ABCequalsCBA).
 assert (~ Col H A S).
  {
  intro.
  assert (Col S H A) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA H A S S A H) by (conclude lemma_ABCequalsCBA).
 assert (CongA F A H H A S) by (conclude lemma_equalanglestransitive).
 assert (CongA F A H S A H) by (conclude lemma_equalanglestransitive).
 assert (Cong A F A S) by (forward_using lemma_congruenceflip).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col A B A) by (conclude_def Col ).
 assert (Col A B G) by (conclude lemma_rayimpliescollinear).
 assert (Col G H A).
 by cases on (eq G H \/ neq G H).
 {
  assert (Col G H A) by (conclude_def Col ).
  close.
  }
 {
  assert (Col G H A) by (conclude lemma_collinear5).
  close.
  }
(* cases *)
 assert (neq F A) by (forward_using lemma_angledistinct).
 assert (neq A F) by (conclude lemma_inequalitysymmetric).
 assert (Out A F F) by (conclude lemma_ray4).
 assert (neq S A) by (forward_using lemma_angledistinct).
 assert (neq A S) by (conclude lemma_inequalitysymmetric).
 assert (Out A S S) by (conclude lemma_ray4).
 assert ((eq G H \/ eq G A \/ eq H A \/ BetS H G A \/ BetS G H A \/ BetS G A H)) by (conclude_def Col ).
 assert (CongA F A G S A G).
 by cases on (eq G H \/ eq G A \/ eq H A \/ BetS H G A \/ BetS G H A \/ BetS G A H).
 {
  assert (~ ~ CongA F A G S A G).
   {
   intro.
   assert (CongA F A G S A G) by (conclude cn_equalitysub).
   contradict.
   }
  close.
  }
 {
  assert (~ ~ CongA F A G S A G).
   {
   intro.
   assert (neq A G) by (conclude lemma_raystrict).
   assert (neq G A) by (conclude lemma_inequalitysymmetric).
   contradict.
   }
  close.
  }
 {
  assert (~ ~ CongA F A G S A G).
   {
   intro.
   assert (neq H A) by (conclude lemma_inequalitysymmetric).
   contradict.
   }
  close.
  }
 {
  assert (BetS A G H) by (conclude axiom_betweennesssymmetry).
  assert (Out A H G) by (conclude lemma_ray4).
  assert (CongA F A H F A H) by (conclude lemma_equalanglesreflexive).
  assert (~ Col S A H).
   {
   intro.
   assert (Col S H A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (CongA S A H S A H) by (conclude lemma_equalanglesreflexive).
  assert (neq H A) by (forward_using lemma_betweennotequal).
  assert (neq A H) by (conclude lemma_inequalitysymmetric).
  assert (eq H H) by (conclude cn_equalityreflexive).
  assert (Out A H H) by (conclude lemma_ray4).
  assert (Out A G H) by (conclude lemma_ray4).
  assert (Cong A G A G) by (conclude cn_congruencereflexive).
  assert (CongA F A H F A G) by (conclude lemma_equalangleshelper).
  assert (CongA S A H S A G) by (conclude lemma_equalangleshelper).
  assert (CongA F A G F A H) by (conclude lemma_equalanglessymmetric).
  assert (CongA F A G S A H) by (conclude lemma_equalanglestransitive).
  assert (CongA F A G S A G) by (conclude lemma_equalanglestransitive).
  close.
  }
 {
  assert (BetS A H G) by (conclude axiom_betweennesssymmetry).
  assert (Out A H G) by (conclude lemma_ray4).
  assert (CongA F A H F A H) by (conclude lemma_equalanglesreflexive).
  assert (~ Col S A H).
   {
   intro.
   assert (Col S H A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (CongA S A H S A H) by (conclude lemma_equalanglesreflexive).
  assert (neq H A) by (forward_using lemma_betweennotequal).
  assert (neq A H) by (conclude lemma_inequalitysymmetric).
  assert (eq H H) by (conclude cn_equalityreflexive).
  assert (Out A H H) by (conclude lemma_ray4).
  assert (Out A G H) by (conclude lemma_ray4).
  assert (CongA F A H F A G) by (conclude lemma_equalangleshelper).
  assert (CongA S A H S A G) by (conclude lemma_equalangleshelper).
  assert (CongA F A G F A H) by (conclude lemma_equalanglessymmetric).
  assert (CongA F A G S A H) by (conclude lemma_equalanglestransitive).
  assert (CongA F A G S A G) by (conclude lemma_equalanglestransitive).
  close.
  }
 {
  assert (BetS H A G) by (conclude axiom_betweennesssymmetry).
  assert (Supp H A F F G) by (conclude_def Supp ).
  assert (Supp H A S S G) by (conclude_def Supp ).
  assert (CongA H A F H A S) by (conclude lemma_equalanglesflip).
  assert (CongA F A G S A G) by (conclude lemma_supplements).
  close.
  }
(* cases *)
 close.
 }
(* cases *)
assert (CongA S A G F A G) by (conclude lemma_equalanglessymmetric).
assert (CongA S A G D C E) by (conclude lemma_equalanglestransitive).
assert (Out H S Q) by (conclude lemma_ray5).
assert (Col J T H) by (forward_using lemma_collinearorder).
assert (Col Q L P) by (conclude_def Col ).
assert (TS S J T P) by (conclude lemma_9_5).
let Tf:=fresh in
assert (Tf:exists M, (BetS S M P /\ Col J T M /\ nCol J T S)) by (conclude_def TS );destruct Tf as [M];spliter.
assert (Col T A B) by (conclude lemma_collinear4).
assert (Col A B T) by (forward_using lemma_collinearorder).
assert (Col B A T) by (forward_using lemma_collinearorder).
assert (Col A J T) by (conclude lemma_collinear4).
assert (Col J T A) by (forward_using lemma_collinearorder).
assert (Col B J T) by (conclude lemma_collinear4).
assert (Col J T B) by (forward_using lemma_collinearorder).
assert (Col A B M) by (conclude lemma_collinear5).
assert (~ Col A B S).
 {
 intro.
 assert (Col J T S) by (conclude lemma_collinear5).
 contradict.
 }
assert (TS S A B P) by (conclude_def TS ).
close.
Qed.

End Euclid.


