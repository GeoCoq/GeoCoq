Require Export GeoCoq.Elements.OriginalProofs.proposition_03.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_angleorderrespectscongruence : 
   forall A B C D E F P Q R, 
   LtA A B C D E F -> CongA P Q R D E F ->
   LtA A B C P Q R.
Proof.
intros.
rename_H H;
let Tf:=fresh in
assert (Tf:exists G H J, (BetS G H J /\ Out E D G /\ Out E F J /\ CongA A B C D E H)) by (conclude_def LtA );destruct Tf as [G[H[J]]];spliter.
assert (nCol D E F) by (conclude lemma_equalanglesNC).
assert ((neq P Q /\ neq Q R /\ neq P R /\ neq D E /\ neq E F /\ neq D F)) by (forward_using lemma_angledistinct).
assert (neq Q P) by (conclude lemma_inequalitysymmetric).
assert ((neq A B /\ neq B C /\ neq A C /\ neq D E /\ neq E H /\ neq D H)) by (forward_using lemma_angledistinct).
assert (neq E G) by (conclude lemma_raystrict).
let Tf:=fresh in
assert (Tf:exists U, (Out Q P U /\ Cong Q U E G)) by (conclude lemma_layoff);destruct Tf as [U];spliter.
assert (neq E J) by (conclude lemma_raystrict).
let Tf:=fresh in
assert (Tf:exists V, (Out Q R V /\ Cong Q V E J)) by (conclude lemma_layoff);destruct Tf as [V];spliter.
assert (Cong G H G H) by (conclude cn_congruencereflexive).
assert (Lt G H G J) by (conclude_def Lt ).
assert (nCol A B C) by (conclude_def CongA ).
assert (nCol D E H) by (conclude lemma_equalanglesNC).
assert (CongA D E F P Q R) by (conclude lemma_equalanglessymmetric).
assert (CongA D E F U Q V) by (conclude lemma_equalangleshelper).
assert (CongA U Q V D E F) by (conclude lemma_equalanglessymmetric).
assert (CongA U Q V G E J) by (conclude lemma_equalangleshelper).
assert (CongA G E J U Q V) by (conclude lemma_equalanglessymmetric).
assert (~ Col G E J).
 {
 intro.
 assert (Col E G J) by (forward_using lemma_collinearorder).
 assert (neq E G) by (conclude lemma_raystrict).
 assert (Out E G D) by (conclude lemma_ray5).
 assert (Col E G D) by (conclude lemma_rayimpliescollinear).
 assert (Col G J D) by (conclude lemma_collinear4).
 assert (Col G D J) by (forward_using lemma_collinearorder).
 assert (Col G D E) by (forward_using lemma_collinearorder).
 assert (Col G J E) by (forward_using lemma_collinearorder).
 assert (Col D J E).
 by cases on (eq G D \/ neq G D).
 {
  assert (Col D J E) by (conclude cn_equalitysub).
  close.
  }
 {
  assert (Col D J E) by (conclude lemma_collinear4).
  close.
  }
(* cases *)
 assert (Col J E D) by (forward_using lemma_collinearorder).
 assert (Col E F J) by (conclude lemma_rayimpliescollinear).
 assert (Col J E F) by (forward_using lemma_collinearorder).
 assert (neq E J) by (conclude lemma_raystrict).
 assert (neq J E) by (conclude lemma_inequalitysymmetric).
 assert (Col E D F) by (conclude lemma_collinear4).
 assert (Col D E F) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle G E J) by (conclude_def Triangle ).
assert (nCol U Q V) by (conclude lemma_equalanglesNC).
assert (Triangle U Q V) by (conclude_def Triangle ).
assert (Cong E G Q U) by (conclude lemma_congruencesymmetric).
assert (Cong E J Q V) by (conclude lemma_congruencesymmetric).
assert ((Cong G J U V /\ CongA E G J Q U V /\ CongA E J G Q V U)) by (conclude proposition_04).
assert (Cong U V G J) by (conclude lemma_congruencesymmetric).
assert (neq G H) by (forward_using lemma_betweennotequal).
assert (neq G J) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists W, (BetS U W V /\ Cong U W G H)) by (conclude proposition_03);destruct Tf as [W];spliter.
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Out E H H) by (conclude lemma_ray4).
assert (CongA A B C G E H) by (conclude lemma_equalangleshelper).
assert (nCol G E H) by (conclude lemma_equalanglesNC).
assert (~ Col G H E).
 {
 intro.
 assert (Col G E H) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle G H E) by (conclude_def Triangle ).
assert (Out G H J) by (conclude lemma_ray4).
assert (neq U V) by (forward_using lemma_betweennotequal).
assert (Out U V W) by (conclude lemma_ray4).
assert (eq Q Q) by (conclude cn_equalityreflexive).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (~ eq U Q).
 {
 intro.
 assert (Col U Q V) by (conclude_def Col ).
 contradict.
 }
assert (Out U Q Q) by (conclude lemma_ray4).
assert (~ eq G E).
 {
 intro.
 assert (Col G H E) by (conclude_def Col ).
 contradict.
 }
assert (Out G E E) by (conclude lemma_ray4).
assert (CongA E G J Q U W) by (conclude lemma_equalangleshelper).
assert (CongA Q U W E G J) by (conclude lemma_equalanglessymmetric).
assert (Out G J H) by (conclude lemma_ray4).
assert (CongA Q U W E G H) by (conclude lemma_equalangleshelper).
assert (CongA E G H Q U W) by (conclude lemma_equalanglessymmetric).
assert (nCol Q U W) by (conclude lemma_equalanglesNC).
assert (~ Col U W Q).
 {
 intro.
 assert (Col Q U W) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle U W Q) by (conclude_def Triangle ).
assert (~ Col H G E).
 {
 intro.
 assert (Col G H E) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle H G E) by (conclude_def Triangle ).
assert (~ Col W U Q).
 {
 intro.
 assert (Col U W Q) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle W U Q) by (conclude_def Triangle ).
assert (Cong G H U W) by (conclude lemma_congruencesymmetric).
assert (Cong G E U Q) by (forward_using lemma_congruenceflip).
assert (CongA E G H Q U W) by (conclude lemma_equalanglessymmetric).
assert (CongA Q U W W U Q) by (conclude lemma_ABCequalsCBA).
assert (CongA E G H W U Q) by (conclude lemma_equalanglestransitive).
assert (CongA H G E E G H) by (conclude lemma_ABCequalsCBA).
assert (CongA H G E W U Q) by (conclude lemma_equalanglestransitive).
assert ((Cong H E W Q /\ CongA G H E U W Q /\ CongA G E H U Q W)) by (conclude proposition_04).
assert (CongA A B C U Q W) by (conclude lemma_equalanglestransitive).
assert (eq W W) by (conclude cn_equalityreflexive).
assert (~ eq Q W).
 {
 intro.
 assert (Col Q U W) by (conclude_def Col ).
 assert (Col W U Q) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out Q W W) by (conclude lemma_ray4).
assert (Out Q U P) by (conclude lemma_ray5).
assert (CongA A B C P Q W) by (conclude lemma_equalangleshelper).
assert (LtA A B C P Q R) by (conclude_def LtA ).
close.
Qed.

End Euclid.


