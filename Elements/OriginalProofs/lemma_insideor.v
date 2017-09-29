Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_insideor : 
   forall A C J P Q, 
   CI J C P Q -> InCirc A J ->
   (eq A C \/ Lt C A P Q).
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists D E, (CI J C P Q /\ BetS D C E /\ Cong C E P Q /\ Cong C D P Q /\ BetS D A E)) by (conclude inside);destruct Tf as [D[E]];spliter.
assert ((eq A C \/ Lt C A P Q)).
by cases on (eq A C \/ neq A C).
{
 close.
 }
{
 assert (~ ~ Lt C A P Q).
  {
  intro.
  assert (~ BetS D A C).
   {
   intro.
   assert (BetS C A D) by (conclude axiom_betweennesssymmetry).
   assert (Cong C A C A) by (conclude cn_congruencereflexive).
   assert (Lt C A C D) by (conclude_def Lt ).
   assert (Lt C A P Q) by (conclude lemma_lessthancongruence).
   contradict.
   }
  assert (~ BetS D C A).
   {
   intro.
   assert (BetS C A E) by (conclude lemma_3_6a).
   assert (Cong C A C A) by (conclude cn_congruencereflexive).
   assert (Lt C A C E) by (conclude_def Lt ).
   assert (Lt C A P Q) by (conclude lemma_lessthancongruence).
   contradict.
   }
  assert (eq A C) by (conclude axiom_connectivity).
  contradict.
  }
 close.
 }
(* cases *)
close.
Qed.

End Euclid.


