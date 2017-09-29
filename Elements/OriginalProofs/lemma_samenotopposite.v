Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_samenotopposite : 
   forall A B C D, 
   OS A B C D ->
   ~ TS A C D B.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists p q r, (Col C D p /\ Col C D q /\ BetS A p r /\ BetS B q r /\ nCol C D A /\ nCol C D B)) by (conclude_def OS );destruct Tf as [p[q[r]]];spliter.
assert (OS B A C D) by (forward_using lemma_samesidesymmetric).
assert (~ TS A C D B).
 {
 intro.
 assert (TS B C D B) by (conclude lemma_planeseparation).
 let Tf:=fresh in
 assert (Tf:exists M, BetS B M B) by (conclude_def TS );destruct Tf as [M];spliter.
 assert (~ BetS B M B) by (conclude axiom_betweennessidentity).
 contradict.
 }
close.
Qed.

End Euclid.


