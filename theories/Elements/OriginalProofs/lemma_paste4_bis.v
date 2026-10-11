Require Export GeoCoq.Elements.OriginalProofs.proposition_35_bis.
Require Export GeoCoq.Elements.OriginalProofs.lemma_paste4_rectangles.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelfacts.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectangleonbase.
Require Export GeoCoq.Elements.OriginalProofs.proposition_30.
Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.
Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesidesymmetric.

Section Euclid.

Context `{Ax : euclidean_euclidean}.

Existing Instance area_follows_Euclid.

Lemma lemma_paste4_bis :
   forall A B C D F G H J K L M P e m,
   EF A B m D F K H G -> EF D B e C G H M L ->
   BetS A P C -> BetS B P D -> BetS K H M -> BetS F G L ->
   BetS B m D -> BetS B e C -> BetS F J M -> BetS K J L ->
   nCol A B D -> nCol C B D -> PG F K H G -> PG G H M L ->
   EF A B C D F K M L.
Proof.
intros A B C D F G H J K L M P e m.
intros.
assert ((Par F K H G /\ Par F G K H)) by (conclude_def PG ).
assert ((Par G H M L /\ Par G L H M)) by (conclude_def PG ).
assert (nCol F G K) by (forward_using lemma_parallelNC).
assert (nCol F K H) by (forward_using lemma_parallelNC).
assert (nCol G H M) by (forward_using lemma_parallelNC).
assert (nCol G L H) by (forward_using lemma_parallelNC).
assert (neq F K) by (forward_using lemma_NCdistinct).
assert (neq K F) by (conclude lemma_inequalitysymmetric).
assert (neq K H) by (forward_using lemma_NCdistinct).
assert (neq H K) by (conclude lemma_inequalitysymmetric).
assert (neq G H) by (forward_using lemma_NCdistinct).
assert (neq H G) by (conclude lemma_inequalitysymmetric).
assert (neq H M) by (forward_using lemma_NCdistinct).
assert (neq M H) by (conclude lemma_inequalitysymmetric).
assert (neq F L) by (forward_using lemma_betweennotequal).
assert (neq K M) by (forward_using lemma_betweennotequal).
assert (neq G L) by (forward_using lemma_betweennotequal).
assert (nCol L H M) by (forward_using lemma_parallelNC).
assert (neq L M) by (forward_using lemma_NCdistinct).
assert (neq M L) by (conclude lemma_inequalitysymmetric).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (eq K K) by (conclude cn_equalityreflexive).
assert (eq L L) by (conclude cn_equalityreflexive).
assert (eq M M) by (conclude cn_equalityreflexive).
assert (Col F G L) by (conclude_def Col ).
assert (Col F L G) by (forward_using lemma_collinearorder).
assert (Col F G F) by (conclude_def Col ).
assert (Col F L F) by (conclude_def Col ).
assert (Col F L L) by (conclude_def Col ).
assert (Col K H M) by (conclude_def Col ).
assert (Col K H K) by (conclude_def Col ).
assert (Col K H H) by (conclude_def Col ).
assert (Par K H F G) by (conclude lemma_parallelsymmetric).
assert (Par K H F L) by (conclude lemma_collinearparallel2).
assert (Par F L K H) by (conclude lemma_parallelsymmetric).
assert (Par F L K M) by (conclude lemma_collinearparallel2).
assert (Par F L H M) by (conclude lemma_collinearparallel2).
assert (Par K F H G) by (forward_using lemma_parallelflip).
assert (Par M L G H) by (conclude lemma_parallelsymmetric).
assert (Par M L H G) by (forward_using lemma_parallelflip).
assert (Col K F F) by (conclude_def Col ).
assert (Col H G G) by (conclude_def Col ).
assert (Col M L L) by (conclude_def Col ).
assert (Par K F M L) by (apply (proposition_30 K F M L H G F G L); assumption).
assert (Par F K M L) by (forward_using lemma_parallelflip).
assert (Par F L M K) by (forward_using lemma_parallelflip).
assert (Par F K L M) by (forward_using lemma_parallelflip).
assert (PG F K M L) by (conclude_def PG ).
let Tf:=fresh in
assert (Tf:exists F' G', (RE F' G' H K /\ Col F L F' /\ Col F L G')) by (conclude lemma_rectangleonbase);destruct Tf as [F'[G']];spliter.
let Tf:=fresh in
assert (Tf:exists G2 L', (RE G2 L' M H /\ Col F L G2 /\ Col F L L')) by (conclude lemma_rectangleonbase);destruct Tf as [G2[L']];spliter.
assert ((Per K F' G' /\ Per F' G' H /\ Per G' H K /\ Per H K F' /\ CR F' H G' K)) by (conclude_def RE ).
assert ((Per H G2 L' /\ Per G2 L' M /\ Per L' M H /\ Per M H G2 /\ CR G2 M L' H)) by (conclude_def RE ).
assert (Per K H G') by (conclude lemma_8_2).
assert (Col M H K) by (forward_using lemma_collinearorder).
assert (Per K H G2) by (conclude lemma_collinearright).
assert (eq G2 G') by (apply (lemma_perpunique K H F L G2 G'); assumption).
assert (RE G' L' M H) by (conclude cn_equalitysub).
assert (PG F' G' H K) by (conclude lemma_rectangleparallelogram).
assert (PG G' L' M H) by (conclude lemma_rectangleparallelogram).
assert ((Par F' G' H K /\ Par F' K G' H)) by (conclude_def PG ).
assert ((Par G' L' M H /\ Par G' H L' M)) by (conclude_def PG ).
assert (nCol F' K G') by (forward_using lemma_parallelNC).
assert (neq F' K) by (forward_using lemma_NCdistinct).
assert (neq K F') by (conclude lemma_inequalitysymmetric).
assert (nCol G' H L') by (forward_using lemma_parallelNC).
assert (neq G' H) by (forward_using lemma_NCdistinct).
assert (neq H G') by (conclude lemma_inequalitysymmetric).
assert (nCol G' L' M) by (forward_using lemma_parallelNC).
assert (neq L' M) by (forward_using lemma_NCdistinct).
assert (neq M L') by (conclude lemma_inequalitysymmetric).
assert (Par G' H F' K) by (conclude lemma_parallelsymmetric).
assert (TP G' H F' K) by (conclude lemma_paralleldef2B).
assert (OS F' K G' H) by (conclude_def TP ).
assert (TP G' H L' M) by (conclude lemma_paralleldef2B).
assert (OS L' M G' H) by (conclude_def TP ).
assert (nCol G' H K) by (forward_using lemma_parallelNC).
assert (Col G' H H) by (conclude_def Col ).
assert (TS K G' H M) by (conclude_def TS ).
assert (TS F' G' H M) by (conclude lemma_planeseparation).
assert (TS M G' H F') by (conclude lemma_oppositesidesymmetric).
assert (TS L' G' H F') by (conclude lemma_planeseparation).
assert (TS F' G' H L') by (conclude lemma_oppositesidesymmetric).
let Tf:=fresh in
assert (Tf:exists X, (BetS F' X L' /\ Col G' H X /\ nCol G' H F')) by (conclude_def TS );destruct Tf as [X];spliter.
assert (neq F' L') by (forward_using lemma_betweennotequal).
assert (Col F' X L') by (conclude_def Col ).
assert (Col F' L' X) by (forward_using lemma_collinearorder).
assert (Col F' L' G') by (conclude lemma_collinear5).
assert (Col H G' X) by (forward_using lemma_collinearorder).
assert (eq G' G') by (conclude cn_equalityreflexive).
assert (Col H G' G') by (conclude_def Col ).
assert (Par K H F' L') by (apply (lemma_collinearparallel2 K H F L F' L'); assumption).
assert (Par F' L' K H) by (conclude lemma_parallelsymmetric).
assert (nCol F' L' H) by (forward_using lemma_parallelNC).
assert (eq X G') by (apply (lemma_intersectionunique F' L' H G' X G'); assumption).
assert (BetS F' G' L') by (conclude cn_equalitysub).
assert (Par K M F L) by (conclude lemma_parallelsymmetric).
assert (Par K M F' L') by (apply (lemma_collinearparallel2 K M F L F' L'); assumption).
assert (Par F' L' K M) by (conclude lemma_parallelsymmetric).
assert (Par F' L' M K) by (forward_using lemma_parallelflip).
assert (Par K F' H G') by (forward_using lemma_parallelflip).
assert (Par L' M G' H) by (conclude lemma_parallelsymmetric).
assert (Par M L' H G') by (forward_using lemma_parallelflip).
assert (eq F' F') by (conclude cn_equalityreflexive).
assert (eq L' L') by (conclude cn_equalityreflexive).
assert (Col K F' F') by (conclude_def Col ).
assert (Col M L' L') by (conclude_def Col ).
assert (Par K F' M L') by (apply (proposition_30 K F' M L' H G' F' G' L'); assumption).
assert (Par F' K L' M) by (forward_using lemma_parallelflip).
assert (PG F' L' M K) by (conclude_def PG ).
let Tf:=fresh in
assert (Tf:exists J', (BetS F' J' M /\ BetS L' J' K)) by (conclude lemma_diagonalsmeet);destruct Tf as [J'];spliter.
assert (BetS K J' L') by (conclude axiom_betweennesssymmetry).
assert (Col F G F') by (conclude lemma_collinear5).
assert (Col F G G') by (conclude lemma_collinear5).
assert (Par F' K H G') by (forward_using lemma_parallelflip).
assert (Par F' G' K H) by (forward_using lemma_parallelflip).
assert (PG F' K H G') by (conclude_def PG ).
assert (EF F K H G F' K H G') by (apply (proposition_35_bis F K H G F' G'); assumption).
assert (EF A B m D F' K H G') by (conclude axiom_EFtransitive).
assert (Col F L G) by (forward_using lemma_collinearorder).
assert (Col G L G') by (conclude lemma_collinear5).
assert (Col G L L') by (conclude lemma_collinear5).
assert (Par G' H M L') by (forward_using lemma_parallelflip).
assert (Par G' L' H M) by (forward_using lemma_parallelflip).
assert (PG G' H M L') by (conclude_def PG ).
assert (EF G H M L G' H M L') by (apply (proposition_35_bis G H M L G' L'); assumption).
assert (EF D B e C G' H M L') by (conclude axiom_EFtransitive).
assert (EF A B C D F' K M L') by (apply (lemma_paste4_rectangles A B C D F' G' H J' K L' M P e m); assumption).
assert (Par F' K M L') by (forward_using lemma_parallelflip).
assert (Par F' L' K M) by (forward_using lemma_parallelflip).
assert (PG F' K M L') by (conclude_def PG ).
assert (Col F L F') by (forward_using lemma_collinearorder).
assert (EF F K M L F' K M L') by (apply (proposition_35_bis F K M L F' L'); assumption).
assert (EF F' K M L' F K M L) by (conclude axiom_EFsymmetric).
assert (EF A B C D F K M L) by (conclude axiom_EFtransitive).
close.
Qed.

End Euclid.