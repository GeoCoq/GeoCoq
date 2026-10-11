Require Export GeoCoq.Elements.OriginalProofs.proposition_34.
Require Export GeoCoq.Elements.OriginalProofs.lemma_diagonalsmeet.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ETreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TCreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectangleparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectanglerotate.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectanglereverse.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rightangleNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearright.
Require Export GeoCoq.Elements.OriginalProofs.lemma_10_12.
Require Export GeoCoq.Elements.OriginalProofs.lemma_8_3.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrotate.

Section Euclid.

Context `{Ax : euclidean_euclidean}.

Existing Instance area_follows_Euclid.

Lemma lemma_paste4_rectangles :
   forall A B C D F G H J K L M P e m,
   EF A B m D F K H G -> EF D B e C G H M L ->
   BetS A P C -> BetS B P D -> BetS K H M -> BetS F G L ->
   BetS B m D -> BetS B e C -> BetS F J M -> BetS K J L ->
   nCol A B D -> nCol C B D -> RE F G H K -> RE G L M H ->
   EF A B C D F K M L.
Proof.
intros A B C D F G H J K L M P e m.
intros.
assert ((Per K F G /\ Per F G H /\ Per G H K /\ Per H K F /\ CR F H G K)) by (conclude_def RE ).
assert ((Per H G L /\ Per G L M /\ Per L M H /\ Per M H G /\ CR G M L H)) by (conclude_def RE ).
assert (nCol F G H) by (conclude lemma_rightangleNC).
assert (nCol L G H).
 {
 assert (Per L G H) by (conclude lemma_8_2).
 conclude lemma_rightangleNC.
 }
assert (neq G H) by (forward_using lemma_NCdistinct).
assert (neq H G) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists h, (BetS H G h /\ Cong G h G H)) by (conclude lemma_extension);destruct Tf as [h];spliter.
assert (BetS h G H) by (conclude axiom_betweennesssymmetry).
assert (Col H G h) by (conclude_def Col ).
assert (Col G H h) by (forward_using lemma_collinearorder).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col G H H) by (conclude_def Col ).
assert (neq h H) by (forward_using lemma_betweennotequal).
assert (neq h G) by (forward_using lemma_betweennotequal).
assert (Cong h G G H) by (forward_using lemma_congruenceflip).
assert (Per H G F) by (conclude lemma_8_2).
assert (Per h G F) by (conclude lemma_collinearright).
assert (Per F G h) by (conclude lemma_8_2).
assert (Cong F h F H) by (conclude lemma_10_12).
assert (Cong F G F G) by (conclude cn_congruencereflexive).
assert (Cong_3 F G h F G H) by (conclude_def Cong_3 ).
assert (nCol F G h) by (conclude lemma_rightangleNC).
assert (Triangle F G h) by (conclude_def Triangle ).
assert (ET F G h F G H) by (conclude axiom_congruentequal).
assert (PG F G H K) by (conclude lemma_rectangleparallelogram).
assert (PG G H K F) by (conclude lemma_PGrotate).
assert (Cong_3 H G F F K H) by (forward_using proposition_34).
assert (nCol H G F) by (forward_using lemma_NCorder).
assert (Triangle H G F) by (conclude_def Triangle ).
assert (ET H G F F K H) by (conclude axiom_congruentequal).
assert (ET F K H H G F) by (conclude axiom_ETsymmetric).
assert (ET F K H F G H) by (forward_using axiom_ETpermutation).
assert (ET F G H F K H) by (conclude axiom_ETsymmetric).
assert (ET F G h F K H) by (conclude axiom_ETtransitive).
assert (ET F G h F H K) by (forward_using axiom_ETpermutation).
assert (ET F H K F G h) by (conclude axiom_ETsymmetric).
assert (ET F H K G F h) by (forward_using axiom_ETpermutation).
assert (nCol F H G) by (forward_using lemma_NCorder).
assert (Triangle F H G) by (conclude_def Triangle ).
assert (ET F H G F H G) by (conclude lemma_ETreflexive).
assert (ET F H G G F H) by (forward_using axiom_ETpermutation).
let Tf:=fresh in
assert (Tf:exists N, (BetS F N H /\ BetS G N K)) by (conclude lemma_diagonalsmeet);destruct Tf as [N];spliter.
assert (eq G G) by (conclude cn_equalityreflexive).
assert (EF F G H K G H F h) by (conclude axiom_paste3).
assert (EF G H F h F G H K) by (conclude axiom_EFsymmetric).
assert (EF G H F h F K H G) by (forward_using axiom_EFpermutation).
assert (EF F K H G G H F h) by (conclude axiom_EFsymmetric).
assert (EF A B m D G H F h) by (conclude axiom_EFtransitive).
assert (EF A B m D F h G H) by (forward_using axiom_EFpermutation).
assert (nCol G H F) by (forward_using lemma_NCorder).
assert (nCol h H F) by (conclude lemma_NChelper).
assert (nCol F h H) by (forward_using lemma_NCorder).
assert (ET A B D F h H) by (conclude lemma_really_triangle).
assert (RE H M L G) by (conclude lemma_rectanglereverse).
assert (RE M L G H) by (conclude lemma_rectanglerotate).
assert (RE L G H M) by (conclude lemma_rectanglerotate).
assert ((Per M L G /\ Per L G H /\ Per G H M /\ Per H M L /\ CR L H G M)) by (conclude_def RE ).
assert (Per H G L) by (conclude lemma_8_2).
assert (Per h G L) by (conclude lemma_collinearright).
assert (Per L G h) by (conclude lemma_8_2).
assert (Cong L h L H) by (conclude lemma_10_12).
assert (Cong L G L G) by (conclude cn_congruencereflexive).
assert (Cong_3 L G h L G H) by (conclude_def Cong_3 ).
assert (nCol L G h) by (conclude lemma_rightangleNC).
assert (Triangle L G h) by (conclude_def Triangle ).
assert (ET L G h L G H) by (conclude axiom_congruentequal).
assert (PG L G H M) by (conclude lemma_rectangleparallelogram).
assert (PG G H M L) by (conclude lemma_PGrotate).
assert (Cong_3 H G L L M H) by (forward_using proposition_34).
assert (nCol H G L) by (forward_using lemma_NCorder).
assert (Triangle H G L) by (conclude_def Triangle ).
assert (ET H G L L M H) by (conclude axiom_congruentequal).
assert (ET L M H H G L) by (conclude axiom_ETsymmetric).
assert (ET L M H L G H) by (forward_using axiom_ETpermutation).
assert (ET L G H L M H) by (conclude axiom_ETsymmetric).
assert (ET L G h L M H) by (conclude axiom_ETtransitive).
assert (ET L G h L H M) by (forward_using axiom_ETpermutation).
assert (ET L H M L G h) by (conclude axiom_ETsymmetric).
assert (ET L H M G L h) by (forward_using axiom_ETpermutation).
assert (nCol L H G) by (forward_using lemma_NCorder).
assert (Triangle L H G) by (conclude_def Triangle ).
assert (ET L H G L H G) by (conclude lemma_ETreflexive).
assert (ET L H G G L H) by (forward_using axiom_ETpermutation).
let Tf:=fresh in
assert (Tf:exists N', (BetS L N' H /\ BetS G N' M)) by (conclude lemma_diagonalsmeet);destruct Tf as [N'];spliter.
assert (EF L G H M G H L h) by (conclude axiom_paste3).
assert (EF G H L h L G H M) by (conclude axiom_EFsymmetric).
assert (EF G H L h G H M L) by (forward_using axiom_EFpermutation).
assert (EF G H M L G H L h) by (conclude axiom_EFsymmetric).
assert (EF D B e C G H L h) by (conclude axiom_EFtransitive).
assert (EF D B e C L h G H) by (forward_using axiom_EFpermutation).
assert (nCol G H L) by (forward_using lemma_NCorder).
assert (nCol h H L) by (conclude lemma_NChelper).
assert (nCol L h H) by (forward_using lemma_NCorder).
assert (nCol D B C) by (forward_using lemma_NCorder).
assert (ET D B C L h H) by (conclude lemma_really_triangle).
assert (ET F h H A B D) by (conclude axiom_ETsymmetric).
assert (ET F h H B D A) by (forward_using axiom_ETpermutation).
assert (ET B D A F h H) by (conclude axiom_ETsymmetric).
assert (ET B D A h H F) by (forward_using axiom_ETpermutation).
assert (ET D B C h H L) by (forward_using axiom_ETpermutation).
assert (ET h H L D B C) by (conclude axiom_ETsymmetric).
assert (ET h H L B D C) by (forward_using axiom_ETpermutation).
assert (ET B D C h H L) by (conclude axiom_ETsymmetric).
assert (EF B A D C h F H L) by (conclude axiom_paste3).
assert (EF h F H L B A D C) by (conclude axiom_EFsymmetric).
assert (EF h F H L A B C D) by (forward_using axiom_EFpermutation).
assert (EF A B C D h F H L) by (conclude axiom_EFsymmetric).
assert (EF A B C D F h L H) by (forward_using axiom_EFpermutation).
assert (neq F G) by (forward_using lemma_betweennotequal).
assert (neq G L) by (forward_using lemma_betweennotequal).
assert (neq L G) by (conclude lemma_inequalitysymmetric).
assert (BetS L G F) by (conclude axiom_betweennesssymmetry).
assert (Out F G L) by (conclude lemma_ray4).
assert (Out L G F) by (conclude lemma_ray4).
assert (neq K H) by (forward_using lemma_betweennotequal).
assert (neq H M) by (forward_using lemma_betweennotequal).
assert (neq M H) by (conclude lemma_inequalitysymmetric).
assert (BetS M H K) by (conclude axiom_betweennesssymmetry).
assert (Out K H M) by (conclude lemma_ray4).
assert (Out M H K) by (conclude lemma_ray4).
assert (Per K F L) by (conclude lemma_8_3).
assert (Per M L F) by (conclude lemma_8_3).
assert (Per F L M) by (conclude lemma_8_2).
assert (Per L M K) by (conclude lemma_8_3).
assert (Per F K H) by (conclude lemma_8_2).
assert (Per F K M) by (conclude lemma_8_3).
assert (Per M K F) by (conclude lemma_8_2).
assert (BetS L J K) by (conclude axiom_betweennesssymmetry).
assert (CR F M L K) by (conclude_def CR ).
assert (RE F L M K) by (conclude_def RE ).
assert (Col K H M) by (conclude_def Col ).
assert (EF F h L H F L M K) by (conclude lemma_7_12).
assert (EF A B C D F L M K) by (conclude axiom_EFtransitive).
assert (EF A B C D F K M L) by (forward_using axiom_EFpermutation).
close.
Qed.

End Euclid.