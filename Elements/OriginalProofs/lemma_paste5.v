Require Export GeoCoq.Elements.OriginalProofs.lemma_rectangleparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.proposition_34.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crossimpliesopposite.

Section Euclid.

Context `{Ax:area}.

Lemma lemma_paste5 : 
   forall B C D E L M b c d e l m, 
   EF B M L D b m l d -> EF M C E L m c e l -> BetS B M C -> BetS b m c -> BetS E L D -> BetS e l d -> RE M C E L -> RE m c e l ->
   EF B C E D b c e d.
Proof.
intros.
assert (PG M C E L) by (conclude lemma_rectangleparallelogram).
assert (PG m c e l) by (conclude lemma_rectangleparallelogram).
assert (Par M C E L) by (conclude_def PG ).
assert (nCol M C L) by (forward_using lemma_parallelNC).
assert (Par m c e l) by (conclude_def PG ).
assert (nCol m c l) by (forward_using lemma_parallelNC).
assert (Cong_3 C M L L E C) by (conclude proposition_34).
assert (Cong_3 c m l l e c) by (conclude proposition_34).
assert (ET C M L L E C) by (conclude axiom_congruentequal).
assert (ET c m l l e c) by (conclude axiom_congruentequal).
assert (CR M E C L) by (conclude_def RE ).
assert (CR m e c l) by (conclude_def RE ).
assert (ET c m l c l e) by (forward_using axiom_ETpermutation).
assert (ET c l e c m l) by (conclude axiom_ETsymmetric).
assert (ET c l e m c l) by (forward_using axiom_ETpermutation).
assert (ET m c l c l e) by (conclude axiom_ETsymmetric).
assert (ET C M L C L E) by (forward_using axiom_ETpermutation).
assert (ET C L E C M L) by (conclude axiom_ETsymmetric).
assert (ET C L E M C L) by (forward_using axiom_ETpermutation).
assert (ET M C L C L E) by (conclude axiom_ETsymmetric).
assert (TS M C L E) by (forward_using lemma_crossimpliesopposite).
assert (TS m c l e) by (forward_using lemma_crossimpliesopposite).
assert (ET M C L m c l) by (conclude axiom_halvesofequals).
assert (EF M C E L e c m l) by (forward_using axiom_EFpermutation).
assert (EF e c m l M C E L) by (conclude axiom_EFsymmetric).
assert (EF e c m l E C M L) by (forward_using axiom_EFpermutation).
assert (EF E C M L e c m l) by (conclude axiom_EFsymmetric).
assert (TS E C L M) by (conclude lemma_oppositesidesymmetric).
assert (TS e c l m) by (conclude lemma_oppositesidesymmetric).
assert (ET M C L E C L) by (forward_using axiom_ETpermutation).
assert (ET E C L M C L) by (conclude axiom_ETsymmetric).
assert (ET E C L C L M) by (forward_using axiom_ETpermutation).
assert (ET m c l e c l) by (forward_using axiom_ETpermutation).
assert (ET e c l m c l) by (conclude axiom_ETsymmetric).
assert (ET e c l c l m) by (forward_using axiom_ETpermutation).
assert (ET E C L e c l) by (conclude axiom_halvesofequals).
assert (EF B M L D d b m l) by (forward_using axiom_EFpermutation).
assert (EF d b m l B M L D) by (conclude axiom_EFsymmetric).
assert (EF d b m l D B M L) by (forward_using axiom_EFpermutation).
assert (EF D B M L d b m l) by (conclude axiom_EFsymmetric).
assert (EF D B C L d b c l) by (conclude axiom_paste2).
assert (EF D B C L b d l c) by (forward_using axiom_EFpermutation).
assert (EF b d l c D B C L) by (conclude axiom_EFsymmetric).
assert (EF b d l c B D L C) by (forward_using axiom_EFpermutation).
assert (EF B D L C b d l c) by (conclude axiom_EFsymmetric).
assert (ET E C L l e c) by (forward_using axiom_ETpermutation).
assert (ET l e c E C L) by (conclude axiom_ETsymmetric).
assert (ET l e c L E C) by (forward_using axiom_ETpermutation).
assert (ET L E C l e c) by (conclude axiom_ETsymmetric).
assert (BetS D L E) by (conclude axiom_betweennesssymmetry).
assert (BetS d l e) by (conclude axiom_betweennesssymmetry).
assert (EF B D E C b d e c) by (conclude axiom_paste2).
assert (EF B D E C b c e d) by (forward_using axiom_EFpermutation).
assert (EF b c e d B D E C) by (conclude axiom_EFsymmetric).
assert (EF b c e d B C E D) by (forward_using axiom_EFpermutation).
assert (EF B C E D b c e d) by (conclude axiom_EFsymmetric).
close.
Qed.

End Euclid.


