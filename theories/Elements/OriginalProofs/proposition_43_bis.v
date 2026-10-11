Require Export GeoCoq.Elements.OriginalProofs.proposition_36_bis.
Require Export GeoCoq.Elements.OriginalProofs.lemma_paralleltransitiveouter.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelfacts.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectangleonbase.
Require Export GeoCoq.Elements.OriginalProofs.lemma_Playfair.
Require Export GeoCoq.Elements.OriginalProofs.lemma_twoperpsparallel.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectangleparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectanglerotate.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectanglereverse.
Require Export GeoCoq.Elements.OriginalProofs.lemma_8_3.
Require Export GeoCoq.Elements.OriginalProofs.lemma_sameside2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidecollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrectangle.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Existing Instance area_follows_Euclid.

Lemma proposition_43_bis :
   forall A B C D E F G H K,
   PG A B C D -> BetS A H D -> BetS A E B -> BetS D F C -> BetS B G C -> BetS A K C ->
   PG E A H K -> PG G K F C ->
   EF K G B E D F K H.
Proof.
intros A B C D E F G H K.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert ((Par E A H K /\ Par E K A H)) by (conclude_def PG ).
assert ((Par G K F C /\ Par G C K F)) by (conclude_def PG ).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (nCol A D B) by (forward_using lemma_parallelNC).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (neq A D) by (forward_using lemma_NCdistinct).
assert (neq D A) by (conclude lemma_inequalitysymmetric).
assert (nCol B C D) by (forward_using lemma_parallelNC).
assert (neq D C) by (forward_using lemma_NCdistinct).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Col B G C) by (conclude_def Col ).
assert (Col G C B) by (forward_using lemma_collinearorder).
assert (Col B C G) by (forward_using lemma_collinearorder).
assert (Col G C C) by (conclude_def Col ).
assert (Col B C C) by (conclude_def Col ).
assert (Col B C B) by (conclude_def Col ).
assert (Col A H D) by (conclude_def Col ).
assert (Col A D H) by (forward_using lemma_collinearorder).
assert (Col A H A) by (conclude_def Col ).
assert (Col A D A) by (conclude_def Col ).
assert (Col D F C) by (conclude_def Col ).
assert (Col F C D) by (forward_using lemma_collinearorder).
assert (Col F C C) by (conclude_def Col ).
assert (Col A E B) by (conclude_def Col ).
assert (Col E A B) by (forward_using lemma_collinearorder).
assert (Col E A A) by (conclude_def Col ).
assert (neq B G) by (forward_using lemma_betweennotequal).
assert (neq G C) by (forward_using lemma_betweennotequal).
assert (nCol G K F) by (forward_using lemma_parallelNC).
assert (neq K F) by (forward_using lemma_NCdistinct).
assert (neq G K) by (forward_using lemma_NCdistinct).
assert (neq K G) by (conclude lemma_inequalitysymmetric).
assert (nCol E A H) by (forward_using lemma_parallelNC).
assert (nCol E K A) by (forward_using lemma_parallelNC).
assert (neq E K) by (forward_using lemma_NCdistinct).
assert (neq K E) by (conclude lemma_inequalitysymmetric).
assert (nCol E A K) by (forward_using lemma_parallelNC).
assert (nCol A H K) by (forward_using lemma_parallelNC).
assert (neq H K) by (forward_using lemma_NCdistinct).
assert (Par K F G C) by (conclude lemma_parallelsymmetric).
assert (Par K F B C) by (conclude lemma_collinearparallel2).
assert (Par E K A D) by (conclude lemma_collinearparallel2).
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (Par C B D A) by (forward_using lemma_parallelflip).
assert (Par K E D A) by (forward_using lemma_parallelflip).
assert (BetS B E A) by (conclude axiom_betweennesssymmetry).
assert (Col C B B) by (conclude_def Col ).
assert (Col D A A) by (conclude_def Col ).
assert (Col K E E) by (conclude_def Col ).
assert (Par C B K E) by (conclude lemma_paralleltransitiveouter).
assert (Par B C E K) by (forward_using lemma_parallelflip).
assert (Par E K B C) by (conclude lemma_parallelsymmetric).
assert (Par B C K F) by (conclude lemma_parallelsymmetric).
assert (Par B C K E) by (forward_using lemma_parallelflip).
assert (Col K F E) by (conclude lemma_Playfair).
assert (Par G K D C) by (conclude lemma_collinearparallel2).
assert (Par K G D C) by (forward_using lemma_parallelflip).
assert (Par A B D C) by (forward_using lemma_parallelflip).
assert (Col A B B) by (conclude_def Col ).
assert (Col D C C) by (conclude_def Col ).
assert (Col K G G) by (conclude_def Col ).
assert (Par A B K G) by (conclude lemma_paralleltransitiveouter).
assert (Par H K E A) by (conclude lemma_parallelsymmetric).
assert (Par H K A B) by (conclude lemma_collinearparallel2).
assert (Par A B H K) by (conclude lemma_parallelsymmetric).
assert (Par A B K H) by (forward_using lemma_parallelflip).
assert (Col K G H) by (conclude lemma_Playfair).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (OS A A B C) by (conclude lemma_samesidereflexive).
assert (BetS C K A) by (conclude axiom_betweennesssymmetry).
assert (neq C A) by (forward_using lemma_NCdistinct).
assert (Out C A K) by (conclude lemma_ray4).
assert (OS A K B C) by (conclude lemma_sameside2).
assert (eq K K) by (conclude cn_equalityreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (Col K F K) by (conclude_def Col ).
assert (Col K F F) by (conclude_def Col ).
assert (Col A D D) by (conclude_def Col ).
let Tf:=fresh in
assert (Tf:exists A' D', (RE A' D' C B /\ Col A D A' /\ Col A D D')) by (conclude lemma_rectangleonbase);destruct Tf as [A'[D']];spliter.
assert (Par A D G C) by (conclude lemma_collinearparallel2).
let Tf:=fresh in
assert (Tf:exists H' D2, (RE H' D2 C G /\ Col A D H' /\ Col A D D2)) by (conclude lemma_rectangleonbase);destruct Tf as [H'[D2]];spliter.
let Tf:=fresh in
assert (Tf:exists K' F', (RE K' F' C G /\ Col K F K' /\ Col K F F')) by (conclude lemma_rectangleonbase);destruct Tf as [K'[F']];spliter.
assert (Par K F B G) by (conclude lemma_collinearparallel2).
let Tf:=fresh in
assert (Tf:exists E' K4, (RE E' K4 G B /\ Col K F E' /\ Col K F K4)) by (conclude lemma_rectangleonbase);destruct Tf as [E'[K4]];spliter.
assert ((Per B A' D' /\ Per A' D' C /\ Per D' C B /\ Per C B A' /\ CR A' C D' B)) by (conclude_def RE ).
assert ((Per G H' D2 /\ Per H' D2 C /\ Per D2 C G /\ Per C G H' /\ CR H' C D2 G)) by (conclude_def RE ).
assert ((Per G K' F' /\ Per K' F' C /\ Per F' C G /\ Per C G K' /\ CR K' C F' G)) by (conclude_def RE ).
assert ((Per B E' K4 /\ Per E' K4 G /\ Per K4 G B /\ Per G B E' /\ CR E' G K4 B)) by (conclude_def RE ).
assert (neq G B) by (conclude lemma_inequalitysymmetric).
assert (neq C G) by (conclude lemma_inequalitysymmetric).
assert (Col C B G) by (forward_using lemma_collinearorder).
assert (Per B C D') by (conclude lemma_8_2).
assert (Per G C D') by (conclude lemma_collinearright).
assert (Per G C D2) by (conclude lemma_8_2).
assert (eq D2 D') by (conclude lemma_perpunique).
assert (RE H' D' C G) by (conclude cn_equalitysub).
assert (Per G H' D') by (conclude cn_equalitysub).
assert (Col B G C) by (conclude_def Col ).
assert (Col C G B) by (forward_using lemma_collinearorder).
assert (Per B G K') by (conclude lemma_collinearright).
assert (Per B G K4) by (conclude lemma_8_2).
assert (eq K4 K') by (conclude lemma_perpunique).
assert (RE E' K' G B) by (conclude cn_equalitysub).
assert (PG A' D' C B) by (conclude lemma_rectangleparallelogram).
assert (PG H' D' C G) by (conclude lemma_rectangleparallelogram).
assert (PG K' F' C G) by (conclude lemma_rectangleparallelogram).
assert (PG E' K' G B) by (conclude lemma_rectangleparallelogram).
assert ((Par A' D' C B /\ Par A' B D' C)) by (conclude_def PG ).
assert ((Par H' D' C G /\ Par H' G D' C)) by (conclude_def PG ).
assert ((Par K' F' C G /\ Par K' G F' C)) by (conclude_def PG ).
assert ((Par E' K' G B /\ Par E' B K' G)) by (conclude_def PG ).
assert (nCol A' D' B) by (forward_using lemma_parallelNC).
assert (neq A' D') by (forward_using lemma_NCdistinct).
assert (neq A' B) by (forward_using lemma_NCdistinct).
assert (nCol A' D' C) by (forward_using lemma_parallelNC).
assert (neq D' C) by (forward_using lemma_NCdistinct).
assert (nCol H' D' G) by (forward_using lemma_parallelNC).
assert (neq H' D') by (forward_using lemma_NCdistinct).
assert (neq H' G) by (forward_using lemma_NCdistinct).
assert (neq G H') by (conclude lemma_inequalitysymmetric).
assert (nCol K' F' G) by (forward_using lemma_parallelNC).
assert (neq K' F') by (forward_using lemma_NCdistinct).
assert (neq K' G) by (forward_using lemma_NCdistinct).
assert (nCol E' K' B) by (forward_using lemma_parallelNC).
assert (neq E' K') by (forward_using lemma_NCdistinct).
assert (neq E' B) by (forward_using lemma_NCdistinct).
assert (neq B E') by (conclude lemma_inequalitysymmetric).
assert (neq K' E') by (conclude lemma_inequalitysymmetric).
assert (OS A' A B C) by (conclude lemma_samesidepar).
assert (OS D' A B C) by (conclude lemma_samesidepar).
assert (OS H' A B C) by (conclude lemma_samesidepar).
assert (OS K' K B C) by (conclude lemma_samesidepar).
assert (OS E' K B C) by (conclude lemma_samesidepar).
assert (OS F' K B C) by (conclude lemma_samesidepar).
assert (OS K A B C) by (forward_using lemma_samesidesymmetric).
assert (OS K' A B C) by (conclude lemma_samesidetransitive).
assert (OS E' A B C) by (conclude lemma_samesidetransitive).
assert (OS F' A B C) by (conclude lemma_samesidetransitive).
assert (OS A D' B C) by (forward_using lemma_samesidesymmetric).
assert (OS A H' B C) by (forward_using lemma_samesidesymmetric).
assert (OS A A' B C) by (forward_using lemma_samesidesymmetric).
assert (OS A E' B C) by (forward_using lemma_samesidesymmetric).
assert (OS K' H' B C) by (conclude lemma_samesidetransitive).
assert (OS F' D' B C) by (conclude lemma_samesidetransitive).
assert (OS A' K' B C).
 {
 assert (OS A K' B C) by (forward_using lemma_samesidesymmetric).
 conclude lemma_samesidetransitive.
 }
assert (OS A' E' B C).
 {
 conclude lemma_samesidetransitive.
 }
assert (OS K' H' C B) by (forward_using lemma_samesidesymmetric).
assert (OS K' H' C G) by (apply (lemma_samesidecollinear C B G K' H'); assumption).
assert (Out G K' H') by (conclude lemma_erectedperpendicularunique).
assert (Col G K' H') by (conclude lemma_rayimpliescollinear).
assert (Per G B A') by (conclude lemma_collinearright).
assert (OS A' E' B G) by (apply (lemma_samesidecollinear B C G A' E'); assumption).
assert (OS A' E' G B) by (forward_using lemma_samesidesymmetric).
assert (Out B A' E') by (conclude lemma_erectedperpendicularunique).
assert (Col B A' E') by (conclude lemma_rayimpliescollinear).
assert (Per G C F') by (conclude lemma_8_2).
assert (OS F' D' C B) by (forward_using lemma_samesidesymmetric).
assert (OS F' D' C G) by (apply (lemma_samesidecollinear C B G F' D'); assumption).
assert (OS F' D' G C) by (forward_using lemma_samesidesymmetric).
assert (Out C F' D') by (conclude lemma_erectedperpendicularunique).
assert (Col C F' D') by (conclude lemma_rayimpliescollinear).
assert (Per A' B C) by (conclude lemma_8_2).
assert (Per A' B G) by (conclude lemma_8_2).
assert (OS A' K' B G) by (apply (lemma_samesidecollinear B C G A' K'); assumption).
assert (Par A' B G K') by (conclude lemma_twoperpsparallel).
assert (Col E K F) by (forward_using lemma_collinearorder).
assert (Col E K K) by (conclude_def Col ).
assert (Par A D E K) by (conclude lemma_parallelsymmetric).
assert (Par A D K F) by (conclude lemma_collinearparallel2).
assert (Par K F A D) by (conclude lemma_parallelsymmetric).
assert (Par K F A' D') by (conclude lemma_collinearparallel2).
assert (nCol K F A') by (forward_using lemma_parallelNC).
assert (nCol K F D') by (forward_using lemma_parallelNC).
assert (nCol K F A) by (forward_using lemma_parallelNC).
assert (nCol K F D) by (forward_using lemma_parallelNC).
assert (nCol K F G) by (forward_using lemma_parallelNC).
assert (TS A K F B) by (conclude_def TS ).
assert (OS A' A K F) by (conclude lemma_samesidepar).
assert (TS A' K F B) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists X, (BetS A' X B /\ Col K F X /\ nCol K F A')) by (conclude_def TS );destruct Tf as [X];spliter.
assert (Col A' X B) by (conclude_def Col ).
assert (Col A' B X) by (forward_using lemma_collinearorder).
assert (Col A' B E') by (forward_using lemma_collinearorder).
assert (eq X E') by (apply (lemma_intersectionunique K F A' B X E'); assumption).
assert (BetS A' E' B) by (conclude cn_equalitysub).
assert (Col D' F' C) by (forward_using lemma_collinearorder).
assert (Col D' C F') by (forward_using lemma_collinearorder).
assert (TS D K F C) by (conclude_def TS ).
assert (OS D' D K F) by (conclude lemma_samesidepar).
assert (TS D' K F C) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists Y, (BetS D' Y C /\ Col K F Y /\ nCol K F D')) by (conclude_def TS );destruct Tf as [Y];spliter.
assert (Col D' Y C) by (conclude_def Col ).
assert (Col D' C Y) by (forward_using lemma_collinearorder).
assert (eq Y F') by (apply (lemma_intersectionunique K F D' C Y F'); assumption).
assert (BetS D' F' C) by (conclude cn_equalitysub).
assert (OS H' A K F) by (conclude lemma_samesidepar).
assert (TS H' K F B) by (conclude lemma_planeseparation).
assert (Par B C K F) by (conclude lemma_parallelsymmetric).
assert (OS G B K F) by (conclude lemma_samesidepar).
assert (TS B K F H') by (conclude lemma_oppositesidesymmetric).
assert (TS G K F H') by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists Z, (BetS G Z H' /\ Col K F Z /\ nCol K F G)) by (conclude_def TS );destruct Tf as [Z];spliter.
assert (Col G Z H') by (conclude_def Col ).
assert (Col G H' Z) by (forward_using lemma_collinearorder).
assert (Col G H' K') by (forward_using lemma_collinearorder).
assert (eq Z K') by (apply (lemma_intersectionunique K F G H' Z K'); assumption).
assert (BetS G K' H') by (conclude cn_equalitysub).
assert (Col G K' G) by (conclude_def Col ).
assert (Par A' B G H') by (conclude lemma_collinearparallel2).
assert (Par G H' A' B) by (conclude lemma_parallelsymmetric).
assert (TP G H' A' B) by (conclude lemma_paralleldef2B).
assert (OS A' B G H') by (conclude_def TP ).
assert (Par G H' D' C) by (forward_using lemma_parallelflip).
assert (TP G H' D' C) by (conclude lemma_paralleldef2B).
assert (OS D' C G H') by (conclude_def TP ).
assert (nCol G H' B) by (forward_using lemma_parallelNC).
assert (Col G H' G) by (conclude_def Col ).
assert (TS B G H' C) by (conclude_def TS ).
assert (TS A' G H' C) by (conclude lemma_planeseparation).
assert (TS C G H' A') by (conclude lemma_oppositesidesymmetric).
assert (TS D' G H' A') by (conclude lemma_planeseparation).
assert (TS A' G H' D') by (conclude lemma_oppositesidesymmetric).
let Tf:=fresh in
assert (Tf:exists U, (BetS A' U D' /\ Col G H' U /\ nCol G H' A')) by (conclude_def TS );destruct Tf as [U];spliter.
assert (Col A' U D') by (conclude_def Col ).
assert (Col A' D' U) by (forward_using lemma_collinearorder).
assert (Col A' D' H') by (conclude lemma_collinear5).
assert (eq H' H') by (conclude cn_equalityreflexive).
assert (Col G H' H') by (conclude_def Col ).
assert (Col C B C) by (conclude_def Col ).
assert (Par A' D' G C) by (apply (lemma_collinearparallel2 A' D' C B G C); assumption).
assert (nCol A' D' G) by (forward_using lemma_parallelNC).
assert (eq U H') by (apply (lemma_intersectionunique A' D' G H' U H'); assumption).
assert (BetS A' H' D') by (conclude cn_equalitysub).
assert (Col E K K') by (conclude lemma_collinear5).
assert (Par A B G K) by (forward_using lemma_parallelflip).
assert (Per K' G C) by (conclude lemma_8_2).
assert (BetS A' K' C) by (apply (lemma_shear A B C D E K G A' K'); assumption).
assert (neq K' H') by (forward_using lemma_betweennotequal).
assert (neq H' K') by (conclude lemma_inequalitysymmetric).
assert (neq A' E') by (forward_using lemma_betweennotequal).
assert (neq E' A') by (conclude lemma_inequalitysymmetric).
assert (neq A' H') by (forward_using lemma_betweennotequal).
assert (neq D' F') by (forward_using lemma_betweennotequal).
assert (neq F' D') by (conclude lemma_inequalitysymmetric).
assert (eq A' A') by (conclude cn_equalityreflexive).
assert (eq D' D') by (conclude cn_equalityreflexive).
assert (eq K' K') by (conclude cn_equalityreflexive).
assert (Col A' B A') by (conclude_def Col ).
assert (Col A' B B) by (conclude_def Col ).
assert (Col A' D' A') by (conclude_def Col ).
assert (Col G H' K') by (forward_using lemma_collinearorder).
assert (Col A B E) by (forward_using lemma_collinearorder).
assert (neq E B) by (forward_using lemma_betweennotequal).
assert (neq B E) by (conclude lemma_inequalitysymmetric).
assert (Par K G A B) by (conclude lemma_parallelsymmetric).
assert (Par K G B E) by (conclude lemma_collinearparallel2).
assert (Par E K G B) by (conclude lemma_collinearparallel2).
assert (Par K E G B) by (forward_using lemma_parallelflip).
assert (PG K G B E) by (conclude_def PG ).
assert (Par G K' A' B) by (conclude lemma_parallelsymmetric).
assert (Col A' B E') by (forward_using lemma_collinearorder).
assert (Par G K' B E') by (conclude lemma_collinearparallel2).
assert (Par K' G B E') by (forward_using lemma_parallelflip).
assert (Par B G K F) by (conclude lemma_parallelsymmetric).
assert (Par B G K' E') by (conclude lemma_collinearparallel2).
assert (Par K' E' B G) by (conclude lemma_parallelsymmetric).
assert (Par K' E' G B) by (forward_using lemma_parallelflip).
assert (PG K' G B E') by (conclude_def PG ).
assert (Col K E K') by (conclude lemma_collinear5).
assert (Col K E E') by (conclude lemma_collinear5).
assert (EF K G B E K' G B E') by (apply (proposition_35_bis K G B E K' E'); assumption).
assert (Col K G K) by (conclude_def Col ).
assert (neq K H) by (conclude lemma_inequalitysymmetric).
assert (Par D C K G) by (conclude lemma_parallelsymmetric).
assert (Par D C K H) by (conclude lemma_collinearparallel2).
assert (Par K H D C) by (conclude lemma_parallelsymmetric).
assert (Col D C F) by (forward_using lemma_collinearorder).
assert (Col D C D) by (conclude_def Col ).
assert (neq D F) by (forward_using lemma_betweennotequal).
assert (neq F D) by (conclude lemma_inequalitysymmetric).
assert (Par K H F D) by (conclude lemma_collinearparallel2).
assert (Par H K F D) by (forward_using lemma_parallelflip).
assert (neq H D) by (forward_using lemma_betweennotequal).
assert (Par K F H D) by (conclude lemma_collinearparallel2).
assert (Par H D K F) by (conclude lemma_parallelsymmetric).
assert (PG H K F D) by (conclude_def PG ).
assert (Par D' C H' G) by (conclude lemma_parallelsymmetric).
assert (Col H' G H') by (conclude_def Col ).
assert (Col H' G K') by (forward_using lemma_collinearorder).
assert (Par D' C H' K') by (conclude lemma_collinearparallel2).
assert (Par H' K' D' C) by (conclude lemma_parallelsymmetric).
assert (Col D' C D') by (conclude_def Col ).
assert (Par H' K' F' D') by (conclude lemma_collinearparallel2).
assert (Par K F H' D') by (conclude lemma_collinearparallel2).
assert (Par H' D' K F) by (conclude lemma_parallelsymmetric).
assert (Par H' D' K' F') by (conclude lemma_collinearparallel2).
assert (PG H' K' F' D') by (conclude_def PG ).
assert (Col H D H') by (conclude lemma_collinear5).
assert (Col H D D') by (conclude lemma_collinear5).
assert (Cong G C K F) by (forward_using proposition_34).
assert (Cong K' F' G C) by (forward_using proposition_34).
assert (Cong K F G C) by (conclude lemma_congruencesymmetric).
assert (Cong G C K' F') by (conclude lemma_congruencesymmetric).
assert (Cong K F K' F') by (conclude lemma_congruencetransitive).
assert (EF H K F D H' K' F' D') by (apply (proposition_36_bis H K F D H' K' F' D'); assumption).
assert (EF H K F D D' F' K' H') by (forward_using axiom_EFpermutation).
assert (EF D' F' K' H' H K F D) by (conclude axiom_EFsymmetric).
assert (EF D' F' K' H' D F K H) by (forward_using axiom_EFpermutation).
assert (Par K' F' H' D') by (conclude lemma_parallelsymmetric).
assert (Par K' F' D' H') by (forward_using lemma_parallelflip).
assert (Par K' H' F' D') by (forward_using lemma_parallelflip).
assert (PG K' F' D' H') by (conclude_def PG ).
assert (Per H' K' F') by (conclude lemma_collinearright).
assert (RE K' F' D' H') by (conclude lemma_PGrectangle).
assert (OS E' B G H') by (apply (lemma_samesidepar G H' A' B E' B); assumption).
assert (Par D' C G H') by (conclude lemma_parallelsymmetric).
assert (Col D' C C) by (conclude_def Col ).
assert (OS F' C G H') by (apply (lemma_samesidepar G H' D' C F' C); assumption).
assert (TS E' G H' C) by (conclude lemma_planeseparation).
assert (TS C G H' E') by (conclude lemma_oppositesidesymmetric).
assert (TS F' G H' E') by (conclude lemma_planeseparation).
assert (TS E' G H' F') by (conclude lemma_oppositesidesymmetric).
let Tf:=fresh in
assert (Tf:exists V, (BetS E' V F' /\ Col G H' V /\ nCol G H' E')) by (conclude_def TS );destruct Tf as [V];spliter.
assert (neq E' F') by (forward_using lemma_betweennotequal).
assert (Col E' V F') by (conclude_def Col ).
assert (Col E' F' V) by (forward_using lemma_collinearorder).
assert (Col E' F' K) by (apply (lemma_collinear5 K F E' F' K); assumption).
assert (Col E' F' F) by (apply (lemma_collinear5 K F E' F' F); assumption).
assert (Col K F V) by (apply (lemma_collinear5 E' F' K F V); assumption).
assert (eq V K') by (apply (lemma_intersectionunique K F G H' V K'); assumption).
assert (BetS E' K' F') by (conclude cn_equalitysub).
assert (BetS C G B) by (conclude axiom_betweennesssymmetry).
assert (BetS H' K' G) by (conclude axiom_betweennesssymmetry).
assert (Cong E' K' E' K') by (conclude cn_congruencereflexive).
assert (Cong K' G K' G) by (conclude cn_congruencereflexive).
assert (Cong K' F' K' F') by (conclude cn_congruencereflexive).
assert (Cong F' D' F' D') by (conclude cn_congruencereflexive).
assert (EF E' K' G B K' F' D' H') by (apply (lemma_7_10 E' K' G B K' F' D' H' E' K' F' D' H' A' C B G); assumption).
assert (EF E' K' G B D' F' K' H') by (forward_using axiom_EFpermutation).
assert (EF D' F' K' H' E' K' G B) by (conclude axiom_EFsymmetric).
assert (EF D' F' K' H' K' G B E') by (forward_using axiom_EFpermutation).
assert (EF K' G B E' D' F' K' H') by (conclude axiom_EFsymmetric).
assert (EF K G B E D' F' K' H') by (conclude axiom_EFtransitive).
assert (EF K G B E D F K H) by (conclude axiom_EFtransitive).
close.
Qed.

End Euclid.