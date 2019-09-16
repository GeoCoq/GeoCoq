(* Trisection Segment - Tarski_euclidean

    Roland Coghetto, 14 Septembre 2019
     GNU Lesser General Public License v3.0 
     See LICENSE GeoCoq 2.4.0 

MAIN RESULTS:
 
Theorem SegmTrisectExistence:
forall A B,
exists C, exists D, Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B.

Theorem SegmTrisectUniqueness:
forall A B C D C' D', 
Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B /\
Bet_4 A C' D' B /\ Cong A C' C' D' /\ Cong C' D' D' B ->
(C = C' /\ D = D').

Theorem SegmTrisectExistenceUniqueness:
forall A B, 
exists! C D, Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B.

Application: Construction of the pentatonic pythagorean scale 
===========

Definition TwoThirds T A B := Bet A T B /\ (forall M, Midpoint M A T -> Cong A M T B).
Definition DoubleTwoThirds D A B := Col A B D /\ (forall TT, TwoThirds TT A B -> Midpoint TT A D).

Theorem PentatonicPythagoreScale:
forall A B,
exists FONDAMENTAL N1 N2 N3 N4 OCTAVE,
FONDAMENTAL = B         /\ 
TwoThirds       N3 A B  /\ 
DoubleTwoThirds N1 A N3 /\
TwoThirds       N4 A N1 /\ 
DoubleTwoThirds N2 A N4 /\
Midpoint OCTAVE A B.

If we begin at DO:

DO (FONDAMENTAL) = 1/1 * f
SOL(N3) = 3/2 * f
RE (N1) = (3/2) * (3/2) * (1/2) * f = 9/8 * f
LA (N4) = (9/8) * (3/2) * f = 27/16 * f
MI (N2) = (27/16) * (3/2) * (1/2) * f = 81/64 * f
DO2 (OCTAVE) = 2 * f
or
 

If we begin at C
C  (FONDAMENTAL) = 1/1 * f
G  (N3) = 3/2 * f
D  (N1) = (3/2) * (3/2) * (1/2) * f = 9/8 * f
A  (N4) = (9/8) * (3/2) * f = 27/16 * f
E  (N2) = (27/16) * (3/2) * (1/2) * f = 81/64 * f
C2 (OCTAVE) = 2 * f

Theorem PentatonicPythagoreScaleTwoOctave:
forall A B,
exists FONDAMENTAL N1 N2 N3 N4 OCTAVE N5 N6 N7 N8 OCTAVE2,
FONDAMENTAL = B                   /\
TwoThirds       N3 A FONDAMENTAL  /\
DoubleTwoThirds N1 A N3           /\
TwoThirds       N4 A N1           /\
DoubleTwoThirds N2 A N4           /\
Midpoint OCTAVE A B               /\
TwoThirds       N7 A OCTAVE       /\
DoubleTwoThirds N5 A N7           /\
TwoThirds       N8 A N5           /\
DoubleTwoThirds N6 A N8           /\
Midpoint OCTAVE2 A OCTAVE.

Bibliograpy:
============
[1] http://villemin.gerard.free.fr/Pavage/Dissecti/Trissect.htm#classi (14/09/2019).
[2] https://fr.wikipedia.org/wiki/Accord_pythagoricien (14/09/2019)
[3] https://en.wikipedia.org/wiki/Pythagorean_tuning (14/09/2019)
[4] Coghetto, Roland. (2018). Pythagorean Tuning: Pentatonic and Heptatonic Scale. 
    Formalized Mathematics. 26. 239-269. 10.2478/forma-2018-0022. 
[5] BASKEVITCH, François. Les représentations de la propagation du son, d'Aristote à l'Encyclopédie. 2008. 
    Thèse de doctorat.
[6] Bernard Parzysz and Yves Hellegouarch. Musique et mathématique: (suivi de) Gammes
    naturelles. Number 53. Association des Professeurs de Mathématiques de l’Enseignement
    Public (APMEP), Paris, 1984
*)

Require Export sesamath_exercises.

Section Segment_Trisection.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

(*****************)
(* Preliminaries *)
(*****************)

Lemma STl6_16_1b: 
forall A B C D, 
A <> B -> Col A B C -> Col A B D -> Col A C D.
Proof.
  intros.
  apply colx with A B.
  auto.
  apply col_trivial_3.
  Col.
  assumption.
Qed.

Lemma par_abbc: 
forall A B C, 
Par A B B C -> Col A B C.
Proof.
  intros.
  assert (Par B A B C). apply par_left_comm;auto.
  assert(Col B A C).
  eapply par_id;auto. Col.
Qed.

Lemma triangle_par_mid2:
forall A B C P Q, 
~ Col B A C -> Midpoint Q A C -> Par B A P Q -> Col P B C -> Midpoint P B C.
Proof.
  intros. assert(~Col C A B). Col. eapply triangle_par_mid with A Q;auto.
Qed.

Lemma Bet4Equal:
forall A B C,
Bet_4 A B C A -> A = B /\ A = C.
Proof.
  intros.
  unfold Bet_4 in H. spliter.
  assert_all. auto.
Qed.

(*********)
(* Steps *)
(*********)

Lemma SegmTrisect01: 
forall A B,
A <> B -> exists C, ~ Col A B C.
Proof.
  intros.
  apply not_col_exists.
  assumption.
Qed.

Lemma SegmTrisect02: 
forall A B C, 
~ Col A B C -> exists D, Midpoint C A D /\ A <> D.
Proof.
  intros.
  assert(exists D, Midpoint C A D).
  apply symmetric_point_construction.
  destruct H0 as [D].
  assert(A <> D). intro. subst. assert(C = D). apply l7_3;auto. subst. assert(Col D B D). ColR. auto.
  exists D.
  auto.
Qed.

Lemma SegmTrisect03: 
forall A B C D, 
~ Col A B C -> Midpoint C A D -> A <> D.
Proof.
  intros.
  intro.
  assert_all.
  auto.
Qed.

Lemma SegmTrisect04: 
forall A B C D, 
~ Col A B C -> Midpoint C A D -> exists E, Midpoint D C E.
Proof.
  intros.
  apply symmetric_point_construction.
Qed.


Lemma SegmTrisect05: 
forall A B C D E,
~ Col A B C -> Midpoint C A D -> Midpoint D C E -> B <> E.
Proof.
  intros.
  assert_diffs.
  assert(Col A C E). apply l6_16_1 with D;finish.
  intro.
  subst.
  assert(Col A E C); finish.
Qed.

Lemma SegmTrisect06: 
forall A B C D E,
~ Col A B C -> Midpoint C A D -> Midpoint D C E -> A <> E.
Proof.
  intros.
  intro.
  subst.
  assert(Midpoint D E C). apply l7_2;auto.
  assert_all. assert(Cong C D D E). Cong.
  assert(Cong C E D E). eapply cong_transitivity with C D;finish.
  assert(C=D). eapply between_cong with E;finish.
  subst. assert_all. auto.
Qed.

Lemma SegmTrisect07: 
forall A B C D E, 
~ Col A B C -> Midpoint C A D -> Midpoint D C E -> Col A C E.
Proof.
  intros.
  assert_diffs.
  apply l6_16_1 with D;finish.
Qed.

Lemma SegmTrisect08:
forall A B C D E,
~ Col A B C -> Midpoint C A D -> Midpoint D C E -> ~ Col E C B.
Proof.
  intros.
  assert_all.
  assert (B <> E). apply SegmTrisect05 with A C D;finish.
  intro. 
  assert(Col C D A); Col.
  assert(Col C D E); Col.
  assert(Col C E A).
  apply STl6_16_1b with D; finish.
  assert(Col C E B);Col.
  assert(Col C A B).
  apply STl6_16_1b with E;finish.
  Col.
Qed.

Lemma SegmTrisect09: 
forall B D E, E <> B ->
exists F, exists G, Col D F G /\ Par F G E B.
Proof.
  intros.
  assert(exists F, exists G, F<>G /\ Par E B F G /\ Col D F G).
  apply parallel_existence. assumption.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  exists x.
  exists x0.
  split.
  auto.
  apply par_symmetry.
  auto.
Qed.

Lemma SegmTrisect10: 
forall A B D E F G, E <> B -> ~ Col B A E -> Col D F G -> Par F G E B ->
~ Par F G A B.
Proof.
  intros.
  intro.
  assert_all.
  assert(Par E B A B). 
    assert(Par E B G F). apply par_symmetry. auto. eapply par_trans with G F; auto.
  assert(Par B A B E);finish.
  assert(Col B A E).
  apply par_id; auto.
  auto.
Qed.

Lemma SegmTrisect11: 
forall A B C D H,
~ Col A B C -> Midpoint C A D -> Col H A B -> D <> H .
Proof.
  intros.
  subst.
  intro.
  subst.
  assert_all.
  assert(Col B A H);Col.
  assert(Col C A H);Col.
  assert(Col B A C). eapply l6_16_1 with H; auto.
  Col.
Qed.

Lemma SegmTrisect12:
forall B D E F G H, 
D <> H -> Par F G E B -> Col D F G -> Col H F G -> Par D H E B.
Proof.
  intros.
  assert(Par E B F G). apply par_symmetry. assumption.
  assert(Par E B D H). 
  apply par_col2_par with F G; auto;Col.
  apply par_symmetry;auto.
Qed.

Lemma SegmTrisect13: 
forall A B C D E H I,
~ Col A B C -> D <> H -> Midpoint C A D -> Midpoint I A H -> Par D H B E ->
Par C I B E.
Proof.
  intros.
  assert(Midpoint C D A);finish.
  assert(Midpoint I H A);finish;
  assert(Par D H C I).
  apply triangle_mid_par with A; finish.
  eapply par_trans with D H.
    + apply par_symmetry; auto.
    + auto.
Qed.

Lemma SegmTrisect14: 
forall A B C D E H I, 
A = H -> ~ Col A B C -> Midpoint C A D -> Midpoint D C E -> Col H A B -> 
Par D H B E -> Par C I B E -> I = H.
Proof.
  intros.
  subst.
  assert_all.
  assert(I = H).
    assert(Col E D H).
      assert(Col E C D);Col.
      assert(Col E C H). assert(Col H C E). eapply SegmTrisect07 with B D;finish. Col.
      eapply STl6_16_1b with C;finish.
  assert(Inter H D B E E). unfold Inter.
  split;auto.
  split.
  assert(Col B B E);Col.
  exists B;auto.
  split;Col.
  assert(~ Col B H D).
  intro.
  assert(Col H D B);Col.
  assert(Col H D C);Col.
  assert(Col H B C).
  eapply STl6_16_1b with D;auto.
  Col.
  auto.
  split. Col. Col.
  assert(~ Par H D B E). apply inter__npar with E;auto.
  auto. tauto. auto.
Qed.

Lemma SegmTrisect15:
forall A B C D E H I, 
A = H -> ~ Col A B C -> Midpoint C A D -> Midpoint D C E -> Col H A B -> 
Par D H B E -> Par C I B E -> Midpoint I A H.
Proof.
  intros.
  assert(I = H). apply SegmTrisect14 with A B C D E;auto.
  subst.
  apply l7_3_2.
Qed.

Lemma SegmTrisect16:
forall A B C D E H I, 
A <> H -> ~ Col A B C -> Midpoint C A D -> Midpoint D C E ->
Col H A B -> Col I A H -> Par D H B E -> Par C I B E ->
Midpoint I A H.
Proof.
  intros.
  assert(~ Col A D B).
    intro. 
    assert(Col A D C);Col.
    assert(A <> D). apply SegmTrisect03 with B C;auto.
    assert(Col A B C). apply STl6_16_1b with D;auto.
    auto.
  assert(Col A D C);Col.
  assert(A <> D). intro. subst. assert(Col D D B);Col.
  assert(~ Col A D H).
    intro.
    assert(Col A C H). eapply STl6_16_1b with D;finish.
    assert(Col A H C);Col.
    assert(Col A B C). eapply STl6_16_1b with H;finish.
  tauto.
  assert_all.
  assert(~ Col H D A);Col.
  assert(Midpoint C D A);finish.
  assert(Par H D I C). assert(Par B E I C). apply par_symmetry;auto. eapply par_trans with B E;auto.
  assert(Col I H A);Col. 
  assert(Midpoint I H A).
  apply triangle_par_mid with D C;auto.
  apply l7_2;auto.
Qed.

Lemma SegmTrisect17:
forall A B C D E H I,
~ Col A B C -> Midpoint C A D -> Midpoint D C E -> Col H A B -> Par D H B E ->
Par C I B E -> Midpoint I A H -> A <> H.
Proof.
  intros.
  intro.
  subst.
  assert(Col C H D);finish. 
  assert(I = H). 
  apply l7_3;auto. subst.
  assert_all.
  assert(Col D C H);finish.
  assert(Col D C E);Col.
  assert(Col D H E). eapply STl6_16_1b with C;finish.
  assert(~ Col B H D). intro. assert(Col H D B);Col. assert(Col H D C);Col.
  assert(Col H B C). apply STl6_16_1b with D;auto. auto.
  assert(Inter H D B E E). unfold Inter.
  split;auto.
  split.
  assert(Col B B E);Col.
  exists B;auto.
  split;Col.
  assert(~ Par H D B E). apply inter__npar with E;auto. 
  auto.
Qed.

Lemma SegmTrisect18:
forall A B C D E H I,
~ Col A B C -> Midpoint C A D -> Midpoint D C E -> Col H A B ->
Par D H B E -> Par C I B E -> Midpoint I A H ->
Midpoint H I B.
Proof.
  intros.
  assert_all.
  assert(Par C I B E). apply par_left_comm;auto.
  assert(Par D H B E). apply par_left_comm;auto.
  assert(Col H A B);Col.
  assert(A <> H). eapply SegmTrisect17 with B C D E I;auto.
  assert(B <> I). intro. subst. assert(Col C I E). apply par_abbc;auto.
                  assert(Col C D A);Col.
    assert(Col C D E);Col.
    assert(Col C A E). eapply STl6_16_1b with D;auto.
    assert(Col C E A);Col.
    assert(Col C E I);Col.
    assert(Col C A I). eapply STl6_16_1b with E;auto.
    assert(Col A I C);Col. auto.
  eapply sesamath_4ieme_G2_ex47 with C D E.
  + assert(~ Col E C B). apply SegmTrisect08 with A D;finish. Col.
  + intro.
  assert(Col A H I);auto.
  assert(Col A H B);Col.
  assert(Col A I B).
  eapply STl6_16_1b with H;auto. Col.
  assert(Col B I A);Col.
  assert(Col B I C);Col.
  assert(Col B A C). eapply STl6_16_1b with I;auto.
  Col.
  + assert(Col H A I);Col. assert(Col H A B);Col.
  eapply STl6_16_1b with A;auto.
  + auto.
  + assert(Par B E D H). apply par_symmetry;auto. apply par_trans with B E;auto.
  + apply par_right_comm;auto.
Qed.

Lemma SegmTrisect19:
forall A B, 
A <> B -> exists C, exists D, A <> D /\ Midpoint C A D /\ Midpoint D C B.
Proof.
  intros.
  assert(exists C, ~ Col A B C). apply SegmTrisect01;auto. destruct H0 as [C].
  assert(exists D, Midpoint C A D /\ A <> D). apply SegmTrisect02 with B;auto. destruct H1 as [D]. spliter.
  assert(exists E, Midpoint D C E). eapply SegmTrisect04 with A B;auto. destruct H3 as [E].
  assert(B <> E). eapply SegmTrisect05 with A C D;auto.
  assert(exists F, exists G, Col D F G /\ Par F G E B). eapply SegmTrisect09;auto. destruct H5 as [F H5]. destruct H5 as [G].
  assert_all.
    assert(~ Col B A E).
  intro.
  assert(Col A C E). eapply SegmTrisect07 with B D;auto. assert(Col A E C);Col.
  assert(Col A E B);auto. 
  assert(Col A B C). eapply STl6_16_1b with E;finish.
  apply SegmTrisect06 with B C D;auto.
  Col.
  assert(Col A C B). eapply STl6_16_1b with E;finish. eapply SegmTrisect06 with B C D;auto. Col.
  assert(~ Par F G A B).
  apply SegmTrisect10 with D E; finish.
  assert(exists H, Col H F G /\ Col H A B). eapply not_par_inter_exists; auto.
  destruct H8 as [HH]. spliter.
  assert(D <> HH). apply SegmTrisect11 with A B C; finish.
  assert(Par D HH E B). apply SegmTrisect12 with F G;auto.
  assert(exists I, Midpoint I A HH). eapply midpoint_existence.
  destruct H18 as [I].
  assert(Col I A HH);finish.
  assert(Par C I B E). apply SegmTrisect13 with A D HH;finish.
  assert(Par D HH B E). apply par_right_comm;auto.
  assert(A = HH -> Midpoint I A HH). 
  intro.
  apply SegmTrisect15 with B C D E; auto.
  assert(A <> HH -> Midpoint I A HH).
  intro.
  apply SegmTrisect16 with B C D E;auto.
  assert(Midpoint I A HH). auto.
  assert(A <> HH). eapply SegmTrisect17 with B C D E I;auto.
  assert(Midpoint HH I B).
  apply SegmTrisect18 with A C D E;finish.
  exists I.
  exists HH.
  auto.
Qed.

Lemma SegmTrisect20:
forall A B C D, 
A <> B -> Midpoint C A D -> Midpoint D C B -> C <> D.
Proof.
  intros.
  intro.
  subst.
  assert_all.
  tauto.
Qed.

Lemma SegmTrisect21: 
forall A B C D, 
A <> B -> Midpoint C A D -> Midpoint D C B -> Bet_4 A C D B.
Proof.
  intros.
  assert(C <> D). apply SegmTrisect20 with A B;auto.
  unfold Bet_4.
  unfold Midpoint in H0.  
  unfold Midpoint in H1. 
  spliter.
  split.
  assumption.
  split.
  assumption.
  assert(HH:Bet A D B).
  apply outer_transitivity_between2 with C;auto.
  split.
  apply HH.  
  apply outer_transitivity_between with D;auto.
Qed.

(*************)
(* Existence *)
(*************)

Theorem SegmTrisectExistence:
forall A B,
exists C, exists D, Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B.
Proof.
  intros.
    induction (eq_dec_points A B).
    exists A. exists B. assert_all. split. 
    unfold Bet_4. split;finish.
    split;finish.
    assert(exists C, exists D, A <> D /\ Midpoint C A D /\ Midpoint D C B).
  apply SegmTrisect19;auto.
  destruct H0 as [C [D]]. spliter.
  exists C.
  exists D.
  split.
  unfold Bet_4. split;finish.
  split;finish.
  split;finish.
  unfold Midpoint in H1. destruct H1.
  unfold Midpoint in H2. destruct H2.
  apply outer_transitivity_between2 with C;auto.
  assert(C <> D). intro. subst. 
    assert(D = B). CongR. subst. 
    assert(A = B). CongR. tauto. auto.
  unfold Midpoint in H1. destruct H1.
  unfold Midpoint in H2. destruct H2.
  apply outer_transitivity_between with D;finish. 
  assert(C <> D). intro. subst. 
    assert(D = B). CongR. subst. 
    assert(A = B). CongR. tauto. auto.
  split; finish.
Qed.

(**************)
(* Uniqueness *)
(**************)

Lemma SegmTrisect22:
forall A B C D, A <> B ->
Midpoint C A D -> Midpoint D C B -> A <> D /\ Col A B C.
Proof.
  intros.
  split. 
  intro. subst.
  assert(C = D). apply l7_3;auto. subst. 
  assert(D = B). apply is_midpoint_id;auto. tauto.
  assert(Col C D A). Col.
  assert(Col C D B). Col.
  assert(Col C A B).
  apply STl6_16_1b with D;auto.
  + intro. subst. assert(D = B). apply is_midpoint_id;auto. 
  assert(D = A). apply is_midpoint_id_2;auto. 
  assert(A = B). subst. tauto. tauto.
  + Col.
Qed.

Lemma SegmTrisect23:
forall A B C D E F, 
A <> B -> ~ Col A B E -> Midpoint E A F -> Midpoint C A D -> Midpoint D C B ->
Par F D E C.
Proof.
  intros.
  assert_all.
  assert(~ Col F A B).
  { 
    intro.
    assert(Col A F E);finish.
    assert(Col A F B);finish.
    assert(Col A E B). eapply STl6_16_1b with F;auto. Col.
  }
  assert(~ Col D F A).
  {
    intro.
    assert(Col A F D);Col.
    assert(Col A F E);Col.
    assert(Col A D E). eapply STl6_16_1b with F;auto. Col.
    assert(Col D C B);finish.
    assert(Col D C A);finish.
    assert(Col D A B). eapply STl6_16_1b with C;auto. 
    intro. subst.
    assert(C = A). apply is_midpoint_id_2;auto.
    assert(C = B). eapply is_midpoint_id;auto.
    subst. auto.
    assert(Col A D B);Col.
    assert(Col A B E). eapply STl6_16_1b with D;auto.
    eapply SegmTrisect22 with B C;auto. Col.
  }
  assert(F <> D). intro. subst. finish. 
  assert(Midpoint C D A);finish.
  assert(Midpoint E F A);finish.
  assert(~ Col F D A). Col.
  assert(Par F D E C).
  apply (triangle_mid_par F D A C E). auto. auto. auto. auto.
Qed.

Lemma SegmTrisect24:
forall A B C D C' D' B', 
A <> B -> ~ Col A B C'-> Midpoint C A D -> Midpoint D C B ->
Midpoint C' A D' -> Midpoint D' C' B' -> ~Par_strict C' B D D'.
Proof.
  intros.
  assert(Par D' D C' C).
  eapply SegmTrisect23 with A B;finish.
  assert_all.
  assert(Coplanar C' B D D').
    unfold Coplanar.
    assert(Col C' D' A). Col.
    assert(B <> D).
       intro. subst. assert(D = C). eapply is_midpoint_id_2;auto. subst. assert(C = A). eapply is_midpoint_id_2;auto. auto.
  assert_all.
  assert(Col D A B).
     assert(Col D C A). Col.
     assert(Col D C B). Col.
     eapply STl6_16_1b with C;finish. 
  assert(Col B D A). Col.
  assert(Col C' D' A);finish.
  exists A. auto.
  intro.
  assert(Par C' B D D'). apply (par_strict_par);auto.
  assert(Par C' B C' C). apply par_trans with D D';auto.
  assert(Col C' B C). apply par_id;auto.
  assert_all. 
  assert(Col B C C');Col.
  assert(Col C A B).
  assert(Col C D A);Col.
  assert(Col C D B);Col.
  apply STl6_16_1b with D;finish. Col.
  assert(Col B C A);Col.
  assert(Col B C' A). eapply STl6_16_1b with C;auto.
  Col.
Qed.

Lemma SegmTrisect25:
forall A B C D C' D' B', A <> B -> ~ Col A B C'-> 
Midpoint C A D -> Midpoint D C B ->
Midpoint C' A D' -> Midpoint D' C' B' ->
Par D' D B' B /\ Par C' C B' B.
Proof.
  intros.
  assert(C <> A). 
    intro. subst. assert(A = D). eapply is_midpoint_id;auto. subst. assert(D = B). apply is_midpoint_id. auto. auto. 
  assert_all.
    assert(Col C A B). 
    assert(Col C D A);Col.
    assert(Col C D B);Col.
    eapply STl6_16_1b with D; finish. 
  assert(Par D' D C' C).
  apply SegmTrisect23 with A B;finish.
  assert_all.
  assert(Coplanar C' B D D').
    unfold Coplanar.
    assert(Col C' D' A). Col.
    assert(B <> D).
     intro. subst. assert(D = C). eapply is_midpoint_id_2;auto. subst. assert(C = A). eapply is_midpoint_id_2;auto. auto.
  assert_all.
  assert(Col D A B).
     assert(Col D C A). Col.
     assert(Col D C B). Col.
     eapply STl6_16_1b with C;finish. 
  assert(Col B D A). Col.
  assert(Col C' D' A);finish.
  exists A. auto.
  assert(~ Par_strict C' B D D').
  apply SegmTrisect24 with A C B';auto.
  assert(exists X, Col X C' B /\ Col X D D'). eapply cop_npars__inter_exists;auto.
  destruct H9 as [X].
  destruct H9.
  auto.
  assert(Midpoint X B C').
    assert(Par D' D C' C). apply par_left_comm;auto.
  assert(Par C' C D' D). apply par_symmetry;auto.
  assert(Col D D' X). Col.
  assert(D <> X).
    intro. subst. assert(Col B X C');Col. 
      assert(C <> X). intro. subst. assert(X = A). eapply is_midpoint_id_2;auto. assert(X = B). eapply is_midpoint_id;auto. subst. subst. assert(Col B B C');Col.  
        assert(B <> X). intro. subst. assert(X = C). assert(Cong X X X C);Cong. apply cong_reverse_identity with X;auto. Col.
      assert(Col B X A).
        assert(Col X C A);Col.
        assert(Col X C B);Col.
        assert(Col X A B). apply STl6_16_1b with C;finish. Col.
        assert(Col B C' A). apply STl6_16_1b with X;auto.
        assert(Col A B C');Col. 
  assert(~ Col C' B C). 
  intro. 
  assert(Col B C A). Col.
  assert(Col B C C'). Col.
  assert(Col B A C'). apply STl6_16_1b with C;finish. Col.
  assert(~ Col C C' B). Col.
  assert(Midpoint D B C);finish.
  assert(Par C C' D D'). apply par_symmetry. apply par_left_comm. apply par_symmetry. apply par_left_comm. auto.
  assert(Par C C' D X). apply par_col_par with D'; auto. 
  assert(Par D X C C'). apply par_symmetry. auto.
  assert(Par X D C' C). apply par_left_comm. apply par_symmetry. auto.  apply par_left_comm. auto.
  assert(~ Col C' C B). Col.
  assert(Midpoint D C B). auto.
  assert(Par C' C X D). apply par_symmetry. auto.
  assert(Midpoint X C' B).
  apply triangle_par_mid2 with C D; auto. apply l7_2;auto.
  assert(Midpoint D' B' C'). apply l7_2;auto.
  assert(~ Col B' B C'). 
  intro. 
  assert(Col C' B' A).
      assert(C' <> D'). intro. subst.
        assert(D' = B'). apply is_midpoint_id;auto.
        assert(D' = A). apply is_midpoint_id_2;auto.
        subst. subst. auto.
    assert(Col C' D' A);finish.
    assert(Col C' D' B');finish.
    eapply STl6_16_1b with D';auto. Col.
  assert(Col C' B' B). Col.
  assert(Col C' A B). apply STl6_16_1b with B';auto. Col.
  assert(Midpoint X B C');auto.
  assert(Midpoint D' B' C');auto.
  assert(Par_strict B' B D' X).
(* WARNING GeoCoq.Tarski_dev.Ch13_1. *)
  apply GeoCoq.Tarski_dev.Ch13_1.triangle_mid_par with C';auto.
(* WARNING GeoCoq.Tarski_dev.Ch13_1. *)
  assert(Par B' B D' X). apply par_strict_par;auto.
  assert(Col D' X D). Col.
  assert(Par B' B D' D). apply par_col_par with X;auto.
  assert(Par D' D B' B).
  apply par_symmetry. auto.
  assert(Par C' C B' B).
  assert(Par D' D C' C). apply par_left_comm;auto.
  assert(Par C' C D' D). apply par_symmetry;auto.
  apply par_trans with D' D;auto.
  tauto.
Qed.

Lemma SegmTrisect26: 
forall A B C D C' D', 
A <> B -> Midpoint C A D -> Midpoint D C B ->
Midpoint C' A D' -> Midpoint D' C' B -> C = C'.
Proof.
  intros.
  assert(exists E, ~ Col A B E). apply SegmTrisect01;auto.
  destruct H4 as [E].
  assert(exists F, Midpoint E A F /\ A <> F). apply SegmTrisect02 with B;auto.
  destruct H5 as [F]. spliter.
  assert_all.
  assert(Par F D E C). apply SegmTrisect23 with A B;auto.
  assert(Par F D' E C'). apply SegmTrisect23 with A B;auto.
  assert(~ Col E B F).
    intro. 
    assert(Col E F B); Col.
    assert(Col E F A); finish.
    assert(Col E B A). apply STl6_16_1b with F;finish. Col.
  assert(exists G, Midpoint F E G /\ E <> G). apply SegmTrisect02 with B;auto.
  destruct H10 as [G]. spliter.
  assert(Par F D G B /\ Par E C G B). apply SegmTrisect25 with A;finish.
  assert(Par F D' G B /\ Par E C' G B). apply SegmTrisect25 with A;finish.
  spliter.
  assert(Par E C E C'). apply par_trans with G B;auto. apply par_symmetry;auto.
  assert(Col E C C'). apply par_id;auto.
  assert(C <> C' -> False). intro. 
    assert(Col E A B).
      assert(Col C A B).
        assert(C <> D). intro. subst. assert(D = B). apply is_midpoint_id;auto. assert(D = A). apply is_midpoint_id_2;auto. subst. Col.
        assert(Col C D A);finish.
        assert(Col C D B);finish.
        apply STl6_16_1b with D;auto.
      assert(Col C' A B).
        assert(C' <> D'). intro. subst. assert(D' = B). apply is_midpoint_id;auto. assert(D' = A). apply is_midpoint_id_2;auto. subst. Col.
        assert(Col C' D' A);finish.
        assert(Col C' D' B);finish.
        apply STl6_16_1b with D';auto.
  ColR.
  Col.
  induction(eq_dec_points C C').
  auto.
  tauto.
Qed.

Lemma SegmTrisect27: 
forall A B C D C' D', 
A <> B -> Midpoint C A D -> Midpoint D C B -> Midpoint C' A D' -> 
Midpoint D' C' B -> D = D'.
Proof.
  intros.
  assert(V1: C = C').
  apply SegmTrisect26 with A B D D'. apply H. apply H0. apply H1. apply H2. apply H3. 
  subst.
  eapply symmetric_point_uniqueness with A C';auto.
Qed.

Lemma SegmTrisect28: 
forall A B C D C' D', 
A <> B -> Midpoint C A D -> Midpoint D C B ->
Midpoint C' A D' -> Midpoint D' C' B -> (C = C' /\ D = D').
Proof.
  intros. split. 
  apply SegmTrisect26 with A B D D';auto.
  apply SegmTrisect27 with A B C C';auto.
Qed.

Theorem SegmTrisectUniqueness:
forall A B C D C' D', 
Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B /\
Bet_4 A C' D' B /\ Cong A C' C' D' /\ Cong C' D' D' B ->
(C = C' /\ D = D').
Proof.
  intros. spliter.
  induction(eq_dec_points A B).
  subst. split.
  assert(B = C /\ B = D).
  eapply Bet4Equal. auto. 
  assert(B = C' /\ B = D').
  eapply Bet4Equal. auto. 
  spliter.
  eapply eq_trans with B;auto.
  assert(B = C /\ B = D).
  apply Bet4Equal. auto. 
  assert(B = C' /\ B = D').
  eapply Bet4Equal. auto. 
  spliter.
  apply eq_trans with B;auto.
  eapply SegmTrisect28 with A B;finish.
  unfold Bet_4 in H. spliter. 
  unfold Bet_4 in H2. spliter.
  unfold Midpoint. split;auto.
  unfold Bet_4 in H. spliter.
  unfold Bet_4 in H2. spliter.
  unfold Midpoint. split;auto.
  unfold Bet_4 in H. spliter.
  unfold Bet_4 in H2. spliter.
  unfold Midpoint. split;auto.
  unfold Bet_4 in H. spliter.
  unfold Bet_4 in H2. spliter.
  unfold Midpoint. split;auto.
Qed.

(********)
(* Main *)
(********)

Theorem SegmTrisectExistenceUniqueness:
forall A B, 
exists! C D, Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B.
Proof.
  intros.
  assert(exists C, exists D, Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B).
  apply SegmTrisectExistence.
  destruct H as [C [D]]. spliter.
  exists C. 
  unfold unique. split.
  exists D. split. auto.
  intros. spliter.
  eapply SegmTrisectUniqueness.
  split. apply H. split. apply H0. split. apply H1. split. apply H2. split; finish.
  intros.
  destruct H2 as [E].
  spliter.
  assert(C = x' /\ D = E).
  eapply SegmTrisectUniqueness. split. apply H. split;finish.
  tauto.
Qed.

(**********************)
(* Segment_Trisection *)
(**********************)

Definition TwoThirds T A B := Bet A T B /\ (forall M, Midpoint M A T -> Cong A M T B).

Lemma SegmTrisect29: 
forall A,
TwoThirds A A A.
Proof.
  intro.
  unfold TwoThirds.
  split.
  Between.
  intros.
  assert(M = A).
  assert_all. auto. subst.
  Cong.
Qed.

Lemma SegmTrisect30: 
forall A B,
TwoThirds A B A -> A = B.
Proof.
  intros.
  unfold TwoThirds in H. spliter.
  Name M the midpoint of B and A.
  assert(Cong B M A A). apply H0. apply H2.
  assert_all. auto.
Qed.

Lemma SegmTrisect31: 
forall A B,
TwoThirds A A B -> A = B.
Proof.
  intros.
  unfold TwoThirds in H. spliter.
  assert(Midpoint A A A). apply l7_3_2.
  assert(Cong A A A B). apply H0. apply H1.
  assert_all. auto.
Qed.

Lemma SegmTrisect32: 
forall A B,
TwoThirds B A B -> A = B.
Proof.
  intros.
  unfold TwoThirds in H. spliter.
  Name M the midpoint of A and B.
  assert(Cong A M B B). apply H0. apply H2.
  assert_all. auto.
Qed.

Lemma SegmTrisectTwoThirdsExistence:
forall A B,
exists T, TwoThirds T A B. 
Proof.
  intros.
  assert (exists C D,  Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B).
  apply SegmTrisectExistence.
  destruct H as [D[C]]. spliter.
  exists C. split. 
  unfold Bet_4 in H. spliter. apply H3.
  intros.
  assert(Midpoint D A C).
  unfold Midpoint.
  split.
  unfold Bet_4 in H. spliter. apply H.
  apply H0.
  assert(M = D). apply l7_17 with A C; finish.
  subst. 
  CongR.
Qed.

Lemma SegmTrisectTwoThirdsUniqueness:
forall A B C D,
TwoThirds C A B -> TwoThirds D A B -> C = D. 
Proof.
  intros.
  unfold TwoThirds in *. spliter.
  Name M1 the midpoint of A and C.
  Name M2 the midpoint of A and D.
  unfold Midpoint in *. spliter.
  assert(Bet A M1 C). Between.
  assert(Bet M1 C B). apply between_exchange3 with A;auto.
  assert(Bet A C B). auto.
  assert(Bet A M1 B). apply between_exchange4 with C; auto.
  assert(Bet A M2 D). Between.
  assert(Bet M2 D B). apply between_exchange3 with A;auto.
  assert(Bet A D B). auto.
  assert(Bet A M2 B). apply between_exchange4 with D; auto.
  assert(Cong A M1 C B). apply H2.
  split; auto. 
  assert(Cong A M2 D B). apply H1.
  split;auto.
  assert(Bet_4 A M1 C B). unfold Bet_4. repeat split;auto. 
  assert(Bet_4 A M2 D B).
  unfold Bet_4. repeat split;auto. 
  assert(Bet A M2 D /\ Cong A M2 M2 D).
  split;auto. 
  assert(Bet A M1 C /\ Cong A M1 M1 C).
  split;auto.
  eapply SegmTrisectUniqueness. split. apply H17. split. auto. 
  split.
  assert(Cong M1 C C B). apply cong_inner_transitivity with A M1.
  apply H6. apply H15. auto.
  assert(Bet_4 A M2 D B).
  unfold Bet_4. repeat split;auto. 
  split.
  apply H21. split. 
  assert(Cong A M2 M2 D). CongR. auto. CongR.
Qed.



Ltac twothirds MM A B :=
 let T:= fresh in assert (T:= SegmTrisectTwoThirdsExistence A B);
ex_and T MM.

Tactic Notation "Name" ident(T) "the" "twothirds" "of" ident(A) "and" ident(B) :=
 twothirds T A B.

Definition DoubleTwoThirds D A B := Col A B D /\ (forall TT, TwoThirds TT A B -> Midpoint TT A D).

Lemma SegmTrisect33: 
forall A B,
DoubleTwoThirds B A A -> A = B.
Proof.
  intros.
  unfold DoubleTwoThirds in H. spliter.
  assert(TwoThirds A A A).
  apply SegmTrisect29.
  assert(Midpoint A A B).
  apply H0. apply H1.
  assert_all. auto. 
Qed.


Lemma SegmTrisect34: 
forall A,
exists B, DoubleTwoThirds B A A.
Proof.
  intro.
  exists A.
  unfold DoubleTwoThirds.
  split.
  Col.
  intros.
  unfold TwoThirds in H.
  spliter.
  assert_all.
  finish.
Qed.

Lemma SegmTrisectDoubleTwoThirdsExistence:
forall A B, 
exists D, DoubleTwoThirds D A B.
Proof.
  intros.
  induction (eq_dec_points A B).
  subst. apply SegmTrisect34.
  Name X the twothirds of A and B.
  assert(A <> X). intro. subst. 
  assert(X = B). apply SegmTrisect31. tauto. tauto.
  double A X TT.
  unfold DoubleTwoThirds.
  exists TT.
  split.
  assert(Col A B TT).
  unfold TwoThirds in H1. spliter.
  assert(Col A X TT). Col.
  assert(Col A X B). Col.
  apply STl6_16_1b with X;finish.
  auto.
  intros.
  assert(X = TT0). apply SegmTrisectTwoThirdsUniqueness with A B; auto. 
  subst.
  auto.
Qed.


Ltac doubletwothirds MM A B :=
 let T:= fresh in assert (T:= SegmTrisectDoubleTwoThirdsExistence A B);
ex_and T MM.

Tactic Notation "Name" ident(T) "the" "doubletwothirds" "of" ident(A) "and" ident(B) :=
 doubletwothirds T A B.

Theorem PentatonicPythagoreScale:
forall A B,
exists FONDAMENTAL N1 N2 N3 N4 OCTAVE,
FONDAMENTAL = B         /\ 
TwoThirds       N3 A B  /\ 
DoubleTwoThirds N1 A N3 /\
TwoThirds       N4 A N1 /\ 
DoubleTwoThirds N2 A N4 /\
Midpoint OCTAVE A B.
Proof.
  intros.
  Name N3 the twothirds of       A and B.
  Name N1 the doubletwothirds of A and N3.
  Name N4 the twothirds of       A and N1.
  Name N2 the doubletwothirds of A and N4.
  Name M the midpoint of         A and B.
  exists B.
  exists N1. 
  exists N2.
  exists N3.
  exists N4.
  exists M.
  split. auto.
  split. auto.
  split. auto. 
  split. auto. 
  split. auto. 
  auto.
Qed.

Theorem PentatonicPythagoreScaleTwoOctave:
forall A B,
exists FONDAMENTAL N1 N2 N3 N4 OCTAVE N5 N6 N7 N8 OCTAVE2,
FONDAMENTAL = B                   /\
TwoThirds       N3 A FONDAMENTAL  /\
DoubleTwoThirds N1 A N3           /\
TwoThirds       N4 A N1           /\
DoubleTwoThirds N2 A N4           /\
Midpoint OCTAVE A B               /\
TwoThirds       N7 A OCTAVE       /\
DoubleTwoThirds N5 A N7           /\
TwoThirds       N8 A N5           /\
DoubleTwoThirds N6 A N8           /\
Midpoint OCTAVE2 A OCTAVE.
Proof.
  intros.
  Name N3 the twothirds of       A and B. 
  Name N1 the doubletwothirds of A and N3.
  Name N4 the twothirds of       A and N1.
  Name N2 the doubletwothirds of A and N4.
  Name M the midpoint of         A and B.
  Name N7 the twothirds of       A and M. 
  Name N5 the doubletwothirds of A and N7.
  Name N8 the twothirds of       A and N5.
  Name N6 the doubletwothirds of A and N8.
  Name M2 the midpoint of        A and M.

  exists B.
  exists N1. 
  exists N2.
  exists N3.
  exists N4.
  exists M.
  exists N5. 
  exists N6.
  exists N7.
  exists N8.
  exists M2.

  split. auto.
  split. auto.
  split. auto. 
  split. auto. 
  split. auto. 
  split. auto. 
  split. auto. 
  split. auto. 
  split. auto. 
  split. auto. 
  auto.
Qed.

End Segment_Trisection.
