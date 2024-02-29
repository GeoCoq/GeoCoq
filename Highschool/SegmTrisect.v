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



Bibliograpy:
============
[1] http://villemin.gerard.free.fr/Pavage/Dissecti/Trissect.htm#classi (14/09/2019).

*)

Require Export sesamath_exercises.

Section Segment_Trisection.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

(*************)
(* Existence *)
(*************)

Theorem SegmTrisectExistence:
forall A B,
exists C, exists D, Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B.
Proof.
  assert(LEM1:forall A B D E F G,  ~ Col B A E -> Col D F G -> 
              Par F G E B -> ~ Par F G A B).
  {
   intros A0 B0 D0 E0 F0 G0. 
   intros.
   intro. 
   assert_all.
   assert(Par E0 B0 G0 F0). Par. 
   assert(Par E0 B0 A0 B0) by (apply par_trans with G0 F0; auto).
   assert(Par B0 A0 B0 E0);finish.
   assert(Col B0 A0 E0). ColR. ColR.
   }

  intros.
  induction (eq_dec_points A B).
  - exists A. exists B. assert_all. split;finish. unfold Bet_4. split;finish.
  - assert(exists C, exists D, A <> D /\ Midpoint C A D /\ Midpoint D C B).
    {
     intros.
     assert(exists C, ~ Col A B C) by (apply not_col_exists; assumption).
     destruct H0 as [C].
     Name D the symmetric of A wrt C.
     Name E the symmetric of C wrt D.
     assert(B <> E). {intro. subst. assert(Col A C E). ColR. ColR. } 
     assert(exists F, exists G, Col D F G /\ Par F G E B).
     {
      intros. 
      assert(exists F, exists G, F<>G /\ Par E B F G /\ Col D F G) by (apply parallel_existence; auto).
      destruct H4 as[F [G]]. spliter.  
      exists F. exists G. Par.
     }
     destruct H4 as [F H5]. 
     destruct H5 as [G].
     assert_all.
     assert(A <> E). 
     { 
      intro. subst. 
      assert(Cong C E D E). CongR. 
      assert(C = D) by (apply between_cong with E;finish). 
      CongR.
     }
     assert(~ Col B A E).
     {
      intro.
      assert(Col A C E) by (apply l6_16_1 with D;finish).
      assert(Col A E C);Col.
      assert(Col A E B). 
      {
       assert(Col A B C). ColR.  
       Col.
      }
      assert(Col A C B). ColR. 
      Col.
     } 
     assert(~ Par F G A B).
     {
      intro. 
      assert_all. 
      assert(Par E B G F). Par.
      assert(Par E B A B) by (apply par_trans with G F;assumption).
      assert(Par B A B E);finish.
      assert(Col B A E). ColR. 
      ColR.
     }
     assert(exists H, Col H F G /\ Col H A B) by (apply not_par_inter_exists; auto).
     destruct H14 as [HH]. 
     spliter.
     assert(D <> HH).
     {
      intro.
      subst. 
      assert(Col B A C). ColR. 
      Col.
     }
     assert(Par D HH E B). 
     { 
      assert(Par E B F G). Par. 
      assert(Par E B D HH). 
      {
       apply par_col2_par with F G. 
       assumption. 
       assumption. 
       Col. 
       Col. 
      }
      Par.
     }
     assert(exists I, Midpoint I A HH). apply midpoint_existence.
     destruct H19 as [I].
     assert(Col I A HH);finish.
     assert(Par C I B E).
     {
      assert(Midpoint C D A);finish.
      assert(Midpoint I HH A);finish;
      assert(Par D HH C I) by (apply triangle_mid_par with A; finish).
      apply par_trans with D HH.
      + apply par_symmetry; auto.
      + Par.
     }
     assert(Par D HH B E). Par.
     assert(A <> HH). 
     {
      intro.
      subst.
      assert(Col C HH D);finish. 
      assert(I = HH) by (apply l7_3;auto). 
      subst.
      assert_all.
      assert(Col D C HH);finish.
      assert(Col D C E);Col.
      assert(Col D HH E). ColR. 
      assert(~ Col B HH D). 
      {
       intro. 
       assert(Col HH D B);Col. 
       assert(Col HH D C);Col.
       assert(Col HH B C). ColR.
       auto.
      }
      assert(Inter HH D B E E). 
      {
       unfold Inter.
       split;auto.
       split.
       assert(Col B B E);Col.
       exists B;auto.
       split;Col.
      }
      assert(~ Par HH D B E) by (apply inter__npar with E;auto). 
      Par.
     }
     assert(Midpoint I A HH);finish.
     assert(Midpoint HH I B).
     { 
      assert_all.
      assert(Par C I B E). Par. 
      assert(Par D HH B E). Par. 
      assert(Col HH A B);Col.
      assert(A <> HH). 
      {
       intro.
       subst. 
       assert(Col C HH D);finish.
      }
      assert(B <> I).
      {
       intro. 
       subst. 
       assert(Col A I C). ColR.
       Col.
      }
      auto.
      apply sesamath_4ieme_G2_ex47 with C D E.
      + assert(~ Col E C B). intro. assert(Col A B C); ColR. ColR. 
      + intro.
        assert(Col B A C). ColR.
        Col.
      + ColR. 
      + auto.
      + assert(Par B E D HH). Par. 
        apply par_trans with B E; auto. 
      + Par.  
     }
     exists I.
     exists HH.
     auto.
    }
    destruct H0 as [C [D]].
    exists C. 
    exists D.
    spliter.
    split.
    unfold Bet_4. 
    split;finish.
    split;finish.
    split;finish.
    unfold Midpoint in H1. 
    destruct H1.
    unfold Midpoint in H2. 
    destruct H2.
    apply outer_transitivity_between2 with C;auto.
    assert(C <> D).
    {
     intro. 
     subst. 
     assert(D = B). CongR. 
     subst. 
     assert(A = B). CongR. tauto.
    }
    auto.
    unfold Midpoint in H1. 
    destruct H1.
    unfold Midpoint in H2. 
    destruct H2.
    apply outer_transitivity_between with D;finish. 
    assert(C <> D). 
    {
     intro. subst. 
     assert(D = B). CongR. 
     subst. 
     assert(A = B). CongR. tauto. 
    }
    auto.
    split; finish.
Qed.

Theorem SegmTrisectUniqueness:
forall A B C D C' D', 
Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B /\
Bet_4 A C' D' B /\ Cong A C' C' D' /\ Cong C' D' D' B ->
(C = C' /\ D = D').
Proof.
  assert(LEM0: forall A B C D C' D', A <> B -> Midpoint C A D -> 
               Midpoint D C B -> Midpoint C' A D' -> Midpoint D' C' B -> 
               (C = C' /\ D = D')).
 {
  assert(LEM1: forall A B C D C' D', 
               A <> B -> Midpoint C A D -> Midpoint D C B ->
               Midpoint C' A D' -> Midpoint D' C' B -> C = C').
  {
   assert(LEM2: forall A B C D C' D' B', A <> B -> ~ Col A B C'-> 
                Midpoint C A D -> Midpoint D C B ->
                Midpoint C' A D' -> Midpoint D' C' B' ->
                Par D' D B' B /\ Par C' C B' B).
   {
    assert(LEM3: forall A B C D C' D' B', 
                 A <> B -> ~ Col A B C'-> Midpoint C A D -> Midpoint D C B ->
                 Midpoint C' A D' -> Midpoint D' C' B' -> ~Par_strict C' B D D').
    {
     intros.
     assert(Par D' D C' C).
     {
      assert(~ Col D D' A).
      {
       intro.
       assert(Col A D C'). ColR. Col. 
       assert(A <> D).  
       {
        intro. 
        subst. 
        ColR.
       }
       assert(Col D A B). ColR.  
       assert(Col A B C'). ColR. 
       Col.
      }
      apply (triangle_mid_par D' D A C C'). 
      assert(D' <> D). 
      {
       intro. 
       subst. 
       assert(Col A D C'). ColR. 
       Col. 
      }   
      auto. 
      assert(Midpoint C D A) by (apply l7_2;auto). 
      auto.
      assert(Midpoint C' D' A) by (apply l7_2;auto). 
      auto.
     }
     assert_all.
     assert(Coplanar C' B D D'). Cop.
     intro.
     assert(Par C' B D D') by (apply (par_strict_par);auto).
     assert(Par C' B C' C) by (apply par_trans with D D';auto).
     assert(Col C' B C) by (apply par_id;auto).
     assert(Col B C' A). ColR. 
     Col.
    }
    intros.
    assert(C <> A). 
    {
     intro. 
     subst. 
     assert(A = D). ColR. 
     subst. 
     assert(D = B). ColR.
     tauto.
    }
    assert_all.
    assert(Col C A B). ColR.
    assert(Par D' D C' C).
    {
     assert(~ Col D D' A).
     {
      intro.
      assert(Col A D C'). ColR. 
      assert(A <> D). ColR.  
      assert(Col D A B). ColR.   
      assert(Col A B C'). ColR. 
      Col.
     }
     apply (triangle_mid_par D' D A C C'). 
     + intro. 
       subst. 
       assert(Col A D C'). ColR. 
       Col.  
     + apply l7_2;auto. 
     + apply l7_2;auto.
    }
    assert_all.
    assert(Coplanar C' B D D'). Cop.
    assert(~ Par_strict C' B D D') by (apply LEM3 with A C B';auto).
    assert(exists X, Col X C' B /\ Col X D D') by (apply cop_npars__inter_exists;auto).
    destruct H9 as [X].
    destruct H9.
    assert(Midpoint X B C').
    {
     assert(Par D' D C' C). Par. 
     assert(Par C' C D' D). Par. 
     assert(Col D D' X). Col.
     assert(D <> X). 
     {
      intro. 
      subst.  
      assert(Col B X C');Col. 
      assert(C <> X).
      { 
       assert_diffs. 
       tauto.
      }
      assert(B <> X).
      {
       assert_diffs.
       auto.
      }
      assert(Col B C' A). ColR. 
      assert(Col A B C');Col.
     } 
     assert(~ Col C' B C).
     {
      intro. 
      assert(Col B A C'). ColR. 
      Col. 
     }
     assert(Par C C' D D'). Par. 
     assert(Par C C' D X) by (apply par_col_par with D'; auto).
     assert(Par D X C C'). Par.
     assert(Par X D C' C). Par. 
     assert(~ Col C' C B). Col.
     assert(Midpoint D C B). auto.
     assert(Par C' C X D) by (apply par_symmetry; auto).
     assert(Midpoint X C' B) by (apply triangle_par_mid with C D; ColR).
     apply l7_2;auto.
    }
    assert(Midpoint D' B' C') by (apply l7_2;auto).
    assert(~ Col B' B C').
    {
     intro. 
     assert(Col C' A B). ColR. 
     Col.
    }
    assert(Midpoint X B C');auto.
    assert(Midpoint D' B' C');auto.
    assert(Par_strict B' B D' X).
(* WARNING GeoCoq.Tarski_dev.Ch13_1. *)
    apply GeoCoq.Tarski_dev.Ch13_1.triangle_mid_par with C';auto.
(* WARNING GeoCoq.Tarski_dev.Ch13_1. *)
    assert(Par B' B D' X); Par. 
    assert(Col D' X D); Col.
    assert(Par B' B D' D). apply par_col_par with X;auto.
    assert(Par D' D B' B); Par.
    assert(Par C' C B' B). 
    {
     assert(Par D' D C' C); Par. 
     assert(Par C' C D' D); Par. 
     apply par_trans with D' D;auto.
    }
    tauto.
   }
   intros.
   assert(exists E, ~ Col A B E) by (apply not_col_exists; assumption).
   destruct H4 as [E].
   Name F the symmetric of A wrt E.
   assert(Par F D E C).
   {
    assert(F <> D). 
    {
     intro. 
     subst. 
     assert(Col A B E). ColR. 
     tauto.  
    } 
    apply triangle_mid_par with A; auto.
    + apply l7_2;auto.
    + apply l7_2;auto. 
   }
   assert(Par F D' E C').
   {
    assert(F <> D'). 
    {
     intro. 
     subst. 
     assert(Col A B E). ColR. 
     tauto.  
    } 
    apply triangle_mid_par with A.
    + auto.
    + apply l7_2;auto. 
    + apply l7_2;auto.
   }
   assert(~ Col E B F).
   {
    intro. 
    assert(Col E B A). ColR. 
    Col.
   }
   Name G the symmetric of E wrt F.
   assert(Par F D G B /\ Par E C G B) by (apply LEM2 with A;finish).
   assert(Par F D' G B /\ Par E C' G B) by (apply LEM2 with A;finish).
   spliter.
   assert(Par E C E C').
   { 
    apply par_trans with G B;auto. 
    Par.
   }
   assert(Col E C C') by (apply par_id;auto).
   assert(C <> C' -> False).
   {
    intro. 
    assert(Col E A B).
    {
     assert(Col C A B). 
     {
      assert(C <> D).
      {
       intro. 
       subst. 
       assert(D = B) by (apply is_midpoint_id;auto).
       assert(D = A) by (apply is_midpoint_id_2;auto). 
       subst. 
       Col.
      }
      assert(Col C D A);finish.
      assert(Col C D B);finish.
      ColR.
     }
     assert(Col C' A B). 
     {
      assert(C' <> D'). 
      {
       intro. 
       subst. 
       assert(D' = B) by (apply is_midpoint_id;auto). 
       assert(D' = A) by (apply is_midpoint_id_2;auto).
       subst. 
       Col. 
      }
      ColR.
     }
     ColR.
    }
    Col.
   }
   induction(eq_dec_points C C').
   + auto.
   + tauto.
  }
  intros. 
  split.
  + apply LEM1 with A B D D';auto.
  + apply LEM1 with B A C C' ;auto;finish.
 }

 intros. 
 spliter.
 induction(eq_dec_points A B).
 + subst. 
   split. 
   unfold Bet_4 in *. 
   spliter.
   assert_all.
   reflexivity.
   unfold Bet_4 in *. 
   spliter.
   assert_all.
   reflexivity.
 + apply LEM0 with A B; finish.
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
  assert(exists C, exists D, Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B) by (apply SegmTrisectExistence).
  destruct H as [C [D]]. 
  spliter.
  exists C. 
  unfold unique. 
  split.
  exists D. 
  split. 
  auto.
  intros. 
  spliter.
  eapply SegmTrisectUniqueness.
  split.
  apply H. 
  split. 
  apply H0. 
  split. 
  apply H1. 
  split. 
  apply H2. 
  split; finish.
  intros.
  destruct H2 as [E].
  spliter.
  assert(C = x' /\ D = E).
  {
   eapply SegmTrisectUniqueness. 
   split. 
   apply H. 
   split;finish.
  }
  tauto.
Qed.

(******************************)
(* First Third - Second Third *)
(******************************)

Definition SecondThird S A B := Bet A S B /\ (forall M, Midpoint M A S -> Cong A M S B).
Definition FirstThird F A B:= Bet A F B /\ (forall S, SecondThird S A B -> Midpoint F A S).

Lemma SegmTrisectSecondThirdExistence:
forall A B,
exists T,SecondThird T A B. 
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

Lemma SegmTrisectSecondThirdUniqueness:
forall A B C D,
SecondThird C A B -> SecondThird D A B -> C = D. 
Proof.
  intros.
  unfold SecondThird in *. spliter.
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


Ltac secondthird S A B :=
 let T:= fresh in assert (T:= SegmTrisectSecondThirdExistence A B);
ex_and T S.

Tactic Notation "Name" ident(T) "the" "second_third" "of" ident(A) "and" ident(B) :=
 secondthird T A B.

Lemma SegmTrisectFirstThirdExistence:
forall A B,
exists F,FirstThird F A B. 
Proof.
  intros.
  assert (exists C D,  Bet_4 A C D B /\ Cong A C C D /\ Cong C D D B).
  apply SegmTrisectExistence.
  destruct H as [C[D]]. spliter.
  exists C. split. 
  unfold Bet_4 in H. spliter. apply H4.
  intros.
  unfold SecondThird in H2;spliter.
  Name M the midpoint of A and S.
  assert(Cong A M S B);auto.
  assert(Cong A M M S);finish.
  assert(Cong M S S B). CongR.
  assert(C = M /\ D = S). 
  {
   assert(Bet_4 A C D B);auto.
   assert(Cong A C C D);auto.
   assert(Cong C D D B);auto.
   assert(Bet_4 A M S B).
   {
    split;finish.
    split. 
    assert(Bet A M S);finish.
    apply between_exchange3 with A;auto.
    split. auto.
    apply between_exchange4 with S;auto.
    finish.
   }
   assert(Cong A M M S);auto.
   assert(Cong M S S B);auto.
   apply SegmTrisectUniqueness with A B.
   split;auto.
  }
  spliter.
  subst.
  auto.
Qed.

Lemma SegmTrisectFirstThirdUniqueness:
forall A B C D,
FirstThird C A B -> FirstThird D A B -> C = D. 
Proof.
  intros.
  unfold FirstThird in *. spliter.
  Name S the second_third of A and B.
  assert(Midpoint C A S);auto.
  assert(Midpoint D A S);auto.
  apply l7_17 with A S;auto.
Qed.

Ltac firstThird F A B :=
 let T:= fresh in assert (T:= SegmTrisectFirstThirdExistence A B);
ex_and F T.

Tactic Notation "Name" ident(T) "the" "second_third" "of" ident(A) "and" ident(B) :=
 secondthird T A B.

End Segment_Trisection.
