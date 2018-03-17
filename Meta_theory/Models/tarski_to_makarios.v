(*   Roland Coghetto, 17 March 2018
     GNU Lesser General Public License v3.0 
     See LICENSE GeoCoq 2.3.0
     
     MODIFY, tarski_to_makarios,v Version GeoCoq 2.3.0
     MOTIVATION:
     in [1] Lemma 5: A' implies (RE)
     CHANGES: {(Point equality decidability),(TE),(IE),(SC),(FS')} |- (RE)
                                                                    i
     in [1] Lemma 6: if (RE) and (TE) holds, then (FS') is equivalent to (FS).
     CHANGES: a) {(RE), (TE),(FS)} |- (FS')
                                    i
              b) {(Point equality decidability), (TE), (IE) (SC), (FS')} |- (FS)
                                                                          i
     SOURCES: 
       [1] Timothy James McKenzie Makarios. A further simplification of 
             Tarski’s axioms of geometry. Note di Matematica, 33(2):123–132, 2013.
       [2] tarski_to_makarios,v GeoCoq 2.3.0
       [3] Mizar Mathematical Library (MML 5.46.1331): 
             gtarski3.miz, Roland Coghetto and Adam Grabowski.
       [4] Tarski Geometry Axioms, part III. 
             R. Coghetto & A. Grabowski. 
             Formalized Mathematics Vol. 25 N° 4, 2017.(In preparation).

     in: Section Tarski83_to_Makarios_variant
         ------------------------------------
     REMOVE: cong_reflexivity, cong_symmetry, cong_left_commutativity.
     MODIFY: five_segment'.

     in: Section Makarios_variant_to_Tarski83
         ------------------------------------
     REMOVE: between_symmetry, Mcong_left_commutativity.
     ADD: LmCoghGrab, cong_pre_pseudo_reflexivity.
     MODIFY: cong_pseudo_reflexivity (Minner_pasch & 
                  Mbetween_identity are not used to
                  prove cong_pseudo_reflexivity)
*)

Require Export GeoCoq.Axioms.tarski_axioms.
(*Require Export GeoCoq.Axioms.makarios_variant_axioms.*)
Require Export GeoCoq.Axioms.makarios_variant_axioms.

(** In this file we formalize the result given in T. J. M. Makarios:
 A further simplification of Tarski's axioms of geometry, June 2013. *)

Section Tarski83_to_Makarios_variant.

Context `{TnEQD:Tarski_neutral_dimensionless}.

Lemma five_segment' : forall A A' B B' C C' D D' : Tpoint,
    Cong A B A' B' ->
    Cong B C B' C' ->
    Cong A D A' D' ->
    Cong B D B' D' ->
    Bet A B C -> Bet A' B' C' -> A <> B -> Cong D C C' D'.
Proof.
  intros.
  assert(Cong C D C' D').
  intros.
  eapply five_segment with A A' B B';assumption.
  assert(Cong C D D C).
  eapply cong_pseudo_reflexivity;eauto.
  apply cong_inner_transitivity with C D;assumption.
Qed.

Lemma lower_dim_ex : 
 exists A B C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists PA.
exists PB. 
exists PC.
apply lower_dim.
Qed.

Instance Makarios_Variant2_follows_from_Tarski : Tarski_neutral_dimensionless_variant.
Proof.
exact (Build_Tarski_neutral_dimensionless_variant
 Tpoint Bet Cong
 cong_identity
 cong_inner_transitivity
 segment_construction
 five_segment'
 between_identity
 inner_pasch
 PA PB PC
 lower_dim).
Qed.

End Tarski83_to_Makarios_variant.

Section Makarios_variant_to_Tarski83.

Context `{MTn:Tarski_neutral_dimensionless_variant_with_decidable_point_equality}.

Ltac prolong A B x C D :=
 assert (sg:= Msegment_construction A B C D);
 ex_and sg x.

Lemma Mcong_reflexivity : forall A B,
 CongM A B A B.
Proof.
intros.
prolong B A x A B.
eapply Mcong_inner_transitivity with A x;auto.
Qed.

Lemma Mcong_symmetry : forall A B C D ,
 CongM A B C D -> CongM C D A B.
Proof.
intros.
eapply Mcong_inner_transitivity.
apply H.
apply Mcong_reflexivity.
Qed.

Lemma between_trivial : forall A B : MTpoint, BetM A B B.
Proof.
intros.
prolong A B x B B.
assert (x = B)
 by (apply Mcong_identity in H0;auto).
subst;assumption.
Qed.

Lemma Mcong_trivial_identity: 
 forall A B:MTpoint, CongM A A B B.
Proof.
  intros.
  assert (sg:= Msegment_construction A A B B);
  ex_and sg x.
  assert( A = x) by (eapply Mcong_identity;eauto).
  subst.
  assumption.
Qed.

Lemma LmCoghGrab: 
 forall A B C D E F:MTpoint,
  A <> B -> BetM B A C -> BetM D A E ->
  CongM B A D A -> CongM A C A E -> CongM B F D F ->
  CongM F C E F. 
Proof.
  intros.
  assert(CongM A F A F) by (eapply Mcong_reflexivity;eauto).
  assert(forall A A' B B' C C' D D':MTpoint,
   CongM A B A' B' -> CongM B C B' C' ->
   CongM A D A' D' -> CongM B D B' D' ->
   BetM A B C -> BetM A' B' C' -> A <> B ->
   CongM D C C' D') by apply Mfive_segment.
  apply (H6 B D A A);auto.
Qed.

Lemma cong_pre_pseudo_reflexivity: 
  forall A B C D:MTpoint, C <> D -> BetM D C B -> CongM A B B A.
Proof.
  intros.
  assert(CongM C B C B) by (eapply Mcong_reflexivity;eauto).
  assert(CongM D C D C) by (eapply Mcong_reflexivity;eauto).
  assert(CongM D A D A) by (eapply Mcong_reflexivity;eauto).
  eapply LmCoghGrab;eauto.
Qed.

Lemma cong_pseudo_reflexivity:
 forall A B:MTpoint, CongM A B B A.
Proof.
  intros.
  elim (Mpoint_equality_decidability A B).
    intros.
    subst.
    eapply Mcong_trivial_identity;eauto.

    intros.
    assert(BetM B A A) by (eapply between_trivial;eauto).
    eapply Mcong_symmetry;eauto.
    eapply cong_pre_pseudo_reflexivity;eauto.
Qed.

Lemma five_segment : forall A A' B B' C C' D D' : MTpoint,
    CongM A B A' B' ->
    CongM B C B' C' ->
    CongM A D A' D' ->
    CongM B D B' D' ->
    BetM A B C -> BetM A' B' C' -> A <> B -> CongM C D C' D'.
Proof.
  intros.
  assert(CongM D C C' D').
  intros.
  eapply Mfive_segment with A A' B B';assumption.
  assert(CongM D C C D).
  eapply cong_pseudo_reflexivity;eauto.
  eapply Mcong_inner_transitivity with D C;eauto.
Qed.

Instance Tarski_follows_from_Makarios_Variant : Tarski_neutral_dimensionless.
Proof.
exact (Build_Tarski_neutral_dimensionless
 MTpoint BetM CongM
 cong_pseudo_reflexivity
 Mcong_inner_transitivity
 Mcong_identity
 Msegment_construction
 five_segment
 Mbetween_identity
 Minner_pasch
 MPA MPB MPC
 Mlower_dim).
Defined.

Instance Tarski_follows_from_Makarios_Variant_with_decidable_point_equality' :
  Tarski_neutral_dimensionless_with_decidable_point_equality Tarski_follows_from_Makarios_Variant.
Proof. split; apply Mpoint_equality_decidability. Defined.

End Makarios_variant_to_Tarski83.
