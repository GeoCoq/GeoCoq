From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.

Class predicates :=
{
  Tpoint : Type;
  Bet : Tpoint -> Tpoint -> Tpoint -> Prop;
  Cong : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop
}.

Class independent_Tarski_neutral_dimensionless (Pred : predicates) :=
{
  cong_pseudo_reflexivity : cong_pseudo_reflexivityP Tpoint Cong;
  cong_inner_transitivity : cong_inner_transitivityP Tpoint Cong;
  cong_identity           : cong_identityP Tpoint Cong;
  segment_construction    : segment_constructionP Tpoint Bet Cong;
  five_segment            : five_segmentP Tpoint Bet Cong;
  inner_pasch             : inner_paschP Tpoint Bet;
  bet_symmetry            : bet_symmetryP Tpoint Bet;
  bet_inner_transitivity  : bet_inner_transitivityP Tpoint Bet
}.

Class dimension :=
{
  n : nat
}.

Instance incr (Dim : dimension) : dimension := {| n := n.+1 |}.

Class independent_Tarski_nD
  (Pred : predicates) (ITn : independent_Tarski_neutral_dimensionless Pred)
  (Dim : dimension) :=
{
  O : Tpoint;
  I : Tpoint;
  basis : n.-tuple Tpoint;
  lower_dim : lower_dimP Tpoint Bet Cong n O I basis;
  upper_dim : upper_dimP Tpoint Bet Cong n O I basis
}.

Class independent_Tarski_euclidean
  (Pred : predicates) (ITn : independent_Tarski_neutral_dimensionless Pred) :=
{
  euclid : euclidP Tpoint Bet Cong
}.

Class Eq_stability
  (Pred : predicates) (ITn : independent_Tarski_neutral_dimensionless Pred) :=
{
  point_equality_stability : (* Model given by Beeson *)
    forall (A B : Tpoint), ~ ~ A = B -> A = B
}.

Class Eq_decidability
  (Pred : predicates) (ITn : independent_Tarski_neutral_dimensionless Pred) :=
{
  point_equality_decidability : (* Model given by Beeson *)
    forall (A B : Tpoint), A = B \/ A <> B
}.