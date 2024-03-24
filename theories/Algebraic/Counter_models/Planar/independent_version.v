From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

Class independent_Tarski_neutral_dimensionless (Tpoint : Type) :=
{
  Bet :
    Tpoint -> Tpoint -> Tpoint -> Prop;
  Cong :
    Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop;
  cong_pseudo_reflexivity : cong_pseudo_reflexivityP Tpoint Cong;
  cong_inner_transitivity : cong_inner_transitivityP Tpoint Cong;
  cong_identity           : cong_identityP Tpoint Cong;
  segment_construction    : segment_constructionP Tpoint Bet Cong;
  five_segment            : five_segmentP Tpoint Bet Cong;
  inner_pasch             : inner_paschP Tpoint Bet;
  bet_symmetry            : bet_symmetryP Tpoint Bet;
  bet_inner_transitivity  : bet_inner_transitivityP Tpoint Bet
}.

Class independent_Tarski_2D `(independent_Tarski_neutral_dimensionless) :=
{
  PA : Tpoint;
  PB : Tpoint;
  PC : Tpoint;
  lower_dim : lower_dimP Tpoint Bet PA PB PC;
  upper_dim : upper_dimP Tpoint Bet Cong
}.

Class independent_Tarski_euclidean
      `(independent_Tarski_neutral_dimensionless) :=
{
  euclid : euclidP Tpoint Bet
}.

Class Eq_stability `(independent_Tarski_neutral_dimensionless) :=
{
  point_equality_stability : (* Model given by Beeson *)
    forall (A B : Tpoint), ~ ~ A = B -> A = B
}.

Class Eq_decidability `(independent_Tarski_neutral_dimensionless) :=
{
  point_equality_decidability : (* Model given by Beeson *)
    forall (A B : Tpoint), A = B \/ A <> B
}.
