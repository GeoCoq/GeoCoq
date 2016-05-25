Require Export Setoid.
Require Export GeoCoq.Utils.aux.



Class Hilbert_neutral_2D := {
 Point : Type;
 Line  : Type;
 EqL   : Line -> Line -> Prop;
 EqL_Equiv : Equivalence EqL;
 Incid : Point -> Line -> Prop;

 Incid_morphism : forall P l m, Incid P l -> EqL l m -> Incid P m;
 Incid_dec : forall P l, Incid P l \/ ~ Incid P l;
 eq_dec_pointsH : forall A B : Point, A=B \/ ~ A=B;

 (** Group I Incidence *)
 line_existence : forall A B, A <> B -> exists l, Incid A l /\ Incid B l;
 line_unicity : forall A B l m, A <> B -> Incid A l -> Incid B l -> Incid A m -> Incid B m -> EqL l m;
 two_points_on_line : forall l, exists A, exists B, Incid B l /\ Incid A l /\ A <> B;
 ColH := fun A B C => exists l, Incid A l /\ Incid B l /\ Incid C l;
 plan : exists l, exists P, ~ Incid P l;

 (** Group II Order *)
 BetH   : Point -> Point -> Point -> Prop;
 between_col :  forall A B C, BetH A B C -> ColH A B C;
 between_diff : forall A B C, BetH A B C -> A <> C;
 between_comm : forall A B C, BetH A B C -> BetH C B A;
 between_out :  forall A B, A <> B -> exists C, BetH A B C;
 between_only_one : forall A B C, BetH A B C -> ~ BetH B C A;
 cut := fun l A B => ~ Incid A l /\ ~ Incid B l /\ exists I, Incid I l /\ BetH A I B;
 pasch : forall A B C l, ~ ColH A B C -> ~ Incid C l -> cut l A B -> cut l A C \/ cut l B C;


 (** Group III Congruence *)
 CongH : Point -> Point -> Point -> Point -> Prop;
 cong_permr : forall A B C D, CongH A B C D -> CongH A B D C;
 cong_pseudo_transitivity : forall A B C D E F, CongH A B C D -> CongH A B E F -> CongH C D E F;
 cong_existence : forall A B l M, A <> B -> Incid M l -> exists A', exists B',
    Incid A' l /\ Incid B' l /\ BetH A' M B' /\ CongH M A' A B /\ CongH M B' A B;

  disjoint := fun A B C D => ~ exists P, BetH A P B /\ BetH C P D;
  addition: forall A B C A' B' C', ColH A B C -> ColH A' B' C' ->
                                  disjoint A B B C -> disjoint A' B' B' C' ->
                                  CongH A B A' B' -> CongH B C B' C' -> CongH A C A' C';

  CongaH: Point -> Point -> Point -> Point -> Point -> Point -> Prop;
  conga_refl: forall A B C, ~ ColH A B C -> CongaH A B C A B C;
  conga_comm: forall A B C, ~ ColH A B C -> CongaH A B C C B A;
  congaH_permlr : forall A B C D E F, CongaH A B C D E F -> CongaH C B A F E D;
  cong_5 : forall A B C A' B' C', ~ ColH A B C -> ~ ColH A' B' C' ->
           CongH A B A' B' -> CongH A C A' C' -> CongaH B A C B' A' C' -> CongaH A B C A' B' C';

  same_side := fun A B l => exists P, cut l A P /\ cut l B P;
  same_side' := fun A B X Y =>  X <> Y /\ forall l, Incid X l -> Incid Y l -> same_side A B l;

  outH := fun P A B => BetH P A B \/ BetH P B A \/ (P <> A /\ A = B);
  congaH_outH_congaH : forall A B C D E F A' C' D' F',
    CongaH A B C D E F ->
    outH B A A' -> outH B C C' -> outH E D D' -> outH E F F' ->
    CongaH A' B C' D' E F';
  hcong_4_existence :  forall A B C O X P,
    ~ ColH P O X -> ~ ColH A B C ->
   exists Y, CongaH A B C X O Y /\ same_side' P Y O X;

  hcong_4_unicity :
   forall A B C O P X Y Y', ~ ColH P O X  -> ~ ColH A B C -> CongaH A B C X O Y -> CongaH A B C X O Y' -> same_side' P Y O X -> same_side' P Y' O X -> outH O Y Y'
}.

Class Hilbert_euclidean_2D `(Hilbert2 : Hilbert_neutral_2D) := {
 Para := fun l m => ~ exists X, Incid X l /\ Incid X m;
 euclid_unicity :  forall l P m1 m2, ~ Incid P l -> Para l m1 -> Incid P m1-> Para l m2 -> Incid P m2 -> EqL m1 m2
}.