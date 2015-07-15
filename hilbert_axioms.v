Require Export Setoid.
Require Export aux.

(** We circumvent a limitation of type class definition by defining a polymorphic type for a triple of elements which will be used to define an angle by instantiating 
 A with Point *)

Class Hilbert := {
 Point : Type;
 Line  : Type;
 EqL   : Line -> Line -> Prop;
 EqL_Equiv : Equivalence EqL;
 Incid : Point -> Line -> Prop;

 (** Group I Incidence *)
 line_existence : forall A B, A<>B -> exists l, Incid A l /\ Incid B l;
 line_unicity : forall A B l m, A <> B -> Incid A l -> Incid B l -> Incid A m -> Incid B m -> EqL l m;
 two_points_on_line : forall l, exists A, exists B, Incid B l /\ Incid A l /\ A <> B;
 ColH := fun A B C => exists l, Incid A l /\ Incid B l /\ Incid C l;
 plan : exists A, exists B, exists C, ~ ColH A B C;

 (** Group II Order *)
 BetH   : Point -> Point -> Point -> Prop;
 between_col :  forall A B C : Point, BetH A B C -> ColH A B C;
 between_comm : forall A B C : Point, BetH A B C -> BetH C B A;
 between_out :  forall A B   : Point, A <> B -> exists C : Point, BetH A B C;
 between_only_one : forall A B C : Point, BetH A B C -> ~ BetH B C A /\ ~ BetH B A C;
 between_one : forall A B C, A<>B -> A<>C -> B<>C -> ColH A B C -> BetH A B C \/ BetH B C A \/ BetH B A C;
 cut := fun l A B => ~ Incid A l /\ ~ Incid B l /\ exists I, Incid I l /\ BetH A I B;
 pasch : forall A B C l, ~ ColH A B C -> ~ Incid C l -> cut l A B -> cut l A C \/ cut l B C;


 (** Group III Parallels *)
 Para := fun l m => ~ exists X, Incid X l /\ Incid X m;
 euclid_existence : forall l P, ~ Incid P l -> exists m, Para l m;
 euclid_unicity :  forall l P m1 m2, ~ Incid P l -> Para l m1 -> Incid P m1-> Para l m2 -> Incid P m2 -> EqL m1 m2;
 
 (** Group IV Congruence *)
 CongH : Point -> Point -> Point -> Point -> Prop;
 cong_pseudo_transitivity : forall A B C D E F, CongH A B C D -> CongH A B E F -> CongH C D E F;
 cong_refl : forall A B, CongH A B A B;
 cong_existence : forall A B l M, A <> B -> Incid M l -> exists A', exists B', 
    Incid A' l /\ Incid B' l /\ BetH A' M B' /\ CongH M A' A B /\ CongH M B' A B;
 cong_unicity : forall A B l M A' B' A'' B'', A <> B -> Incid M l ->
  Incid A'  l -> Incid B'  l ->
  Incid A'' l -> Incid B'' l ->
  BetH A' M B' -> CongH M A' A B ->
  CongH M B'  A B -> BetH  A'' M B'' ->
  CongH M A'' A B -> 
  CongH M B'' A B ->
  (A' = A'' /\ B' = B'') \/ (A' = B'' /\ B' = A'');

 disjoint := fun A B C D => ~ exists P, BetH A P B /\ BetH C P D;
 addition: forall A B C A' B' C', ColH A B C -> ColH A' B' C' ->
                                  disjoint A B B C -> disjoint A' B' B' C' -> 
                                  CongH A B A' B' -> CongH B C B' C' -> CongH A C A' C';
 Angle := @Triple Point;
 angle := build_triple Point;
 CongaH : Angle -> Angle -> Prop;
 cong_5 : forall A B C A' B' C', forall H1 : (B<>A /\ C<>A), forall H2: B' <> A' /\ C' <> A',
  forall H3 : (A<>B /\ C<>B), forall H4: A' <> B' /\ C' <> B',
  CongH A B A' B' -> CongH A C A' C' -> CongaH (angle B A C H1) (angle B' A' C' H2) -> 
   CongaH (angle A B C H3) (angle A' B' C' H4);

 same_side := fun A B l => exists P, cut l A P /\ cut l B P;

 outH := fun P A B => BetH P A B \/ BetH P B A \/ (P <> A /\ A = B);

 InAngleH := fun a P => 
 (exists M, BetH (V1 a) M (V2 a) /\ ((outH (V a) M P) \/ M = (V a))) \/ 
                                   outH (V a) (V1 a) P \/ outH (V a) (V2 a) P;

 Hline := @Couple Point;
 line_of_hline : Hline -> Line;
 hline_construction := fun a (h: Hline)  P (hc:Hline) H => 
 (P1 h) = (P1 hc) /\
 CongaH a (angle (P2 h) (P1 h) (P2 hc) (conj (sym_not_equal (Cond h)) H)) /\
  (forall M, InAngleH (angle (P2 h) (P1 h) (P2 hc) (conj (sym_not_equal (Cond h)) H)) M ->
   same_side P M  (line_of_hline h));


  aux : forall (h h1 : Hline), P1 h = P1 h1 -> P2 h1 <> P1 h;

  hcong_4_existence: forall a h P, 
  ~Incid P (line_of_hline h) -> ~ BetH (V1 a)(V a)(V2 a) ->
  exists h1, (P1 h) = (P1 h1) /\ (forall CondAux : P1 h = P1 h1,  
                                    CongaH a (angle (P2 h) (P1 h) (P2 h1) (conj (sym_not_equal (Cond h)) (aux h h1 CondAux)))
                                    /\ (forall M, ~ Incid M (line_of_hline h) /\ InAngleH (angle (P2 h) (P1 h) (P2 h1) (conj (sym_not_equal (Cond h)) (aux h h1 CondAux))) M
                                                    -> same_side P M  (line_of_hline h)));


 hEq : relation Hline := fun h1 h2 => (P1 h1) = (P1 h2) /\ 
                          ((P2 h1) = (P2 h2) \/ BetH (P1 h1) (P2 h2) (P2 h1) \/ 
                                                  BetH (P1 h1) (P2 h1) (P2 h2));

 hcong_4_unicity :
  forall a h P h1 h2 HH1 HH2,
  ~Incid P (line_of_hline h) -> ~ BetH (V1 a)(V a)(V2 a) ->
  hline_construction a h P h1 HH1 -> hline_construction a h P h2 HH2 ->
  hEq h1 h2

}.
