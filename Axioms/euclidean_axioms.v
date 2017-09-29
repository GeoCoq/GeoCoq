(** The following axiom systems are used to formalize
    Euclid's proofs of Euclid's Elements.OriginalProofs.statements. *)

(** First, we define an axiom system for neutral geometry, 
    i.e. geometry without continuity axioms nor parallel postulate.
 *)

Class euclidean_neutral :=
{
  Point : Type;
  Circle : Type; 
  Cong : Point -> Point -> Point -> Point -> Prop;
  BetS : Point -> Point -> Point -> Prop;
  InCirc : Point -> Circle -> Prop;
  OnCirc : Point -> Circle -> Prop;
  OutCirc : Point -> Circle -> Prop;
  PA : Point;
  PB : Point;
  PC : Point;
  CI : Circle -> Point -> Point -> Point -> Prop;
  eq := @eq Point;
  neq A B := ~ eq A B;
  TE A B C := ~ (neq A B /\ neq B C /\ ~ BetS A B C);
  nCol A B C := neq A B /\ neq A C /\ neq B C /\ ~ BetS A B C /\ ~ BetS A C B /\ ~ BetS B A C;
  Col A B C := (eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B);
  Cong_3 A B C a b c := Cong A B a b /\ Cong B C b c /\ Cong A C a c;
  TS P A B Q := exists X, BetS P X Q /\ Col A B X /\ nCol A B P;
  Triangle A B C := nCol A B C; 

  cn_equalitytransitive : 
   forall A B C, eq A C -> eq B C -> eq A B;
  cn_congruencetransitive :
   forall B C D E P Q, Cong P Q B C -> Cong P Q D E -> Cong B C D E;
  cn_equalityreflexive :
   forall A, eq A A;
  cn_congruencereflexive :
   forall A B, Cong A B A B;
  cn_equalityreverse :
   forall A B, Cong A B B A;
  cn_stability :
   forall A B, ~ neq A B -> eq A B;
  cn_equalitysub :
   forall A B C D, eq D A -> BetS A B C -> BetS D B C;
  circle : forall A B C, neq A B -> exists X, CI X C A B;
  inside : forall A B C J P, CI J C A B /\ InCirc P J <-> exists X Y, CI J C A B /\ BetS X C Y /\ Cong C Y A B /\ Cong C X A B /\ BetS X P Y;
  outside : forall A B C J P, CI J C A B /\ OutCirc P J <-> exists X, CI J C A B /\ BetS C X P /\ Cong C X A B;
  on : forall A B C D J, CI J A C D /\ OnCirc B J <-> CI J A C D /\ Cong A B C D;
  axiom_lower_dim : nCol PA PB PC;
  axiom_betweennessidentity :
   forall A B, ~ BetS A B A;
  axiom_betweennesssymmetry :
   forall A B C, BetS A B C -> BetS C B A;
  axiom_innertransitivity :
   forall A B C D,
    BetS A B D -> BetS B C D -> BetS A B C;
  axiom_connectivity :
   forall A B C D,
    BetS A B D -> BetS A C D -> ~ BetS A B C -> ~ BetS A C B ->
    eq B C;
  axiom_nullsegment1 :
   forall A B C, Cong A B C C -> eq A B;
  axiom_nullsegment2 :
   forall A B, Cong A A B B;
  axiom_5_line :
   forall A B C D a b c d,
    Cong B C b c -> Cong A D a d -> Cong B D b d ->
    BetS A B C -> BetS a b c -> Cong A B a b ->
    Cong D C d c;
  postulate_extension :
   forall A B C D,
    neq A B -> neq C D ->
    exists X, BetS A B X /\ Cong B X C D;
  postulate_extension2 :
   forall A B C D,
    neq A B ->
    exists X, TE A B X /\ Cong B X C D;
  postulate_Pasch_inner :
   forall A B C P Q,
    BetS A P C -> BetS B Q C -> nCol A C B ->
    exists X, BetS A X Q /\ BetS B X P;
  postulate_Pasch_outer :
   forall A B C P Q,
    BetS A P C -> BetS B C Q -> nCol B Q A ->
    exists X, BetS A X Q /\ BetS B P X;
}.

(** Second, we enrich the axiom system with line-circle
     and circle-circle continuity axioms. 
    Those two axioms states that we allow ruler and compass
    constructions. 
*)

Class euclidean_neutral_ruler_compass `(Ax : euclidean_neutral) := 
{
  postulate_line_circle :
   forall A B C K P Q,
    CI K C P Q -> InCirc B K -> neq A B ->
    exists X Y, Col A B X /\ Col A B Y /\ OnCirc X K /\ OnCirc Y K /\ BetS X B Y;
  postulate_circle_circle :
   forall C D F G J K P Q R S,
    CI J C R S -> InCirc P J ->
    OutCirc Q J -> CI K D F G ->
    OnCirc P K -> OnCirc Q K ->
    exists X, OnCirc X J /\ OnCirc X K
}.

(** Third, we introduce the famous fifth postulate of Euclid, 
    which ensure that the geometry is 
    Euclidean (i.e. not hyperbolic).
 *)

Class euclidean_euclidean `(Ax : euclidean_neutral_ruler_compass) := 
{
  postulate_Euclid5 :
   forall a p q r s t,
    BetS r t s -> BetS p t q -> BetS r a q ->
    Cong p t q t -> Cong t r t s -> nCol p q s ->
    exists X, BetS p a X /\ BetS s q X
}.

(** Last, we enrich the axiom system with axioms for equality of areas. *)

Class area `(Ax : euclidean_euclidean) := 
{
  EF : Point -> Point -> Point -> Point -> Point -> Point -> Point -> Point -> Prop;
  ET : Point -> Point -> Point -> Point -> Point -> Point -> Prop;
  axiom_EFreflexive :
   forall A B C D, EF A B C D A B C D;
  axiom_ETreflexive :
   forall A B C, ET A B C A B C;
  axiom_congruentequal :
   forall A B C a b c, Cong_3 A B C a b c -> ET A B C a b c;
  axiom_ETpermutation :
   forall A B C a b c, 
    ET A B C a b c ->
    ET A B C b c a /\
    ET A B C a c b /\
    ET A B C b a c /\
    ET A B C c b a /\
    ET A B C c a b;
  axiom_ETsymmetric :
   forall A B C a b c, ET A B C a b c -> ET a b c A B C;
  axiom_EFpermutation :
   forall A B C D a b c d,
   EF A B C D a b c d -> 
     EF A B C D b c d a /\
     EF A B C D d c b a /\
     EF A B C D c d a b /\
     EF A B C D b a d c /\
     EF A B C D d a b c /\
     EF A B C D c b a d /\
     EF A B C D a d c b;
  axiom_halvesofequals :
   forall A B C D a b c d, ET A B C B C D ->
                           TS A B C D -> ET a b c b c d ->
                           TS a b c d -> EF A B D C a b d c -> ET A B C a b c;
  axiom_EFsymmetric :
   forall A B C D a b c d, EF A B C D a b c d ->
                           EF a b c d A B C D;
  axiom_EFtransitive :
   forall A B C D P Q R S a b c d, 
     EF A B C D a b c d -> EF a b c d P Q R S ->
     EF A B C D P Q R S;
  axiom_ETtransitive :
   forall A B C P Q R a b c,
    ET A B C a b c -> ET a b c P Q R -> ET A B C P Q R;
  axiom_cutoff1 :
   forall A B C D E a b c d e,
    BetS A B C -> BetS a b c -> BetS E D C -> BetS e d c ->
    ET B C D b c d -> ET A C E a c e ->
    EF A B D E a b d e;
  axiom_cutoff2 :
   forall A B C D E a b c d e,
    BetS B C D -> BetS b c d -> ET C D E c d e -> EF A B D E a b d e ->
    EF A B C E a b c e;
  axiom_paste1 :
   forall A B C D E a b c d e,
    BetS A B C -> BetS a b c -> BetS E D C -> BetS e d c ->
    ET B C D b c d -> EF A B D E a b d e ->
    ET A C E a c e;
  axiom_deZolt1 :
   forall B C D E, BetS B E D -> ~ ET D B C E B C;
  axiom_deZolt2 :
   forall A B C E F,
    Triangle A B C -> BetS B E A -> BetS B F C ->
  ~ ET A B C E B F;
  axiom_paste2 :
   forall A B C D E a b c d e,
    BetS B C D -> BetS b c d -> ET C D E c d e ->
    EF A B C E a b c e -> EF A B D E a b d e;
  axiom_paste3 :
   forall A B C D a b c d,
    ET A B C a b c -> ET A B D a b d ->
    TS C A B D -> TS c a b d ->
    EF A C B D a c b d;
  axiom_paste4 :
   forall A B C D F G H K L M e m,
    EF A B m D F K H G -> EF D B e C G H M L ->
    TS A B D C -> BetS K H M -> BetS F G L -> BetS B m D -> BetS B e C ->
    EF A B C D F K M L;
  axiom_paste5 :
   forall B C D E L M b c d e l m, 
    EF B M L D b m l d -> EF M C E L m c e l ->
    BetS B M C -> BetS b m c -> BetS E L D -> BetS e l d ->
    EF B C E D b c e d;
}.






