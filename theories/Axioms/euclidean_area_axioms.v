(** Axioms for equality of areas, used to formalize
    Euclid's proofs of Euclid's Elements.OriginalProofs.statements. *)

Require Export GeoCoq.Axioms.euclidean_axioms.

(** Last, we enrich the axiom system with axioms for equality of areas. *)

Class area `(Ax : euclidean_euclidean) :=
{
  EF : Point -> Point -> Point -> Point -> Point -> Point -> Point -> Point -> Prop;
  ET : Point -> Point -> Point -> Point -> Point -> Point -> Prop;
  axiom_congruentequal :
    forall A B C a b c, Triangle A B C -> Cong_3 A B C a b c -> ET A B C a b c;
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
    forall A B C D a b c d,
      ET A B C B C D ->
      TS A B C D -> ET a b c b c d ->
      TS a b c d -> EF A B D C a b d c -> ET A B C a b c;
  axiom_EFsymmetric :
    forall A B C D a b c d,
      EF A B C D a b c d ->
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
    forall A B C D E M a b c d e m,
      BetS B C D -> BetS b c d -> ET C D E c d e ->
      EF A B C E a b c e ->
      BetS A M D -> BetS B M E ->
      BetS a m d -> BetS b m e ->
      EF A B D E a b d e;
  axiom_paste3 :
    forall A B C D M a b c d m,
      ET A B C a b c -> ET A B D a b d ->
      BetS C M D ->
      (BetS A M B \/ eq A M \/ eq M B) ->
      BetS c m d ->
      (BetS a m b \/ eq a m \/ eq m b) ->
      EF A C B D a c b d;
  axiom_paste4 :
    forall A B C D F G H J K L M P e m,
      EF A B m D F K H G -> EF D B e C G H M L ->
      BetS A P C -> BetS B P D -> BetS K H M -> BetS F G L ->
      BetS B m D -> BetS B e C -> BetS F J M -> BetS K J L ->
      EF A B C D F K M L;
}.

Module Area_inconsistent.

Class area_inconsistent `(Ax : euclidean_euclidean) :=
{
  EF : Point -> Point -> Point -> Point -> Point -> Point -> Point -> Point -> Prop;
  ET : Point -> Point -> Point -> Point -> Point -> Point -> Prop;
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
    forall A B C D a b c d,
      ET A B C B C D ->
      TS A B C D -> ET a b c b c d ->
      TS a b c d -> EF A B D C a b d c -> ET A B C a b c;
  axiom_EFsymmetric :
    forall A B C D a b c d,
      EF A B C D a b c d ->
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
    forall A B C D E M a b c d e m,
      BetS B C D -> BetS b c d -> ET C D E c d e ->
      EF A B C E a b c e ->
      BetS A M D -> BetS B M E ->
      BetS a m d -> BetS b m e ->
      EF A B D E a b d e;
  axiom_paste3 :
    forall A B C D M a b c d m,
      ET A B C a b c -> ET A B D a b d ->
      BetS C M D ->
      (BetS A M B \/ eq A M \/ eq M B) ->
      BetS c m d ->
      (BetS a m b \/ eq a m \/ eq m b) ->
      EF A C B D a c b d;
  axiom_paste4 :
    forall A B C D F G H J K L M P e m,
      EF A B m D F K H G -> EF D B e C G H M L ->
      BetS A P C -> BetS B P D -> BetS K H M -> BetS F G L ->
      BetS B m D -> BetS B e C -> BetS F J M -> BetS K J L ->
      EF A B C D F K M L;
}.

End Area_inconsistent.
