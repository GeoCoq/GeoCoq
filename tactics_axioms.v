Require Export arity.

(** Minimal set of lemmas needed to use the ColR tactic. *)
Class Col_theory (COLTpoint : Type) (CTCol: COLTpoint -> COLTpoint -> COLTpoint -> Prop) :=
{
  CTcol_trivial : forall A B : COLTpoint, CTCol A A B;
  CTcol_permutation_1 : forall A B C : COLTpoint, CTCol A B C -> CTCol B C A;
  CTcol_permutation_2 : forall A B C : COLTpoint, CTCol A B C -> CTCol A C B;
  CTcol3 : forall X Y A B C : COLTpoint,
             X <> Y -> CTCol X Y A -> CTCol X Y B -> CTCol X Y C -> CTCol A B C
}.

Class Arity :=
{
  COATpoint : Type;
  n : nat
}.

Class Coapp_predicates (Ar : Arity) :=
{
  wd : arity COATpoint (S (S n));
  coapp : arity COATpoint (S (S (S n)))
}.

(** Minimal set of lemmas needed to use the Coapp tactic. *)
Class Coapp_theory (Ar : Arity) (COP : Coapp_predicates Ar) :=
{
  wd_perm_1 : forall A : COATpoint,
              forall X : cartesianPower COATpoint (S n),
                app_1_n wd A X -> app_n_1 wd X A;
  wd_perm_2 : forall A B : COATpoint,
              forall X : cartesianPower COATpoint n,
                app_2_n wd A B X -> app_2_n wd B A X;
  coapp_perm_1 : forall A : COATpoint,
                 forall X : cartesianPower COATpoint (S (S n)),
                   app_1_n coapp A X -> app_n_1 coapp X A;
  coapp_perm_2 : forall A B : COATpoint,
                 forall X : cartesianPower COATpoint (S n),
                   app_2_n coapp A B X -> app_2_n coapp B A X;
  coapp_bd : forall A : COATpoint,
             forall X : cartesianPower COATpoint (S n),
              app_2_n coapp A A X;
  coapp_n : forall COAPP : cartesianPower COATpoint (S (S (S n))),
            forall WD : cartesianPower COATpoint (S (S n)),
              pred_conj coapp COAPP WD ->
              app wd WD ->
              app coapp COAPP
}.