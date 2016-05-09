Require Export GeoCoq.Tarski_dev.Annexes.saccheri.
Require Export GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Export GeoCoq.Tarski_dev.Annexes.quadrilaterals.
Require Export GeoCoq.Tarski_dev.Coplanar_perm.
Require Export GeoCoq.Tarski_dev.Ch13_1.

Section Euclid_def.

Context `{Tn:Tarski_neutral_dimensionless}.

(** First some statements needed for equivalence proofs between different versions of
the parallel postulate. *)

Definition decidability_of_parallelism := forall A B C D,
  Par A B C D \/ ~ Par A B C D.

Definition decidability_of_not_intersection := forall A B C D,
  ~ (exists I, Col I A B /\ Col I C D) \/
  ~ ~ (exists I, Col I A B /\ Col I C D).

Definition decidability_of_intersection := forall A B C D,
  (exists I, Col I A B /\ Col I C D) \/
  ~ (exists I, Col I A B /\ Col I C D).

(*
Definition decidability_of_intersection_in_a_plane :=
  forall A B C D,
  coplanar' A B C D ->
  (exists I, Col I A B /\ Col I C D) \/
  ~ (exists I, Col I A B /\ Col I C D).
*)

Definition aristotle_s_postulate := forall P Q A B C,
  ~ Col A B C -> Acute A B C ->
  exists X, exists Y, Out B A X /\ Out B C Y /\ Per B X Y /\ Lt P Q X Y.

Definition greenberg_s_postulate := forall P Q R A B C, ~ Col A B C ->
  Acute A B C -> Q <> R -> Per P Q R ->
  exists S, LtA P S Q A B C /\ Out Q S R.

Definition tarski_s_parallel_postulate := forall A B C D T,
  Bet A D T -> Bet B D C -> A <> D ->
  exists X, exists Y, Bet A B X /\ Bet A C Y /\ Bet X T Y.

(** This is unicity of parallel postulate. *)

Definition playfair_s_postulate := forall A1 A2 B1 B2 C1 C2 P,
  Par A1 A2 B1 B2 -> Col P B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2.

(** According to wikipedia:
"Proclus (410-485) wrote a commentary on The Elements where he comments on attempted proofs to deduce
 the fifth postulate from the other four, in particular he notes that Ptolemy had produced a false 'proof'.
 Proclus then goes on to give a false proof of his own.
 However he did give a postulate which is equivalent to the fifth postulate." *)

Definition proclus_postulate := forall A B C D P Q,
  Par A B C D -> Col A B P -> ~ Col A B Q ->
  exists Y, Col P Q Y /\ Col C D Y.

(** Transitivity of parallelism. *)

Definition postulate_of_transitivity_of_parallelism := forall A1 A2 B1 B2 C1 C2,
  Par A1 A2 B1 B2 -> Par B1 B2 C1 C2 ->
  Par A1 A2 C1 C2.

Definition perpendicular_transversal_postulate := forall A B C D P Q,
  Par A B C D -> Perp A B P Q ->
  Perp C D P Q.

Definition proclus_second_postulate := forall A1 A2 A3 A4 B1 B2 B3 B4,
  Par A1 A2 B1 B2 ->
  Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
  Col A1 A2 A4 -> Col B1 B2 B4 -> Perp A1 A2 A4 B4 ->
  Cong A3 B3 A4 B4.

Definition postulate_of_parallelism_of_perpendicular_transversals :=
  forall A1 A2 B1 B2 C1 C2 D1 D2,
  Par A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
  Par C1 C2 D1 D2.

Definition triangle_circumscription_principle := forall A B C,
  ~ Col A B C -> exists CC, Cong A CC B CC /\ Cong A CC C CC.

Definition BetS A B C : Prop := Bet A B C /\ A <> B /\ B <> C.

Lemma BetSEq : forall A B C, BetS A B C <-> Bet A B C /\ A <> B /\ A <> C /\ B <> C.
Proof.
intros; unfold BetS; split; intro; spliter;
repeat split; Col; intro; treat_equalities; Col.
Qed.

Definition SPP := forall P Q R S T U,
  BetS P T Q -> BetS R T S -> ~ Col P R U ->
  Coplanar P Q R U ->
  Cong P T Q T -> Cong R T S T ->
  exists I, Col S Q I /\ Col P U I.

Definition strong_parallel_postulate := forall P Q R S T U,
  BetS P T Q -> BetS R T S -> ~ Col P R U ->
  Cong P T Q T -> Cong R T S T ->
  exists I, Col S Q I /\ Col P U I.

Definition euclid_5 := forall P Q R S T U,
  BetS P T Q -> BetS R T S -> BetS Q U R -> ~ Col P Q S ->
  Cong P T Q T -> Cong R T S T ->
  exists I, BetS S Q I /\ BetS P U I.

(** This is the converse of triangle_mid_par. *)

Definition midpoint_converse_postulate := forall A B C P Q,
  ~Col A B C ->
  Midpoint P B C ->
  Par A B Q P ->
  Col A C Q ->
  Midpoint Q A C.

(** This is the converse of l12_21_b. *)

Definition alternate_interior_angles_postulate := forall A B C D,
  TS A C B D -> Par A B C D ->
  CongA B A C D C A.

Definition existential_playfair_s_postulate :=
  exists A1 A2 P, ~ Col A1 A2 P /\
             (forall B1 B2 C1 C2,
                Par A1 A2 B1 B2 -> Col P B1 B2 ->
                Par A1 A2 C1 C2 -> Col P C1 C2 ->
                Col C1 B1 B2 /\ Col C2 B1 B2).

Definition triangle_postulate := forall A B C D E F,
  TriSumA A B C D E F -> Bet D E F.

Definition alternative_playfair_s_postulate := forall A1 A2 B1 B2 C1 C2 P,
  Perp2 A1 A2 B1 B2 P -> Col P B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2.

Definition euclid_s_parallel_postulate := forall A B C D P Q R,
  OS B C A D ->
  Isi A B C B C D ->
  SumA A B C B C D P Q R ->
  ~ Bet P Q R ->
  exists Y, Out B A Y /\ Out C D Y.

Definition alternative_strong_parallel_postulate := forall A B C D P Q R,
  OS B C A D ->
  SumA A B C B C D P Q R ->
  ~ Bet P Q R ->
  exists Y, Col B A Y /\ Col C D Y.

Definition inverse_projection_postulate := forall A B C P Q,
  Acute A B C ->
  Out B A P ->
  P <> Q -> Per B P Q ->
  exists Y, Out B C Y /\ Col P Q Y.

Definition alternative_proclus_postulate := forall A B C D P Q,
  Perp2 A B C D P ->
  Col A B P ->
  ~ Col A B Q ->
  exists Y, Col P Q Y /\ Col C D Y.

Definition consecutive_interior_angles_postulate := forall A B C D P Q R,
  OS B C A D ->
  Par A B C D ->
  SumA A B C B C D P Q R ->
  Bet P Q R.

Definition postulate_of_existence_of_a_triangle_whose_angles_sum_to_2_rights :=
  exists A B C D E F, ~ Col A B C /\ TriSumA A B C D E F /\ Bet D E F.

Definition postulate_of_right_saccheri_quadrilaterals := forall A B C D,
  Saccheri A B C D -> Per A B C.

Definition postulate_of_existence_of_a_right_saccheri_quadrialteral :=
  exists A B C D, Saccheri A B C D /\ Per A B C.

Definition postulate_of_right_lambert_quadrilaterals := forall A B C D,
  Lambert A B C D -> Per B C D.

Definition postulate_of_existence_of_a_right_lambert_quadrialteral :=
  exists A B C D, Lambert A B C D /\ Per B C D.

Definition thales_postulate := forall A B C M,
  ~ Col A B C -> Midpoint M A B -> Cong M A M C ->
  Per A C B.

Definition thales_converse_postulate := forall A B C M,
  ~ Col A B C -> Midpoint M A B -> Per A C B ->
  Cong M A M C.

Definition existential_thales_postulate :=
  exists A B C M, ~ Col A B C /\ Midpoint M A B /\ Cong M A M C /\ Per A C B.

Definition weak_triangle_circumscription_principle := forall A B C A1 A2 B1 B2,
  ~ Col A B C ->
  Per A C B ->
  Perp_bisect A1 A2 B C -> Perp_bisect B1 B2 A C ->
  exists I, Col A1 A2 I /\ Col B1 B2 I.

Definition bachmann_s_lotschnittaxiom := forall A1 A2 B1 B2 C1 C2 D1 D2,
  Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
  ~ Col A1 A2 D1 -> ~ Col B1 B2 C1 ->
  exists I, Col C1 C2 I /\ Col D1 D2 I.

Definition existential_inverse_projection_postulate :=
  exists A B C, ~ Col A B C /\ Acute A B C /\
  forall P Q, Out B A P -> P <> Q -> Per B P Q ->
  exists Y, Out B C Y /\ Col P Q Y.

Definition legendre_s_postulate :=
  exists A B C, ~ Col A B C /\ Acute A B C /\
  forall T, InAngle T A B C -> exists X Y, Out B A X /\ Out B C Y /\ Bet X T Y.

Definition posidonius_postulate :=
  exists A1 A2 B1 B2, ~ Col A1 A2 B1 /\ B1 <> B2 /\ forall A3 A4 B3 B4,
  Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
  Col A1 A2 A4 -> Col B1 B2 B4 -> Perp A1 A2 A4 B4 ->
  Cong A3 B3 A4 B4.

Definition postulate_of_existence_of_similar_triangles :=
  exists A B C D E F,
  ~ Col A B C /\ ~ Cong A B D E /\
  CongA A B C D E F /\ CongA B C A E F D /\ CongA C A B F D E.

End Euclid_def.