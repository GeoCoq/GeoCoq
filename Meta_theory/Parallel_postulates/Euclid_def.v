Require Export GeoCoq.Tarski_dev.Annexes.suma.
Require Export GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Export GeoCoq.Tarski_dev.Annexes.quadrilaterals.
Require Export GeoCoq.Tarski_dev.Coplanar_perm.
Require Export GeoCoq.Tarski_dev.Ch13_1.

Section Euclid_def.

Context `{M:Tarski_neutral_dimensionless}.

(** First some statements needed for equivalence proofs between different versions of 
the parallel postulate. *)

Definition decidability_of_intersection :=
  forall A B C D,
  (exists I, Col I A B /\ Col I C D) \/
  ~ (exists I, Col I A B /\ Col I C D).

(*
Definition decidability_of_intersection_in_a_plane :=
  forall A B C D,
  coplanar' A B C D ->
  (exists I, Col I A B /\ Col I C D) \/
  ~ (exists I, Col I A B /\ Col I C D).
*)

Definition aristotle_s_postulate :=
  forall P Q A B C,
  ~ Col A B C -> acute A B C ->
  exists X, exists Y, out B A X /\ out B C Y /\ Per B X Y /\ lt P Q X Y.

Definition greenberg_s_postulate :=
  forall P Q R A B C, ~ Col A B C ->
  acute A B C -> Q <> R -> Per P Q R ->
  exists S, lta P S Q A B C /\ out Q S R.

Definition tarski_s_parallel_postulate :=
 forall A B C D T,
 Bet A D T -> Bet B D C -> A<>D ->
 exists x, exists y,
 Bet A B x /\ Bet A C y /\ Bet x T y.

(** This is unicity of parallel postulate. *)

Definition playfair_s_postulate :=
 forall A1 A2 B1 B2 C1 C2 P,
 Par A1 A2 B1 B2 -> Col P B1 B2 ->
 Par A1 A2 C1 C2 -> Col P C1 C2 ->
 Col C1 B1 B2 /\ Col C2 B1 B2.

(** According to wikipedia:
"Proclus (410-485) wrote a commentary on The Elements where he comments on attempted proofs to deduce
 the fifth postulate from the other four, in particular he notes that Ptolemy had produced a false 'proof'.
 Proclus then goes on to give a false proof of his own.
 However he did give a postulate which is equivalent to the fifth postulate." *)

Definition proclus_postulate :=
 forall A B C D P Q, Par A B C D -> Col A B P -> ~ Col A B Q -> exists Y, Col P Q Y /\ Col C D Y.

(** Transitivity of parallelism. *)

Definition postulate_of_transitivity_of_parallelism :=
 forall A1 A2 B1 B2 C1 C2,
 Par A1 A2 B1 B2 -> Par B1 B2 C1 C2 -> Par A1 A2 C1 C2.

Definition perpendicular_transversal_postulate :=
 forall A B C D P Q,
 Par A B C D -> Perp A B P Q -> Perp C D P Q.

Definition postulate_of_parallelism_of_perpendicular_tranversals :=
 forall A1 A2 B1 B2 C1 C2 D1 D2,
 Par A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 -> Par C1 C2 D1 D2.

Definition triangle_circumscription_principle :=
  forall A B C,
  ~ Col A B C -> exists CC, Cong A CC B CC /\ Cong A CC C CC.

Definition BetS (A B C : Tpoint) : Prop := Bet A B C /\ A <> B /\ B <> C.

Lemma BetSEq : forall A B C, BetS A B C <-> Bet A B C /\ A <> B /\ A <> C /\ B <> C.
Proof.
intros; unfold BetS; split; intro; spliter;
repeat split; Col; intro; treat_equalities; Col.
Qed.

Definition SPP :=
  forall P Q R S T U,
  BetS P T Q -> BetS R T S -> ~ Col P R U ->
  Coplanar P Q R U ->
  Cong P T Q T -> Cong R T S T ->
  exists I, Col S Q I /\ Col P U I.

Definition strong_parallel_postulate :=
  forall P Q R S T U,
  BetS P T Q -> BetS R T S -> ~ Col P R U ->
  Cong P T Q T -> Cong R T S T ->
  exists I, Col S Q I /\ Col P U I.

Definition euclid_5 :=
  forall P Q R S T U,
  BetS P T Q -> BetS R T S -> BetS Q U R -> ~ Col P Q S ->
  Cong P T Q T -> Cong R T S T ->
  exists I, BetS S Q I /\ BetS P U I.

(** This is the converse of triangle_mid_par. *)

Definition midpoints_converse_postulate :=
  forall A B C P Q,
 ~Col A B C ->
 is_midpoint P B C ->
 Par A B Q P ->
 Col A C Q ->
 is_midpoint Q A C.

(** This is the converse of l12_21_b. *)

Definition alternate_interior_angles_postulate :=
  forall A B C D, two_sides A C B D -> Par A B C D -> Conga B A C D C A.

Definition triangle_postulate := forall A B C D E F, Trisuma A B C D E F -> Bet D E F.

Definition playfair_bis := forall A1 A2 B1 B2 C1 C2 P,
  Perp2 A1 A2 B1 B2 P -> Col P B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2.

Definition original_euclid :=
  forall A B C D P Q R,
  one_side B C A D ->
  Isi A B C B C D ->
  Suma A B C B C D P Q R ->
  ~ Bet P Q R ->
  exists Y, out B A Y /\ out C D Y.

Definition original_spp :=
  forall A B C D P Q R,
  one_side B C A D ->
  Suma A B C B C D P Q R ->
  ~ Bet P Q R ->
  exists Y, Col B A Y /\ Col C D Y.

Definition inverse_projection_postulate :=
  forall A B C P Q,
  acute A B C ->
  out B A P ->
  P <> Q -> Per B P Q ->
  exists Y, out B C Y /\ Col P Q Y.

Definition proclus_bis :=
  forall A B C D P Q,
  Perp2 A B C D P ->
  Col A B P ->
  ~ Col A B Q ->
  exists Y, Col P Q Y /\ Col C D Y.

Definition consecutive_interior_angles_postulate :=
  forall A B C D P Q R,
  one_side B C A D ->
  Par A B C D ->
  Suma A B C B C D P Q R ->
  Bet P Q R.

End Euclid_def.