Require Export perp_bisect.
Require Export quadrilaterals.
Require Export Coplanar_trans.

Section Euclid_def.

Context `{M:Tarski_neutral_dimensionless}.

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

Definition tarski_s_parallel_postulate :=
 forall A B C D T : Tpoint,
 Bet A D T -> Bet B D C -> A<>D ->
 exists x, exists y,
 Bet A B x /\ Bet A C y /\ Bet x T y.

(** This unicity of parallel postulate. *)

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
  coplanar P Q R U ->
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

Definition midpoints_converse_postulate :=
  forall A B C P Q,
 ~Col A B C ->
 is_midpoint P B C ->
 Par A B Q P ->
 Col A C Q ->
 is_midpoint Q A C.

End Euclid_def.
