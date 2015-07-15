Require Export Euclid_1.
Require Export Euclid_2.
Require Import List.

Section Euclid.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Definition all_equiv (l: list Prop) :=
  forall x y, In x l -> In y l -> (x<->y).

(** To state the final result we need to choose an arbitrary reference. *)

Theorem parallel_postulates_without_decidability_of_intersection_of_lines: 
 all_equiv  (playfair_s_postulate::
             perpendicular_transversal_postulate::
             postulate_of_parallelism_of_perpendicular_tranversals::
             postulate_of_transitivity_of_parallelism::
             midpoints_converse_postulate::nil).
Proof.
intros.
unfold all_equiv.
simpl.
intros.
assert (K:=playfair_implies_par_trans).
assert (L:=par_trans_implies_playfair).
assert (M:=playfair_s_postulate_implies_midpoints_converse_postulate).
assert (N:=midpoints_converse_postulate_implies_playfair).
assert (Q:=par_perp_perp_implies_par_perp_2_par).
assert (R:=par_perp_2_par_implies_par_perp_perp).
assert (S:=playfair_implies_par_perp_perp).
assert (T:=par_perp_perp_implies_playfair).
decompose [or] H;clear H;decompose [or] H0;clear H0;subst;
tauto. (* We could create a lemma to make this line quicker... *)
Qed.

Theorem parallel_postulates: 
 decidability_of_intersection ->
 all_equiv  (tarski_s_parallel_postulate::
             triangle_circumscription_principle::
             playfair_s_postulate::
             perpendicular_transversal_postulate::
             postulate_of_parallelism_of_perpendicular_tranversals::
             proclus_postulate::
             postulate_of_transitivity_of_parallelism::
             strong_parallel_postulate::
             euclid_5::
             midpoints_converse_postulate::nil).
Proof.
intros.
unfold all_equiv.
simpl.
intros.
assert (J:=strong_parallel_postulate_SPP).
assert (K:=playfair_implies_par_trans).
assert (L:=par_trans_implies_playfair).
assert (M:=playfair_s_postulate_implies_midpoints_converse_postulate).
assert (N:=midpoints_converse_postulate_implies_playfair).
assert (O:=inter_dec_plus_par_trans_imply_proclus).
assert (P:=proclus_s_postulate_implies_strong_parallel_postulate).
assert (Q:=par_perp_perp_implies_par_perp_2_par).
assert (R:=par_perp_2_par_implies_par_perp_perp).
assert (S:=playfair_implies_par_perp_perp).
assert (T:=par_perp_perp_implies_playfair).
assert (U:=tarski_s_euclid_implies_euclid_5).
assert (V:=euclid_5_implies_strong_parallel_postulate).
assert (W:=strong_parallel_postulate_implies_tarski_s_euclid).
assert (X:=inter_dec_plus_par_perp_perp_imply_triangle_circumscription).
assert (Y:=triangle_circumscription_implies_tarski_s_euclid).
assert (Z:=tarski_s_euclid_implies_playfair).
decompose [or] H0;clear H0;decompose [or] H1;clear H1;subst;
tauto. (* We could create a lemma to make this line quicker... *)
Qed.

(* Is decidability_of_intersection_in_a_plane enough? *)
(* Every postulate which states the existence of a point is equivalent *)

Theorem result_similar_to_beeson_s_one :
   all_equiv 
  (euclid_5::
   strong_parallel_postulate::
   triangle_circumscription_principle::
   proclus_postulate::
   tarski_s_parallel_postulate::nil).
Proof.
assert (O:=strong_parallel_postulate_SPP).
assert (P:=strong_parallel_postulate_implies_tarski_s_euclid).
assert (Q:=tarski_s_euclid_implies_euclid_5).
assert (R:=euclid_5_implies_strong_parallel_postulate).
assert (S:=proclus_s_postulate_implies_strong_parallel_postulate).
assert (T:=triangle_circumscription_implies_tarski_s_euclid).
assert (U:=strong_parallel_postulate_implies_inter_dec).
assert (V:=parallel_postulates).
unfold all_equiv in V.
simpl in V; unfold all_equiv; simpl; intros;
decompose [or] H; clear H; decompose [or] H0; clear H0; subst; try tauto; split; intro;
assert decidability_of_intersection by tauto; let A := type of H in (apply -> (V H0 A); tauto).
Qed.

End Euclid.