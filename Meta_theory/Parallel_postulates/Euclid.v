Require Export GeoCoq.Meta_theory.Parallel_postulates.SPP_ID.
Require Export GeoCoq.Meta_theory.Parallel_postulates.SPP_tarski.
Require Export GeoCoq.Meta_theory.Parallel_postulates.TCP_tarski.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_consecutive_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_playfair_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.aristotle_greenberg.
Require Export GeoCoq.Meta_theory.Parallel_postulates.consecutive_interior_angles_alternate_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_SPP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_5_original_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.inverse_projection_proclus_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.midpoints_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.original_euclid_original_spp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.original_spp_inverse_projection.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_2_par_par_perp_perp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_TCP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_par_perp_2_par.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_trans_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_trans_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_alternate_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_bis_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_par_trans_par_perp_perp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_SPP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_aristotle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_bis_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_midpoints.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_playfair_bis.

Require Import GeoCoq.Utils.all_equiv.

Section Euclid.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma strong_parallel_postulate_SPP : strong_parallel_postulate <-> SPP.
Proof.
unfold strong_parallel_postulate; unfold SPP.
split; intros; try apply H with R T; auto; apply all_coplanar.
Qed.

(** To state the final result we need to choose an arbitrary reference. *)

Theorem parallel_postulates_without_decidability_of_intersection_of_lines :
 all_equiv  (playfair_s_postulate::
             perpendicular_transversal_postulate::
             postulate_of_parallelism_of_perpendicular_tranversals::
             postulate_of_transitivity_of_parallelism::
             midpoints_converse_postulate::
             alternate_interior_angles_postulate::
             playfair_bis::
             consecutive_interior_angles_postulate::
             nil).
Proof.
intros.
unfold all_equiv; simpl; intros x y Hx Hy.
assert (K:=playfair_implies_par_trans).
assert (L:=par_trans_implies_playfair).
assert (M:=playfair_s_postulate_implies_midpoints_converse_postulate).
assert (N:=midpoints_converse_postulate_implies_playfair).
assert (Q:=par_perp_perp_implies_par_perp_2_par).
assert (R:=par_perp_2_par_implies_par_perp_perp).
assert (S:=playfair_implies_par_perp_perp).
assert (T:=par_perp_perp_implies_playfair).
assert (U:=playfair_bis__playfair).
assert (V:=alternate_interior__playfair_bis).
assert (W:=playfair__alternate_interior).
assert (X:=consecutive_interior__alternate_interior).
assert (Y:=alternate_interior__consecutive_interior).
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy; subst;
tauto. (* We could create a lemma to make this line quicker... *)
Qed.

Theorem parallel_postulates :
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
             midpoints_converse_postulate::
             alternate_interior_angles_postulate::
             playfair_bis::
             consecutive_interior_angles_postulate::
             original_euclid::
             original_spp::
             inverse_projection_postulate::
             proclus_bis::
             nil).
Proof.
intro HID; unfold all_equiv; simpl; intros x y Hx Hy.
assert (AA:=euclid_5__original_euclid).
assert (A:=inverse_projection__proclus_bis).
assert (B:=original_euclid__original_spp).
assert (C:=original_spp__inverse_projection).
assert (D:=proclus_bis__proclus).
assert (E:=consecutive_interior__alternate_interior).
assert (F:=alternate_interior__consecutive_interior).
assert (G:=playfair_bis__playfair).
assert (H:=alternate_interior__playfair_bis).
assert (I:=playfair__alternate_interior).
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
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy; subst;
tauto. (* We could create a lemma to make this line quicker... *)
Qed.

(* Is decidability_of_intersection_in_a_plane enough? *)
(* Every postulate which states the existence of a point is equivalent *)

Theorem result_similar_to_beeson_s_one :
  all_equiv (euclid_5::
             strong_parallel_postulate::
             triangle_circumscription_principle::
             proclus_postulate::
             tarski_s_parallel_postulate::
             original_euclid::
             original_spp::
             inverse_projection_postulate::
             proclus_bis::
             nil).
Proof.
assert (J:=euclid_5__original_euclid).
assert (K:=inverse_projection__proclus_bis).
assert (L:=original_euclid__original_spp).
assert (M:=original_spp__inverse_projection).
assert (N:=proclus_bis__proclus).
assert (O:=strong_parallel_postulate_SPP).
assert (P:=strong_parallel_postulate_implies_tarski_s_euclid).
assert (Q:=tarski_s_euclid_implies_euclid_5).
assert (R:=euclid_5_implies_strong_parallel_postulate).
assert (S:=proclus_s_postulate_implies_strong_parallel_postulate).
assert (T:=triangle_circumscription_implies_tarski_s_euclid).
assert (U:=strong_parallel_postulate_implies_inter_dec).
assert (V:=parallel_postulates).
unfold all_equiv in V.
simpl in V; unfold all_equiv; simpl; intros x y Hx Hy;
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy;
subst; try tauto; split; intro W;
assert (X:decidability_of_intersection) by tauto;
let A := type of W in (apply -> (V X A); tauto).
Qed.

Theorem stronger_parallel_postulates :
  stronger (euclid_5::
            strong_parallel_postulate::
            triangle_circumscription_principle::
            proclus_postulate::
            tarski_s_parallel_postulate::
            original_euclid::
            original_spp::
            inverse_projection_postulate::
            proclus_bis::
            nil)
           (playfair_s_postulate::
            perpendicular_transversal_postulate::
            postulate_of_parallelism_of_perpendicular_tranversals::
            postulate_of_transitivity_of_parallelism::
            midpoints_converse_postulate::
            alternate_interior_angles_postulate::
            playfair_bis::
            consecutive_interior_angles_postulate::
            nil).
Proof.
assert(H:=result_similar_to_beeson_s_one).
assert(I:=strong_parallel_postulate_SPP).
assert(J:=strong_parallel_postulate_implies_inter_dec).
assert(K:=parallel_postulates); unfold all_equiv in *.
simpl in H; simpl in K; unfold stronger; simpl; intros x y Hx Hy;
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy;
subst; try tauto; intro L;
let A := type of L in (assert (M:A->strong_parallel_postulate) by (apply H; tauto));
assert (N:decidability_of_intersection) by tauto;
let A := type of L in (apply -> (K N A); tauto).
Qed.

Theorem equivalence_of_aristotle_greenberg_and_decidability_of_intersection :
  all_equiv_under (tarski_s_parallel_postulate::
                   triangle_circumscription_principle::
                   playfair_s_postulate::
                   perpendicular_transversal_postulate::
                   postulate_of_parallelism_of_perpendicular_tranversals::
                   proclus_postulate::
                   postulate_of_transitivity_of_parallelism::
                   strong_parallel_postulate::
                   euclid_5::
                   midpoints_converse_postulate::
                   alternate_interior_angles_postulate::
                   playfair_bis::
                   consecutive_interior_angles_postulate::
                   original_euclid::
                   original_spp::
                   inverse_projection_postulate::
                   proclus_bis::
                   nil)
                  (aristotle_s_postulate::
                   decidability_of_intersection::
                   greenberg_s_postulate::
                   nil).
Proof.
intros x y z HInx HIny HInz Hx.
cut playfair_s_postulate;
[intro HP; clear Hx|clear HIny; clear y; clear HInz; clear z].
  {
  assert(H:=aristotle__greenberg).
  assert(I:decidability_of_intersection->aristotle_s_postulate).
    {
    intro I; apply proclus__aristotle.
    assert(playfair_s_postulate<->proclus_postulate); [|tauto].
    assert(J:=parallel_postulates).
    unfold all_equiv in J; apply J; simpl; tauto.
    }
  assert(J:greenberg_s_postulate->decidability_of_intersection).
    {
    assert(J:alternate_interior_angles_postulate).
      {
      assert(playfair_s_postulate<->alternate_interior_angles_postulate); [|tauto].
      assert (K:=parallel_postulates_without_decidability_of_intersection_of_lines).
      unfold all_equiv in K; apply K; simpl; tauto.
      }
    assert(K:=alternate_interior__proclus).
    assert(L:proclus_postulate->decidability_of_intersection); [|tauto].
    assert(L:proclus_postulate<->strong_parallel_postulate).
      {
      assert(L:=result_similar_to_beeson_s_one).
      unfold all_equiv in L; apply L; simpl; tauto.
      }
    assert (M:=strong_parallel_postulate_implies_inter_dec).
    assert (N:=strong_parallel_postulate_SPP); intro; tauto.
    }
  simpl in *; decompose [or] HIny; clear HIny; decompose [or] HInz; clear HInz;
  subst; tauto. (* We could create a lemma to make this line quicker... *)
  }

  {
  assert (H:=stronger_parallel_postulates).
  assert(I:=parallel_postulates_without_decidability_of_intersection_of_lines).
  unfold stronger, all_equiv in *; simpl in H; simpl in I; simpl in HInx;
  decompose [or] HInx; clear HInx; subst; try tauto;
  let A := type of Hx in (try (apply (H A); tauto); try (apply -> (I A); tauto)).
  }
Qed.

Theorem parallel_postulates_assuming_greenberg_s_postulate :
 greenberg_s_postulate ->
 all_equiv  (tarski_s_parallel_postulate::
             triangle_circumscription_principle::
             playfair_s_postulate::
             perpendicular_transversal_postulate::
             postulate_of_parallelism_of_perpendicular_tranversals::
             proclus_postulate::
             postulate_of_transitivity_of_parallelism::
             strong_parallel_postulate::
             euclid_5::
             midpoints_converse_postulate::
             alternate_interior_angles_postulate::
             playfair_bis::
             triangle_postulate::
             consecutive_interior_angles_postulate::
             original_euclid::
             original_spp::
             inverse_projection_postulate::
             proclus_bis::
             nil).
Proof.
intros HG; assert(H:=parallel_postulates).
assert(I:=alternate_interior__triangle).
assert(J:=triangle_playfair_bis).
assert(K:=equivalence_of_aristotle_greenberg_and_decidability_of_intersection).
unfold all_equiv, all_equiv_under in *; simpl in *; intros x y Hx Hy.
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy; subst; try tauto; split;
intro L; let A := type of L in
         (let B := type of HG in
          (try (assert (M:decidability_of_intersection)
                 by (apply -> (K A B); tauto);
                try (apply -> (H M A); tauto);
                cut alternate_interior_angles_postulate; auto;
                apply -> (H M A); tauto));
          cut playfair_bis; auto; intro M;
          let C := type of M in
          (assert (N:decidability_of_intersection)
            by (apply -> (K C B); tauto); apply -> (H N C); tauto)).
Qed.

End Euclid.