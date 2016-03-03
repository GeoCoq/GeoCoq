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
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_saccheri_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_triangle_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.inverse_projection_postulate_proclus_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.midpoints_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.original_euclid_original_spp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.original_spp_inverse_projection_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_2_par_par_perp_perp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_TCP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_par_perp_2_par.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_trans_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_trans_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_alternate_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_bis_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_par_trans_par_perp_perp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.posidonius_postulate_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_SPP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_aristotle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_bis_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_midpoints.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_existential_saccheri.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_rectangle_principle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_similar.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_thales_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_universal_posidonius.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rectangle_existence_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rectangle_principle_rectangle_existence.
Require Export GeoCoq.Meta_theory.Parallel_postulates.similar_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_thales_existence.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_existence_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_postulate_thales_converse_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_existential_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_playfair_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.universal_posidonius_posidonius_postulate.

Require Import GeoCoq.Utils.all_equiv.

Section Euclid.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma strong_parallel_postulate_SPP : strong_parallel_postulate <-> SPP.
Proof.
unfold strong_parallel_postulate; unfold SPP.
split; intros; try apply H with R T; auto; apply all_coplanar.
Qed.

Theorem parallel_postulates_without_decidability_of_intersection_of_lines :
  all_equiv
    (alternate_interior_angles_postulate::
     consecutive_interior_angles_postulate::
     midpoints_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_bis::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     nil).
Proof.
assert (K:=alternate_interior__consecutive_interior).
assert (L:=alternate_interior__playfair_bis).
assert (M:=consecutive_interior__alternate_interior).
assert (N:=midpoints_converse_postulate_implies_playfair).
assert (O:=par_perp_perp_implies_par_perp_2_par).
assert (P:=par_perp_perp_implies_playfair).
assert (Q:=par_perp_2_par_implies_par_perp_perp).
assert (R:=par_trans_implies_playfair).
assert (S:=playfair_bis__playfair).
assert (T:=playfair_implies_par_perp_perp).
assert (U:=playfair_implies_par_trans).
assert (V:=playfair_s_postulate_implies_midpoints_converse_postulate).
assert (W:=playfair__alternate_interior).
apply all_equiv_equiv; unfold all_equiv'; simpl; repeat (split; tauto).
Qed.

Theorem parallel_postulates_without_any_continuity :
  all_equiv
    (existential_saccheri::
     existential_triangle::
     posidonius_postulate::
     rectangle_existence::
     rectangle_principle::
     saccheri_s_right_angle_hypothesis::
     similar_triangles_existence::
     thales_postulate::
     thales_converse_postulate::
     thales_existence::
     triangle_postulate::
     universal_posidonius::
     nil).
intros.
assert (H:=existential_saccheri__rah).
assert (I:=existential_triangle__rah).
assert (J:=posidonius_postulate__rah).
assert (K:=rah__existential_saccheri).
assert (L:=rah__rectangle_principle).
assert (M:=rah__similar).
assert (N:=rah__thales_postulate).
assert (O:=rah__triangle).
assert (P:=rah__universal_posidonius).
assert (Q:=rectangle_existence__rah).
assert (R:=rectangle_principle__rectangle_existence).
assert (S:=similar__rah).
assert (T:=thales_converse_postulate__thales_existence).
assert (U:=thales_existence__rah).
assert (V:=thales_postulate__thales_converse_postulate).
assert (W:=universal_posidonius__posidonius_postulate).
assert (X:=triangle__existential_triangle).
apply all_equiv_equiv; unfold all_equiv'; simpl; repeat (split; tauto).
Qed.

Theorem parallel_postulates :
  decidability_of_intersection ->
  all_equiv
    (alternate_interior_angles_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     inverse_projection_postulate::
     midpoints_converse_postulate::
     original_euclid::
     original_spp::
     perpendicular_transversal_postulate::
     playfair_bis::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_bis::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil).
Proof.
intro HID.
assert (K:=euclid_5_implies_strong_parallel_postulate).
assert (L:=euclid_5__original_euclid).
assert (M:=inter_dec_plus_par_perp_perp_imply_triangle_circumscription HID).
assert (N:=inter_dec_plus_par_trans_imply_proclus HID); clear HID.
assert (O:=inverse_projection_postulate__proclus_bis).
assert (P:=original_euclid__original_spp).
assert (Q:=original_spp__inverse_projection_postulate).
assert (R:=proclus_bis__proclus).
assert (S:=proclus_s_postulate_implies_strong_parallel_postulate).
assert (T:=strong_parallel_postulate_implies_tarski_s_euclid).
assert (U:=strong_parallel_postulate_SPP).
assert (V:=tarski_s_euclid_implies_euclid_5).
assert (W:=tarski_s_euclid_implies_playfair).
assert (X:=triangle_circumscription_implies_tarski_s_euclid).
assert (Y:=parallel_postulates_without_decidability_of_intersection_of_lines).
apply all_equiv_equiv; unfold all_equiv, all_equiv' in *; simpl in *.
repeat (split; try (try tauto; split; intro Z;
        assert (HP:playfair_s_postulate)
          by (try tauto; let A := type of Z in (apply -> (Y A); tauto));
        assert (J:perpendicular_transversal_postulate)
          by (let A := type of HP in (apply -> (Y A); tauto));
        assert (I:postulate_of_transitivity_of_parallelism)
          by (let A := type of HP in (apply -> (Y A); tauto));
        try tauto; let A := type of HP in (apply -> (Y A); tauto))).
Qed.

(* Is decidability_of_intersection_in_a_plane enough? *)
(* Every postulate which states the existence of a point is equivalent *)
Theorem result_similar_to_beeson_s_one :
  all_equiv
    (euclid_5::
     inverse_projection_postulate::
     original_euclid::
     original_spp::
     proclus_bis::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil).
Proof.
assert (J:=euclid_5_implies_strong_parallel_postulate).
assert (K:=euclid_5__original_euclid).
assert (L:=inverse_projection_postulate__proclus_bis).
assert (M:=original_euclid__original_spp).
assert (N:=original_spp__inverse_projection_postulate).
assert (O:=proclus_bis__proclus).
assert (P:=proclus_s_postulate_implies_strong_parallel_postulate).
assert (Q:=strong_parallel_postulate_implies_inter_dec).
assert (R:=strong_parallel_postulate_implies_tarski_s_euclid).
assert (S:=strong_parallel_postulate_SPP).
assert (T:=tarski_s_euclid_implies_euclid_5).
assert (U:=triangle_circumscription_implies_tarski_s_euclid).
assert (HPP:=parallel_postulates).
apply all_equiv_equiv; unfold all_equiv, all_equiv' in *; simpl in *.
repeat (split; try (try tauto; split; intro W;
                    assert (HID:decidability_of_intersection) by tauto;
                    let HTW := type of W in (apply -> (HPP HID HTW); tauto))).
Qed.

Theorem stronger_parallel_postulates :
  stronger
    (euclid_5::
     inverse_projection_postulate::
     original_euclid::
     original_spp::
     proclus_bis::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil)

    (alternate_interior_angles_postulate::
     consecutive_interior_angles_postulate::
     midpoints_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_bis::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     nil).
Proof.
assert(H:=result_similar_to_beeson_s_one).
assert(I:=strong_parallel_postulate_SPP).
assert(J:=strong_parallel_postulate_implies_inter_dec).
assert(K:=parallel_postulates); unfold all_equiv in *.
unfold stronger; simpl in *; intros x y Hx Hy;
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy;
subst; try tauto; intro L;
let HTL := type of L in
((assert (M:HTL->strong_parallel_postulate) by (apply H; tauto));
assert (N:decidability_of_intersection) by tauto; apply -> (K N HTL); tauto).
Qed.

Theorem stronger_parallel_postulates_bis :
  stronger
    (alternate_interior_angles_postulate::
     consecutive_interior_angles_postulate::
     midpoints_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_bis::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     nil)

    (existential_saccheri::
     existential_triangle::
     posidonius_postulate::
     rectangle_existence::
     rectangle_principle::
     saccheri_s_right_angle_hypothesis::
     similar_triangles_existence::
     thales_postulate::
     thales_converse_postulate::
     thales_existence::
     triangle_postulate::
     universal_posidonius::
     nil).
Proof.
assert(H:=parallel_postulates_without_decidability_of_intersection_of_lines).
assert(I:=parallel_postulates_without_any_continuity).
assert(J:=alternate_interior__triangle).
unfold all_equiv in *.
unfold stronger; simpl in *; intros x y Hx Hy;
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy;
subst; try tauto; intro L;
let HTL := type of L in
((assert (M:HTL->alternate_interior_angles_postulate) by (apply H; tauto));
try solve[apply -> (H HTL); tauto]; assert (N:triangle_postulate) by tauto;
let HTN := type of N in (apply -> (I HTN); tauto)).
Qed.

Theorem equivalence_of_aristotle_greenberg_and_decidability_of_intersection :
  all_equiv_under
    (alternate_interior_angles_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     inverse_projection_postulate::
     midpoints_converse_postulate::
     original_euclid::
     original_spp::
     perpendicular_transversal_postulate::
     playfair_bis::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_bis::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
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
  all_equiv
    (alternate_interior_angles_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     existential_saccheri::
     existential_triangle::
     inverse_projection_postulate::
     midpoints_converse_postulate::
     original_euclid::
     original_spp::
     perpendicular_transversal_postulate::
     playfair_bis::
     playfair_s_postulate::
     posidonius_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_bis::
     proclus_postulate::
     rectangle_existence::
     rectangle_principle::
     saccheri_s_right_angle_hypothesis::
     similar_triangles_existence::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     thales_postulate::
     thales_converse_postulate::
     thales_existence::
     triangle_circumscription_principle::
     triangle_postulate::
     universal_posidonius::
     nil).
Proof.
assert(HADG:=equivalence_of_aristotle_greenberg_and_decidability_of_intersection).
assert(HPP:=parallel_postulates).
assert(HPPWC:=parallel_postulates_without_any_continuity).
assert(H:=alternate_interior__triangle).
intro HG; assert(I:=triangle_playfair_bis HG).
apply all_equiv_equiv; unfold all_equiv, all_equiv' in *; simpl in *.
repeat (split; try (try tauto; split; intro J;
                    let HTJ := type of J in
                    (let G := type of HG in
                     (try (assert (HID:decidability_of_intersection)
                             by (apply -> (HADG HTJ G); simpl; tauto);
                           try (apply -> (HPP HID HTJ); tauto);
                           assert (HAIA:alternate_interior_angles_postulate)
                             by (apply -> (HPP HID HTJ); tauto);
                           assert (HT:triangle_postulate) by tauto);
                           try (let T := type of HT in (apply -> (HPPWC T); tauto)));
                      assert (HT:triangle_postulate)
                        by (apply -> (HPPWC HTJ); tauto);
                      assert (HP:playfair_bis) by tauto); let P := type of HP in
                      assert (HID:decidability_of_intersection)
                             by (let G := type of HG in
                                 apply -> (HADG P G); simpl; tauto);
                      try solve [let P := type of HP in
                                 apply -> (HPP HID P); tauto];
                      apply -> (HPPWC HTJ); tauto)).
Qed.

End Euclid.
