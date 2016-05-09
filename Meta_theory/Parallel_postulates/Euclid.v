Require Export GeoCoq.Meta_theory.Parallel_postulates.SPP_ID.
Require Export GeoCoq.Meta_theory.Parallel_postulates.SPP_tarski.
Require Export GeoCoq.Meta_theory.Parallel_postulates.TCP_tarski.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_consecutive_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_playfair_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.aristotle_greenberg.
Require Export GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_existential_inverse_projection_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.consecutive_interior_angles_alternate_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_5_original_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_inverse_projection_postulate_legendre_s_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_playfair_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_saccheri_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_triangle_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.inverse_projection_postulate_proclus_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.midpoint_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.original_euclid_original_spp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.original_spp_inverse_projection_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_2_par_par_perp_perp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_TCP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_par_perp_2_par.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_trans_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_alternate_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_bis_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_existential_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_midpoint.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_par_trans.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_proclus_second_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.posidonius_postulate_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_SPP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_aristotle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_bis_proclus.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_second_postulate_par_perp_perp.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_existential_saccheri.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_rectangle_principle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_similar.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_thales_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_posidonius_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rectangle_existence_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rectangle_principle_rectangle_existence.
Require Export GeoCoq.Meta_theory.Parallel_postulates.similar_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_thales_existence.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_weak_triangle_circumscription_principle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_existence_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.thales_postulate_thales_converse_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_existential_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_playfair_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.

Require Import GeoCoq.Utils.all_equiv.

Require Import Rtauto.

Section Euclid.

Context `{T2D:Tarski_2D}.

Lemma strong_parallel_postulate_SPP : strong_parallel_postulate <-> SPP.
Proof.
unfold strong_parallel_postulate; unfold SPP.
split; intros; try apply H with R T; auto; apply all_coplanar.
Qed.

Theorem equivalent_parallel_postulates_without_decidability_of_intersection_of_lines :
  all_equiv
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     consecutive_interior_angles_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_second_postulate::
     nil).
Proof.
assert (K:=alternate_interior__consecutive_interior).
assert (L:=alternate_interior__playfair_bis).
assert (M:=consecutive_interior__alternate_interior).
assert (N:=midpoint_converse_postulate_implies_playfair).
assert (O:=par_perp_perp_implies_par_perp_2_par).
assert (P:=par_perp_perp_implies_playfair).
assert (Q:=par_perp_2_par_implies_par_perp_perp).
assert (R:=par_trans_implies_playfair).
assert (S:=playfair_bis__playfair).
assert (T:=playfair_implies_par_trans).
assert (U:=playfair_s_postulate_implies_midpoint_converse_postulate).
assert (V:=playfair__alternate_interior).
assert (W:=playfair__proclus_second_postulate).
assert (X:=proclus_second_postulate__perpendicular_transversal_postulate).
apply all_equiv_equiv; unfold all_equiv'; simpl; repeat (split; tauto).
Qed.

Theorem equivalent_parallel_postulates_without_any_continuity :
  all_equiv
    (existential_thales_postulate::
     posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrialteral::
     postulate_of_existence_of_a_right_saccheri_quadrialteral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_2_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     thales_postulate::
     thales_converse_postulate::
     triangle_postulate::
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
assert (P:=rah__posidonius).
assert (Q:=rectangle_existence__rah).
assert (R:=rectangle_principle__rectangle_existence).
assert (S:=similar__rah).
assert (T:=thales_converse_postulate__thales_existence).
assert (U:=thales_existence__rah).
assert (V:=thales_postulate__thales_converse_postulate).
assert (W:=triangle__existential_triangle).
apply all_equiv_equiv; unfold all_equiv'; simpl; repeat (split; tauto).
Qed.

Theorem equivalent_parallel_postulates_with_decidability_of_intersection_of_lines :
  decidability_of_intersection ->
  all_equiv
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     alternative_proclus_postulate::
     alternative_strong_parallel_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     inverse_projection_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_postulate::
     proclus_second_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil).
Proof.
intro HID.
assert (L:=euclid_5__original_euclid).
assert (M:=inter_dec_plus_par_perp_perp_imply_triangle_circumscription HID); clear HID.
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
assert (Y:=equivalent_parallel_postulates_without_decidability_of_intersection_of_lines).
apply all_equiv_equiv; unfold all_equiv, all_equiv' in *; simpl in *.
repeat (split; try rtauto; try (intro Z;
        assert (HP:playfair_s_postulate)
          by (try rtauto; let A := type of Z in (apply -> (Y A); try assumption; tauto));
        assert (J:perpendicular_transversal_postulate)
          by (let A := type of HP in (apply -> (Y A); try assumption; tauto));
        try rtauto; let A := type of HP in (apply -> (Y A); try assumption; tauto))).
Qed.

(* Is decidability_of_intersection_in_a_plane enough? *)
(* Every postulate which states the existence of a point is equivalent *)
Theorem equivalent_parallel_postulates_without_decidability_of_intersection_of_lines_bis :
  all_equiv
    (alternative_strong_parallel_postulate::
     alternative_proclus_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     inverse_projection_postulate::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil).
Proof.
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
assert (HPP:=equivalent_parallel_postulates_with_decidability_of_intersection_of_lines).
apply all_equiv_equiv; unfold all_equiv, all_equiv' in *; simpl in *.
repeat (split; try (try rtauto; split; intro W;
                    assert (HID:decidability_of_intersection) by rtauto;
                    let HTW := type of W in (apply -> (HPP HID HTW); try tauto; rtauto))).
Qed.

Theorem stronger_parallel_postulates :
  stronger
    (alternative_strong_parallel_postulate::
     alternative_proclus_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     inverse_projection_postulate::
     proclus_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     triangle_circumscription_principle::
     nil)

    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     consecutive_interior_angles_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_second_postulate::
     nil).
Proof.
assert(H:=equivalent_parallel_postulates_without_decidability_of_intersection_of_lines_bis).
assert(I:=strong_parallel_postulate_SPP).
assert(J:=strong_parallel_postulate_implies_inter_dec).
assert(K:=equivalent_parallel_postulates_with_decidability_of_intersection_of_lines); unfold all_equiv in *.
unfold stronger; simpl in *; intros x y Hx Hy;
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy;
subst; try tauto; intro L;
let HTL := type of L in
((assert (M:HTL->strong_parallel_postulate) by (apply H; tauto));
assert (N:decidability_of_intersection) by rtauto; apply -> (K N HTL); try tauto; rtauto).
Qed.

Theorem stronger_parallel_postulates_bis :
  stronger
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     consecutive_interior_angles_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_second_postulate::
     nil)

    (existential_thales_postulate::
     posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrialteral::
     postulate_of_existence_of_a_right_saccheri_quadrialteral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_2_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     thales_postulate::
     thales_converse_postulate::
     triangle_postulate::
     nil).
Proof.
assert(H:=equivalent_parallel_postulates_without_decidability_of_intersection_of_lines).
assert(I:=equivalent_parallel_postulates_without_any_continuity).
assert(J:=alternate_interior__triangle).
unfold all_equiv in *.
unfold stronger; simpl in *; intros x y Hx Hy;
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy;
subst; try tauto; intro L;
let HTL := type of L in
((assert (M:HTL->alternate_interior_angles_postulate) by (apply H; tauto));
try solve[apply -> (H HTL); tauto]; assert (N:triangle_postulate) by rtauto;
let HTN := type of N in (apply -> (I HTN); try tauto; rtauto)).
Qed.

Theorem equivalence_of_aristotle_greenberg_and_decidability_of_intersection :
  all_equiv_under
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     alternative_proclus_postulate::
     alternative_strong_parallel_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     inverse_projection_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_transitivity_of_parallelism::
     proclus_postulate::
     proclus_second_postulate::
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
    assert(playfair_s_postulate<->proclus_postulate); [|rtauto].
    assert(J:=equivalent_parallel_postulates_with_decidability_of_intersection_of_lines).
    unfold all_equiv in J; apply J; simpl; try tauto; rtauto.
    }
  assert(J:greenberg_s_postulate->decidability_of_intersection).
    {
    assert(J:alternate_interior_angles_postulate).
      {
      assert(playfair_s_postulate<->alternate_interior_angles_postulate); [|rtauto].
      assert (K:=equivalent_parallel_postulates_without_decidability_of_intersection_of_lines).
      unfold all_equiv in K; apply K; simpl; tauto.
      }
    assert(K:=alternate_interior__proclus).
    assert(L:proclus_postulate->decidability_of_intersection); [|rtauto].
    assert(L:proclus_postulate<->strong_parallel_postulate).
      {
      assert(L:=equivalent_parallel_postulates_without_decidability_of_intersection_of_lines_bis).
      unfold all_equiv in L; apply L; simpl; tauto.
      }
    assert (M:=strong_parallel_postulate_implies_inter_dec).
    assert (N:=strong_parallel_postulate_SPP); intro; rtauto.
    }
  simpl in *; decompose [or] HIny; clear HIny; decompose [or] HInz; clear HInz;
  subst; tauto. (* We could create a lemma to make this line quicker... *)
  }

  {
  assert (H:=stronger_parallel_postulates).
  assert(I:=equivalent_parallel_postulates_without_decidability_of_intersection_of_lines).
  unfold stronger, all_equiv in *; simpl in H; simpl in I; simpl in HInx;
  decompose [or] HInx; clear HInx; subst; try rtauto;
  let A := type of Hx in (try (apply (H A); try tauto; rtauto); try (apply -> (I A); try tauto; rtauto)).
  }
Qed.

Theorem equivalent_parallel_postulates_assuming_greenberg_s_postulate :
  greenberg_s_postulate ->
  all_equiv
    (alternate_interior_angles_postulate::
     alternative_playfair_s_postulate::
     alternative_proclus_postulate::
     alternative_strong_parallel_postulate::
     consecutive_interior_angles_postulate::
     euclid_5::
     euclid_s_parallel_postulate::
     existential_playfair_s_postulate::
     existential_thales_postulate::
     inverse_projection_postulate::
     midpoint_converse_postulate::
     perpendicular_transversal_postulate::
     playfair_s_postulate::
     posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrialteral::
     postulate_of_existence_of_a_right_saccheri_quadrialteral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_2_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_parallelism_of_perpendicular_transversals::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     postulate_of_transitivity_of_parallelism::
     proclus_postulate::
     proclus_second_postulate::
     strong_parallel_postulate::
     tarski_s_parallel_postulate::
     thales_postulate::
     thales_converse_postulate::
     triangle_circumscription_principle::
     triangle_postulate::
     nil).
Proof.
assert(HADG:=equivalence_of_aristotle_greenberg_and_decidability_of_intersection).
assert(HPP:=equivalent_parallel_postulates_with_decidability_of_intersection_of_lines).
assert(HPPWC:=equivalent_parallel_postulates_without_any_continuity).
assert(H:=alternate_interior__triangle).
intro HG; assert(I:=triangle_playfair_bis HG).
assert(J:=existential_playfair__rah).
assert(K:=playfair__existential_playfair).
apply all_equiv_equiv; unfold all_equiv, all_equiv' in *; simpl in *.
repeat (split; try (try rtauto; split; intro L; try apply K; try apply J in L;
                    let HTL := type of L in
                    (let G := type of HG in
                     (try (assert (HID:decidability_of_intersection)
                             by (apply -> (HADG HTL G); simpl; try tauto; rtauto);
                           try (apply -> (HPP HID HTL); try tauto; rtauto);
                           assert (HAIA:alternate_interior_angles_postulate)
                             by (apply -> (HPP HID HTL); try tauto; rtauto);
                           assert (HT:triangle_postulate) by rtauto);
                           try (let T := type of HT in (apply -> (HPPWC T); try tauto; rtauto)));
                      assert (HT:triangle_postulate)
                        by (apply -> (HPPWC HTL); try tauto; rtauto);
                      assert (HP:alternative_playfair_s_postulate) by rtauto); let P := type of HP in
                      assert (HID:decidability_of_intersection)
                             by (let G := type of HG in
                                 apply -> (HADG P G); simpl; try tauto; rtauto);
                      try solve [let P := type of HP in
                                 apply -> (HPP HID P); try tauto; rtauto];
                      apply -> (HPPWC HTL); try tauto; rtauto)).
Qed.

Theorem equivalent_parallel_postulates_without_any_continuity_bis :
  all_equiv
    (bachmann_s_lotschnittaxiom::
     weak_triangle_circumscription_principle::
     nil).
Proof.
assert(H:=bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle).
assert(I:=weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom).
apply all_equiv_equiv; unfold all_equiv, all_equiv' in *; simpl in *; tauto.
Qed.

Theorem stronger_parallel_postulates_ter :
  stronger
    (existential_thales_postulate::
     posidonius_postulate::
     postulate_of_existence_of_a_right_lambert_quadrialteral::
     postulate_of_existence_of_a_right_saccheri_quadrialteral::
     postulate_of_existence_of_a_triangle_whose_angles_sum_to_2_rights::
     postulate_of_existence_of_similar_triangles::
     postulate_of_right_lambert_quadrilaterals::
     postulate_of_right_saccheri_quadrilaterals::
     thales_postulate::
     thales_converse_postulate::
     triangle_postulate::
     nil)
    (bachmann_s_lotschnittaxiom::
     existential_inverse_projection_postulate::
     legendre_s_postulate::
     weak_triangle_circumscription_principle::
     nil).
Proof.
assert(HPPWC:=equivalent_parallel_postulates_without_any_continuity).
assert(H:=bachmann_s_lotschnittaxiom__existential_inverse_projection_postulate).
assert(I:=existential_inverse_projection_postulate__legendre_s_postulate).
assert(J:=thales_converse_postulate__weak_triangle_circumscription_principle).
assert(K:=weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom).
unfold all_equiv, all_equiv' in *; simpl in *.
unfold stronger; simpl in *; intros x y Hx Hy;
decompose [or] Hx; clear Hx; decompose [or] Hy; clear Hy;
subst; try rtauto; intro L;
let HTL := type of L in assert (HTCP:thales_converse_postulate)
                          by (apply -> (HPPWC HTL); try tauto; rtauto); rtauto.
Qed.

End Euclid.