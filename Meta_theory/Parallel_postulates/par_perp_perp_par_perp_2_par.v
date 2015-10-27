Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section par_perp_perp_par_perp_2_par.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma par_perp_perp_implies_par_perp_2_par :
  perpendicular_transversal_postulate ->
  postulate_of_parallelism_of_perpendicular_tranversals.
Proof.
intros HPPP A1; intros.
apply l12_9 with A1 A2; try apply all_coplanar; Perp.
apply perp_sym.
apply HPPP with B1 B2; Par; Perp.
Qed.

End par_perp_perp_par_perp_2_par.