Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section par_perp_perp_par_perp_2_par.

Context `{T2D:Tarski_2D}.

Lemma par_perp_perp_implies_par_perp_2_par :
  perpendicular_transversal_postulate ->
  postulate_of_parallelism_of_perpendicular_transversals.
Proof.
intros HPPP A1; intros.
apply l12_9 with A1 A2; Perp.
apply perp_sym.
apply HPPP with B1 B2; Par; Perp.
Qed.

End par_perp_perp_par_perp_2_par.