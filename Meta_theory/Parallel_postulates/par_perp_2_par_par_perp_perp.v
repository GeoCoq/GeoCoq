Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section par_perp_2_par_par_perp_perp.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma par_perp_2_par_implies_par_perp_perp :
  postulate_of_parallelism_of_perpendicular_transversals ->
  perpendicular_transversal_postulate.
Proof.
intros HPPP A B C D P Q HPar HPerp.
assert (HX := HPerp); destruct HX as [X HX].
elim (Col_dec C D X); intro HCDX.

  elim HPar; clear HPar; intro HPar.

    exfalso; apply HPar; exists X; unfold Perp_at in HX; spliter; Col.

    apply perp_sym; apply perp_col2_bis with A B; spliter; Col; Perp.

  assert (HY := l8_18_existence C D X HCDX); destruct HY as [Y [HCDY HPerp']].
  assert (HPar' : Par P Q X Y) by (apply HPPP with A B C D; assumption).
  elim HPar'; clear HPar'; intro HPar'.

    exfalso; apply HPar'; exists X; unfold Perp_at in HX; spliter; Col.

    destruct HPar' as [HPQ [HXY [HCol1 HCol2]]].
    apply perp_sym; apply perp_col2 with X Y; Col; Perp.
Qed.

End par_perp_2_par_par_perp_perp.
