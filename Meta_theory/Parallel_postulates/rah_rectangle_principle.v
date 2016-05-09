Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section rah_rectangle_principle.

Context `{T2D:Tarski_2D}.

Lemma rah__rectangle_principle : postulate_of_right_saccheri_quadrilaterals -> postulate_of_right_lambert_quadrilaterals.
Proof.
  intros rah A B C D HLam.
  apply (lam_per__rah A); assumption.
Qed.

End rah_rectangle_principle.
