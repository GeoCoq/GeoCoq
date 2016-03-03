Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section rah_thales_postulate.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma rah__thales_postulate : saccheri_s_right_angle_hypothesis -> thales_postulate.
Proof.
  intros rah A B C M HNCol HM HCong.
  apply (t22_17__rah _ _ _ M); assumption.
Qed.

End rah_thales_postulate.
