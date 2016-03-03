Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section rah_rectangle_principle.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma rah__rectangle_principle : saccheri_s_right_angle_hypothesis -> rectangle_principle.
Proof.
  intros rah A B C D HLam.
  apply (lam_per__rah A); assumption.
Qed.

End rah_rectangle_principle.
