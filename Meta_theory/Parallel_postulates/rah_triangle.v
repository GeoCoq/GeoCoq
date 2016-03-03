Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section rah_triangle.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma rah__triangle : saccheri_s_right_angle_hypothesis -> triangle_postulate.
Proof.
  intros rah A B C D E F.
  apply (t22_14__bet rah).
Qed.

End rah_triangle.
