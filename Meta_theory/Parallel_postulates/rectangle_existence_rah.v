Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section rectangle_existence_rah.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma rectangle_existence__rah : rectangle_existence -> saccheri_s_right_angle_hypothesis.
Proof.
  intros HABCD.
  destruct HABCD as [A [B [C [D []]]]].
  apply (lam_per__rah A B C D); assumption.
Qed.

End rectangle_existence_rah.
