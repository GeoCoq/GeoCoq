Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section existential_saccheri_rah.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma existential_saccheri__rah : existential_saccheri -> saccheri_s_right_angle_hypothesis.
Proof.
  intro HABCD.
  destruct HABCD as [A [B [C [D [HSac HPer]]]]].
  apply (per_sac__rah A B C D HSac HPer).
Qed.

End existential_saccheri_rah.
